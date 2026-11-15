#!/usr/bin/env python3
"""Recompute both frequency denominators and magnitudes from one set of actions.

No cached negative result is treated as evidence of absence: each record reports
numerical failures separately from RTBT moves that leave its mathematical domain.
Checkpoints are keyed by input, source, options, and dependency hashes.
"""
from __future__ import annotations
import argparse
import csv
import gzip
import hashlib
import json
import multiprocessing as mp
import platform
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import numpy as np
import scipy
from scipy.special import logsumexp

from scripts.coval.profiles import load_cases_tie_norm, parse_ranking, ranking_to_wins_and_ties, strictly_first_candidate
from scripts.theory.nlhf_tie_normalization import solve_nlhf_tie_norm, normalized_margin_matrix_tie_norm
from scripts.theory.search_nlhf_tie_normalization_examples import improvements, demotions, monotonicity_move_valid, strictly_last_candidate, load_rho_cache
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda, strongly_connected

REFS = {
    'nemo': 'results/reference_distributions/nemo_pytorch_rho_strip_identity_float32.jsonl',
    'qwen25': 'results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl',
    'qwen3': 'results/reference_distributions/qwen3_pytorch_rho_strip_identity.jsonl',
}
TAUS = [.0005, .001, .002, .005, .01, .02, .05, .1, .2, .5]
BETAS = [.005, .01, .02, .05, .1, .2, .5, 1., 2., 5.]
CASES = []
CACHES = {}


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def init_worker(dataset, limit):
    global CASES, CACHES
    CASES = sorted(load_cases_tie_norm(Path(dataset), ['world', 'personal']), key=lambda c: (c.prompt_id, c.block_name))
    if limit: CASES = CASES[:limit]
    CACHES = {name: load_rho_cache(Path(path)) for name, path in REFS.items()}


def profile_record(case, model, rule, param, temperature):
    labels = case.response_indices
    index = {label: i for i, label in enumerate(labels)}
    rho = np.array([CACHES[model][case.prompt_id]['rho'][label] for label in labels])
    assert np.all(rho > 0) and np.all(np.isfinite(rho))
    log_rho = np.log(rho) / temperature
    rho = np.exp(log_rho - logsumexp(log_rho))
    wins = np.asarray(case.total_wins)
    ties = np.asarray(case.total_ties)
    record = dict(case_key=f'{case.prompt_id}:{case.block_name}', model=model, rule=rule,
                  param=param, temperature=temperature, in_domain=True, failures=0, domain_exits=0,
                  mono_change=0., mono_effect=0., inv_change=0., inv_effect=0.,
                  mono_witness=None, inv_witness=None, solve_count=0)
    if rule == 'rtbt' and not strongly_connected(wins):
        record['in_domain'] = False
        return record
    solutions = {}
    def solve(w, t):
        if rule == 'rtbt' and not strongly_connected(w):
            record['domain_exits'] += 1
            return None
        key = (normalized_margin_matrix_tie_norm(w, t).tobytes() if rule == 'nlhf' else w.tobytes())
        if key not in solutions:
            p = (solve_nlhf_tie_norm(param, w, t, rho) if rule == 'nlhf'
                 else solve_weighted_logistic_borda(param, w, rho))
            solutions[key] = p
            record['solve_count'] += 1
            if p is None:
                record['failures'] += 1
            else:
                assert np.all(np.isfinite(p)) and np.all(p >= 0) and abs(p.sum()-1) < 1e-10
        return solutions[key]
    original = solve(wins, ties)
    if original is None: return record
    record['baseline_tv'] = float(np.abs(original-rho).sum()/2)
    seen = set()
    def update(kind, change, effect, detail):
        record[kind+'_change'] = max(record[kind+'_change'], abs(float(change)))
        if effect > record[kind+'_effect']:
            record[kind+'_effect'] = float(effect)
            record[kind+'_witness'] = detail
    for vi, ranking in enumerate(case.rankings):
        if ranking in seen: continue
        seen.add(ranking)
        old_w = np.asarray(case.wins_per_ranking[vi])
        old_t = np.asarray(case.ties_per_ranking[vi])
        top = strictly_first_candidate(ranking, labels)
        bottom = strictly_last_candidate(ranking, labels)
        if top is not None or bottom is not None:
            reduced = solve(wins-old_w, ties-old_t)
            if reduced is not None:
                for candidate, sign, axiom in [(top, 1, 'positive_involvement'), (bottom, -1, 'negative_involvement')]:
                    if candidate is None: continue
                    k = index[candidate]
                    effect = sign*float(reduced[k]-original[k])
                    update('inv', effect, effect, dict(axiom=axiom, voter_index=vi, ranking=ranking,
                           candidate=candidate, before=reduced.tolist(), after=original.tolist()))
        if rule != 'nlhf': continue
        blocks = parse_ranking(ranking)
        for candidate in labels:
            k = index[candidate]
            for direction, generator in [('up', improvements), ('down', demotions)]:
                for new_ranking in generator(blocks, candidate):
                    new_blocks = parse_ranking(new_ranking)
                    valid = (monotonicity_move_valid(blocks, new_blocks, candidate, labels) if direction=='up'
                             else monotonicity_move_valid(new_blocks, blocks, candidate, labels))
                    if not valid: raise AssertionError('generated inadmissible move')
                    new_w, new_t = ranking_to_wins_and_ties(new_ranking, index)
                    modified = solve(wins-old_w+new_w, ties-old_t+new_t)
                    if modified is None: continue
                    before, after = (original, modified) if direction=='up' else (modified, original)
                    effect = float(before[k]-after[k])
                    update('mono', effect, effect, dict(axiom='monotonicity', voter_index=vi,
                           old_ranking=ranking if direction=='up' else new_ranking,
                           new_ranking=new_ranking if direction=='up' else ranking,
                           observed_role='before' if direction=='up' else 'after', candidate=candidate,
                           before=before.tolist(), after=after.tolist()))
    return record


def task(args):
    model, rule, param, temperature, directory = args
    path = Path(directory)/f'{model}_{rule}_{param:g}_T{temperature:g}.jsonl.gz'
    if path.exists():
        with gzip.open(path, 'rt') as handle: records = [json.loads(s) for s in handle]
        return str(path), records
    records = [profile_record(c, model, rule, param, temperature) for c in CASES]
    temporary = path.with_suffix('.partial')
    with gzip.open(temporary, 'wt') as handle:
        for row in records: handle.write(json.dumps(row, sort_keys=True, allow_nan=False)+'\n')
    temporary.replace(path)
    return str(path), records


def summarize(records, threshold):
    first = records[0]
    rows = []
    for kind, axiom in ([('mono','monotonicity'), ('inv','involvement')] if first['rule']=='nlhf' else [('inv','involvement')]):
        valid = [r for r in records if r['in_domain']]
        eligible = [r for r in valid if r[kind+'_change'] >= threshold]
        witnessed = [r for r in valid if r[kind+'_effect'] >= threshold]
        assert all(r in eligible for r in witnessed)
        rows.append(dict(model=first['model'], rule=first['rule'], axiom=axiom, param=first['param'],
                         temperature=first['temperature'], threshold=threshold, profiles_total=len(valid),
                         profiles_eligible=len(eligible), profiles_with_witness=len(witnessed),
                         unconditioned_percent=100*len(witnessed)/len(valid) if valid else 0.,
                         conditioned_percent=100*len(witnessed)/len(eligible) if eligible else 0.,
                         profiles_with_numerical_failures=sum(r['failures']>0 for r in valid),
                         failed_unique_solves=sum(r['failures'] for r in valid),
                         near_threshold_effects=sum(abs(r[kind+'_effect']-threshold)<1e-7 for r in valid),
                         near_threshold_changes=sum(abs(r[kind+'_change']-threshold)<1e-7 for r in valid)))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dataset', default='data/coval_comparisons.jsonl')
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--limit', type=int, default=0)
    parser.add_argument('--temperatures', default='1,2')
    parser.add_argument('--models', default='nemo,qwen25,qwen3')
    parser.add_argument('--taus', default=','.join(map(str, TAUS)))
    parser.add_argument('--betas', default=','.join(map(str, BETAS)))
    parser.add_argument('--threshold', type=float, default=.01)
    args = parser.parse_args()
    assert 1 <= args.workers <= 4
    args.output_dir.mkdir(parents=True, exist_ok=True)
    source_paths = [Path(__file__), Path('scripts/coval/profiles.py'), *Path('scripts/theory').glob('*.py')]
    metadata = dict(dataset=args.dataset, limit=args.limit, temperatures=args.temperatures,
                    models=args.models, taus=args.taus, betas=args.betas, threshold=args.threshold,
                    python=platform.python_version(), numpy=np.__version__, scipy=scipy.__version__,
                    hashes={str(p): file_hash(p) for p in [*source_paths, Path(args.dataset), *map(Path, REFS.values())]})
    meta_path = args.output_dir/'metadata.json'
    if meta_path.exists() and json.loads(meta_path.read_text()) != metadata:
        raise SystemExit('Checkpoint provenance differs. Use a new output directory.')
    meta_path.write_text(json.dumps(metadata, indent=2, sort_keys=True)+'\n')
    tasks = [(m, r, p, t, str(args.output_dir)) for t in map(float, args.temperatures.split(','))
             for m in args.models.split(',') for r, values in [('nlhf',args.taus), ('rtbt',args.betas)]
             for p in map(float, values.split(',')) if values]
    start = time.monotonic(); summary = []
    with ProcessPoolExecutor(max_workers=args.workers, mp_context=mp.get_context('fork'),
                             initializer=init_worker, initargs=(args.dataset,args.limit)) as pool:
        futures = [pool.submit(task, t) for t in tasks]
        for i, future in enumerate(as_completed(futures), 1):
            path, records = future.result()
            summary.extend(summarize(records,args.threshold))
            print(json.dumps(dict(completed=i, total=len(tasks), file=path,
                                  seconds=round(time.monotonic()-start,1),
                                  solves=sum(r['solve_count'] for r in records),
                                  failures=sum(r['failures'] for r in records))), flush=True)
    summary.sort(key=lambda r:(r['temperature'],r['rule'],r['axiom'],r['model'],r['param']))
    with (args.output_dir/'summary.csv').open('w') as handle:
        writer=csv.DictWriter(handle,fieldnames=list(summary[0]));writer.writeheader();writer.writerows(summary)
    print('Finished',len(summary),'summary rows',flush=True)

if __name__=='__main__': main()
