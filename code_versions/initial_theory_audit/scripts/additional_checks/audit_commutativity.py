#!/usr/bin/env python3
"""Recheck type-preserving NLHF partitions using log-space composition.

The result is a lower bound over all profiles. For a positive profile, retain
its first witness of at least the threshold, as in the original capped search.
Tied blocks are canonicalized: A=B and B=A are the same ranking type.
"""
import argparse,csv,gzip,json,multiprocessing as mp,time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor,as_completed
from pathlib import Path
import numpy as np
from scipy.special import logsumexp
from scripts.coval.profiles import load_cases_tie_norm,parse_ranking,ranking_to_string,ranking_to_wins_and_ties
from scripts.theory.nlhf_tie_normalization import solve_nlhf_tie_norm_log,normalized_margin_matrix_tie_norm
from scripts.theory.search_nlhf_tie_normalization_examples import load_rho_cache
from scripts.additional_checks.nlhf_batch_audit import solve_batch

def grouped_masks(n):
    return (1 | (tail << 1) for tail in range((1 << (n-1))-1))
from scripts.additional_checks.audit_numerical_release import REFS,TAUS,file_hash

CASES=[];CACHES={}
def initialize(dataset):
    global CASES,CACHES
    CASES=sorted(load_cases_tie_norm(Path(dataset),['world','personal']),key=lambda c:(c.prompt_id,c.block_name))
    if not all({x for b in parse_ranking(r) for x in b}==set(c.response_indices) for c in CASES for r in c.rankings):
        raise ValueError('The pruning bound in this audit requires complete ballots')
    CACHES={k:load_rho_cache(Path(v)) for k,v in REFS.items()}

def canonical(ranking): return ranking_to_string([sorted(block) for block in parse_ranking(ranking)])

def check(case,model,tau,temperature,threshold,cap):
    labels=case.response_indices;idx={x:i for i,x in enumerate(labels)}
    counts=Counter(canonical(r) for r in case.rankings);types=sorted(counts)
    r=dict(case_key=f'{case.prompt_id}:{case.block_name}',model=model,tau=tau,temperature=temperature,
           unique_types=len(types),effect=0.,partitions_tested=0,failures=0,witness=None,skipped=None)
    if not 2<=len(types)<=cap:
        r['skipped']='ranking_type_cap' if len(types)>cap else 'one_ranking_type';return r
    rho=np.array([CACHES[model][case.prompt_id]['rho'][x] for x in labels]);logrho=np.log(rho)/temperature;logrho-=logsumexp(logrho)
    matrices=[ranking_to_wins_and_ties(t,idx) for t in types]
    # Each subprofile margin is an average of these complete-ballot margins.
    # Across two stages, log(pi(j)/pi(a)) increases by at most max_diff/tau.
    ballot_margins=np.array([normalized_margin_matrix_tie_norm(w,t) for w,t in matrices])
    a=int(np.argmax(logrho));max_diff=(ballot_margins-ballot_margins[:,a:a+1,:]).max(axis=(0,2))
    log_ratios=logrho-logrho[a]+max_diff/tau;log_ratios[a]=0
    tv_bound=-np.expm1(-logsumexp(log_ratios))
    if tv_bound < threshold-1e-12:
        r['skipped']='certified_small_tv';r['tv_upper_bound']=float(tv_bound);return r
    weighted_w=np.array([counts[t]*p[0] for t,p in zip(types,matrices)])
    weighted_t=np.array([counts[t]*p[1] for t,p in zip(types,matrices)])
    total_w=weighted_w.sum(0);total_t=weighted_t.sum(0)
    masks=list(grouped_masks(len(types)))
    start=0
    while start<len(masks):
        size=32 if start==0 else 256
        chunk=masks[start:start+size]
        selected=np.array([[bool(mask&(1<<i)) for i in range(len(types))] for mask in chunk])
        w1=np.einsum('bi,ijk->bjk',selected.astype(float),weighted_w)
        t1=np.einsum('bi,ijk->bjk',selected.astype(float),weighted_t)
        w2=total_w-w1;t2=total_t-t1
        def margins(w,t):
            totals=w+w.transpose(0,2,1)+t
            return np.divide(w-w.transpose(0,2,1),totals,out=np.zeros_like(w),where=totals>0)
        m1=margins(w1,t1);m2=margins(w2,t2)
        l1,f1,_=solve_batch(tau,m1,logrho);l2,f2,_=solve_batch(tau,m2,logrho)
        valid=np.ones(len(chunk),dtype=bool);valid[f1+f2]=False;ix=np.flatnonzero(valid)
        effects=np.full(len(chunk),-1.);out12={};out21={}
        if len(ix):
            l12,f12,_=solve_batch(tau,m2[ix],l1[ix]);l21,f21,_=solve_batch(tau,m1[ix],l2[ix])
            valid[ix[f12+f21]]=False
            for j,i in enumerate(ix):
                if not valid[i]:continue
                p12=np.exp(l12[j]);p21=np.exp(l21[j])
                effects[i]=float(np.abs(p12-p21).sum()/2);out12[i]=p12;out21[i]=p21
        hits=np.flatnonzero(effects>=threshold)
        stop=int(hits[0])+1 if len(hits) else len(chunk)
        r['partitions_tested']+=stop
        r['failures']+=int(np.sum(~valid[:stop]))
        if np.max(effects[:stop])>r['effect']:
            best=int(np.argmax(effects[:stop]));r['effect']=float(effects[best])
            r['witness']=dict(rankings_left=[t for i,t in enumerate(types) if selected[best,i]],
                               rankings_right=[t for i,t in enumerate(types) if not selected[best,i]],
                               counts=dict(counts),rho=np.exp(logrho).tolist(),
                               left_then_right=out12[best].tolist(),right_then_left=out21[best].tolist())
        if len(hits):break
        start+=len(chunk)

    return r

def worker(task):
    model,tau,temp,threshold,cap,outdir=task
    path=Path(outdir)/f'{model}_tau{tau:g}_T{temp:g}.jsonl.gz'
    if path.exists():
        with gzip.open(path,'rt') as f:rows=[json.loads(l) for l in f]
    else:
        rows=[]
        for i,c in enumerate(CASES,1):
            rows.append(check(c,model,tau,temp,threshold,cap))
            if i%200==0:print(json.dumps(dict(progress=i,model=model,tau=tau,temperature=temp)),flush=True)
        partial=path.with_suffix('.partial')
        with gzip.open(partial,'wt') as f:
            for r in rows:f.write(json.dumps(r,sort_keys=True,allow_nan=False)+'\n')
        partial.replace(path)
    return dict(model=model,tau=tau,temperature=temp,threshold=threshold,total_profiles=len(rows),
                profiles_with_witness=sum(r['effect']>=threshold for r in rows),
                profiles_over_cap=sum(r['skipped']=='ranking_type_cap' for r in rows),
                profiles_certified_small=sum(r['skipped']=='certified_small_tv' for r in rows),
                profiles_with_failures=sum(r['failures']>0 for r in rows),
                partitions_tested=sum(r['partitions_tested'] for r in rows))

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--taus',default=','.join(map(str,TAUS)));p.add_argument('--temperatures',default='1,2')
    p.add_argument('--models',default='nemo,qwen25,qwen3');p.add_argument('--workers',type=int,default=2)
    p.add_argument('--dataset',default='data/coval_comparisons.jsonl');p.add_argument('--threshold',type=float,default=.01)
    p.add_argument('--max-unique',type=int,default=12);a=p.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True)
    meta=dict(taus=a.taus,temperatures=a.temperatures,models=a.models,threshold=a.threshold,max_unique=a.max_unique,
              hashes={str(x):file_hash(x) for x in [__file__,a.dataset,*REFS.values(),'scripts/theory/nlhf_tie_normalization.py','scripts/additional_checks/nlhf_batch_audit.py']})
    mpth=a.output_dir/'metadata.json'
    if mpth.exists() and json.loads(mpth.read_text())!=meta:raise SystemExit('Checkpoint provenance mismatch')
    mpth.write_text(json.dumps(meta,indent=2,sort_keys=True)+'\n')
    tasks=[(m,t,T,a.threshold,a.max_unique,str(a.output_dir)) for T in map(float,a.temperatures.split(','))
           for m in a.models.split(',') for t in map(float,a.taus.split(','))]
    start=time.monotonic();rows=[]
    with ProcessPoolExecutor(max_workers=a.workers,mp_context=mp.get_context('fork'),initializer=initialize,initargs=(a.dataset,)) as pool:
        for future in as_completed([pool.submit(worker,t) for t in tasks]):
            row=future.result();rows.append(row);print(json.dumps(dict(row,completed=len(rows),seconds=round(time.monotonic()-start,1))),flush=True)
    rows.sort(key=lambda r:(r['temperature'],r['model'],r['tau']))
    with (a.output_dir/'summary.csv').open('w') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

if __name__=='__main__':main()
