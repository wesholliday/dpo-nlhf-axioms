"""Reconstruct fully documented current runs without changing curated results."""
import argparse,json,csv,gzip,re
from pathlib import Path
from collections import defaultdict,Counter
import numpy as np
from scipy.special import logsumexp
from scripts.additional_checks.audit_numerical_release import REFS,file_hash
from scripts.additional_checks.audit_commutativity import canonical
from scripts.theory.search_nlhf_tie_normalization_examples import load_rho_cache
from scripts.theory.nlhf_tie_normalization import solve_nlhf_tie_norm_log

LABELS=['A','B','C','D']
def arr(d):return np.array([d[x] for x in LABELS])
def tv(a,b):return float(np.abs(a-b).sum()/2)
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--runs-input',type=Path,help='Public recovered JSONL.gz bundle; no working/ directory is needed with this option.')
 parser.add_argument('--output-dir',type=Path,default=Path('results/audits/commutativity-training-2026-10-28'))
 args=parser.parse_args();out=args.output_dir;out.mkdir(parents=True,exist_ok=True)
 candidates=defaultdict(list);source_hashes={}
 if args.runs_input:
  with gzip.open(args.runs_input,'rt') as f:
   for line in f:
    row=json.loads(line);p=Path(row['source']);d=row['run'];model=row['model_alias']
    source_hashes[str(p)]=row['sha256']
    candidates[(model,d['prompt_id'],d['block_name'],d['order'])].append((p,d))
 else:
  for p in Path('working/nlhf_nashmd/runs').rglob('run.json'):
   model=next((m for m in REFS if p.parts[3].startswith(m+'_commutativity_latest')),None)
   if model is None:continue
   d=json.loads(p.read_text())
   if d.get('order') not in ['12','21']:continue
   source_hashes[str(p)]=file_hash(p)
   candidates[(model,d['prompt_id'],d['block_name'],d['order'])].append((p,d))
 caches={m:load_rho_cache(Path(p)) for m,p in REFS.items()};records=[];run_records=[]
 for model in REFS:
  for old in csv.DictReader(open(f'results/empirical/nlhf_nashmd/commutativity_witnesses/{model}_summary.csv')):
   options={o:candidates[(model,old['prompt_id'],old['block_name'],o)] for o in ['12','21']}
   pairs=[]
   for p,a in options['12']:
    for q,b in options['21']:
     ra={s['stage']:Counter(map(canonical,s['rankings'])) for s in a['stages']}
     rb={s['stage']:Counter(map(canonical,s['rankings'])) for s in b['stages']}
     if ra!=rb:continue
     valid=all(d['steps_per_stage']==300 and d['lr']==3e-6 and d['tau']==.01 and d['exploration_epsilon']==.0001 and d['weight_decay']==0 for d in [a,b])
     if not valid:continue
     # Prefer the pair reproducing the curated empirical endpoints. Retain
     # unmatched but fully documented runs as NEW candidate results, not repairs
     # to an unverified historical run.
     mismatch=tv(arr(a['final_probs']),arr(json.loads(old['empirical_order12_json'])))+tv(arr(b['final_probs']),arr(json.loads(old['empirical_order21_json'])))
     if not np.isfinite(mismatch):mismatch=float('inf')
     pairs.append((mismatch,str(p),str(q),p,q,a,b))
   if not pairs:raise ValueError(f'No matched input/setting pair for {model}/{old["witness_index"]}')
   mismatch,_,_,p,q,a,b=min(pairs,key=lambda t:t[:3])
   rho=arr(caches[model][old['prompt_id']]['rho']);rho/=rho.sum()
   def composed(reference):
    outputs=[]
    for data in [a,b]:
     lr=np.log(reference)
     for stage in data['stages']:
      lr=solve_nlhf_tie_norm_log(.01,np.array(stage['wins']),np.array(stage['ties']),lr)
      if lr is None:raise ValueError('Numerical solve failed')
     outputs.append(np.exp(lr))
    return tv(*outputs)
   predicted=composed(rho)
   recorded_reference=arr(a['base_reference_probs'])
   assert tv(recorded_reference,arr(b['base_reference_probs']))<1e-10
   recorded_prediction=composed(recorded_reference)
   empirical=tv(arr(a['final_probs']),arr(b['final_probs']))
   records.append(dict(model=model,witness_index=int(old['witness_index']),prompt_id=old['prompt_id'],block_name=old['block_name'],
                       theory_common_cached_reference=predicted,empirical_current_raw=empirical,
                       theory_recorded_training_reference=recorded_prediction,
                       recorded_training_predicted_violation=recorded_prediction>=.01,
                       originally_reported_theory=float(old['theory_commutativity_magnitude']),
                       original_vs_current_empirical_endpoints_tv=mismatch if np.isfinite(mismatch) else None,
                       original_empirical_endpoints_finite=bool(np.isfinite(mismatch)),
                       matches_original_empirical_endpoints=mismatch<1e-6,
                       currently_predicted_violation=predicted>=.01,empirical_violation=empirical>=.01,
                       order12_source=str(p),order21_source=str(q),
                       initial_reference_difference_between_orders=tv(arr(a['base_reference_probs']),arr(b['base_reference_probs']))))
   for order,path,data in [('12',p,a),('21',q,b)]:run_records.append(dict(model_alias=model,witness_index=int(old['witness_index']),order=order,source=str(path),sha256=source_hashes[str(path)],run=data))
 with gzip.open(out/'all_current_documented_runs.jsonl.gz','wt') as f:
  for r in run_records:f.write(json.dumps(r,sort_keys=True,allow_nan=False)+'\n')
 with (out/'reconstructed_comparison.csv').open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(records[0]));w.writeheader();w.writerows(records)
 summary=[]
 for model in REFS:
  rs=[r for r in records if r['model']==model];positive=[r for r in rs if r['currently_predicted_violation']]
  recorded_positive=[r for r in rs if r['recorded_training_predicted_violation']]
  summary.append(dict(model=model,documented_pairs=len(rs),changed_finite_empirical_pairs=sum(r['original_empirical_endpoints_finite'] and not r['matches_original_empirical_endpoints'] for r in rs),
                      restored_nonfinite_empirical_pairs=sum(not r['original_empirical_endpoints_finite'] for r in rs),
                      corrected_theory_x_values=sum(abs(r['theory_common_cached_reference']-r['originally_reported_theory'])>1e-6 for r in rs),
                      currently_predicted_positive=len(positive),positive_with_empirical_violation=sum(r['empirical_violation'] for r in positive),
                      recorded_reference_predicted_positive=len(recorded_positive),
                      recorded_reference_positive_with_empirical_violation=sum(r['empirical_violation'] for r in recorded_positive),
                      max_initial_reference_difference=max(r['initial_reference_difference_between_orders'] for r in rs)))
 (out/'reconstruction_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
