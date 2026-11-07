"""Distinguish cross-prompt fitting error from same-prompt target conflicts."""
import json
from collections import defaultdict
from pathlib import Path
import numpy as np
from scripts.coval.profiles import load_cases_tie_norm
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda

LABELS=['A','B','C','D']
def arr(d):return np.array([d[k] for k in LABELS])
def tv(a,b):return float(np.abs(a-b).sum()/2)
def main():
 d=json.loads(Path('results/empirical/dpo_rtbt/joint_qwen25/run.json').read_text())
 cases={f'{c.prompt_id}:{c.block_name}':c for c in load_cases_tie_norm(Path('data/coval_comparisons.jsonl'),['world','personal'])}
 groups=defaultdict(list)
 for r in d['per_case']:groups[r['prompt_id']].append(r)
 out=[];errors=[];lower_bound=0.
 for pid,rs in groups.items():
  ref=arr(rs[0]['reference_probs']);emp=arr(rs[0]['final_probs'])
  assert all(tv(ref,arr(r['reference_probs']))<1e-10 and tv(emp,arr(r['final_probs']))<1e-10 for r in rs)
  wins=sum(np.asarray(cases[r['case_key']].total_wins) for r in rs)
  pooled=solve_weighted_logistic_borda(d['beta'],wins,ref);assert pooled is not None
  pair_target_tv=tv(arr(rs[0]['theoretical_probs']),arr(rs[1]['theoretical_probs'])) if len(rs)==2 else 0.
  lower_bound+=pair_target_tv
  for r in rs:
   own=solve_weighted_logistic_borda(d['beta'],np.asarray(cases[r['case_key']].total_wins),ref)
   errors.append(tv(own,arr(r['theoretical_probs'])))
  out.append(dict(prompt_id=pid,profiles=len(rs),case_keys=[r['case_key'] for r in rs],
                  own_target_conflict_tv=pair_target_tv,tv_empirical_to_pooled_target=tv(emp,pooled),
                  mean_tv_empirical_to_individual_targets=float(np.mean([tv(emp,arr(r['theoretical_probs'])) for r in rs])),
                  pooled_target=dict(zip(LABELS,pooled))))
 report=dict(profiles=len(d['per_case']),prompts=len(groups),prompts_with_two_profiles=sum(len(rs)==2 for rs in groups.values()),
             profiles_in_shared_prompts=sum(len(rs) for rs in groups.values() if len(rs)>1),
             shared_prompts_with_distinct_targets=sum(r['own_target_conflict_tv']>1e-6 for r in out),
             max_target_conflict_tv=max(r['own_target_conflict_tv'] for r in out),
             unavoidable_mean_individual_target_tv_lower_bound=lower_bound/len(d['per_case']),
             mean_empirical_to_individual_target_tv=float(np.mean([r['tv_to_theory'] for r in d['per_case']])),
             mean_empirical_to_pooled_target_tv_per_profile=sum(r['profiles']*r['tv_empirical_to_pooled_target'] for r in out)/len(d['per_case']),
             max_saved_theory_tv_error=max(errors),
             note='The joint loss pools strict-comparison counts for repeated prompts. Comparing to separate world/personal targets confounds pooling with cross-prompt/model fitting effects.')
 dest=Path('results/audits/joint-dpo-2026-10-28');dest.mkdir(parents=True,exist_ok=True)
 (dest/'audit.json').write_text(json.dumps(dict(summary=report,prompts=out),indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
