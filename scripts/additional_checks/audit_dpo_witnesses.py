"""Validate DPO involvement witnesses and identify reference-cache drift."""
import csv,json
from pathlib import Path
import numpy as np
from scripts.coval.profiles import load_cases_tie_norm,parse_ranking,strictly_first_candidate
from scripts.theory.search_nlhf_tie_normalization_examples import strictly_last_candidate,load_rho_cache
from scripts.theory.search_strict_weak_positive_involvement import solve_weighted_logistic_borda
from scripts.additional_checks.audit_numerical_release import REFS

def tv(a,b):return float(np.abs(np.asarray(a)-np.asarray(b)).sum()/2)
def main():
 cs={c.prompt_id+':'+c.block_name:c for c in load_cases_tie_norm(Path('data/coval_comparisons.jsonl'),['world','personal'])}
 rows=[];summaries=[]
 for model,path in REFS.items():
  cache=load_rho_cache(Path(path));base=Path(f'results/empirical/dpo_rtbt/involvement_witnesses/{model}')
  empirical={r['witness_id']:r for r in csv.DictReader((base/'summary.csv').open())}
  for line in (base/'selected_witnesses.jsonl').open():
   w=json.loads(line);c=cs[w['prompt_id']+':'+w['block_name']];i=w['assessment_index'];labels=c.response_indices
   ranking=c.rankings[i];candidate=w['candidate'];k=labels.index(candidate)
   assert (strictly_first_candidate(ranking,labels) if w['axiom']=='positive_involvement' else strictly_last_candidate(ranking,labels))==candidate
   before=np.asarray(c.total_wins)-np.asarray(c.wins_per_ranking[i]);after=np.asarray(c.total_wins)
   rho=np.asarray(w['rho']);rho/=rho.sum()
   p=solve_weighted_logistic_borda(w['param'],before,rho);q=solve_weighted_logistic_borda(w['param'],after,rho)
   assert p is not None and q is not None
   sign=1 if w['axiom']=='positive_involvement' else -1;effect=sign*float(p[k]-q[k])
   current=np.array([cache[c.prompt_id]['rho'][x] for x in labels]);current/=current.sum()
   pnew=solve_weighted_logistic_borda(w['param'],before,current);qnew=solve_weighted_logistic_borda(w['param'],after,current)
   new_effect=sign*float(pnew[k]-qnew[k])
   em=empirical[w['witness_id']];emp_effect=sign*(float(em['reduced_empirical_candidate_prob'])-float(em['full_empirical_candidate_prob']))
   rows.append(dict(model=model,witness_id=w['witness_id'],saved_theory_error=max(tv(p,w['before']),tv(q,w['after'])),
                    saved_effect_error=abs(effect-w['effect']),reference_cache_tv=tv(rho,current),
                    original_theory_effect=effect,current_cache_theory_effect=new_effect,
                    empirical_effect=emp_effect,empirical_metric_error=abs(emp_effect-float(em['empirical_effect']))))
  sub=[r for r in rows if r['model']==model]
  summaries.append(dict(model=model,witnesses=len(sub),max_saved_theory_tv_error=max(r['saved_theory_error'] for r in sub),
                        max_reference_cache_tv=max(r['reference_cache_tv'] for r in sub),
                        max_empirical_metric_error=max(r['empirical_metric_error'] for r in sub),
                        current_cache_effect_below_0p01=sum(r['current_cache_theory_effect']<.01 for r in sub)))
 out=Path('results/audits/dpo-witnesses-2026-10-28');out.mkdir(parents=True,exist_ok=True)
 (out/'audit.json').write_text(json.dumps(dict(summary=summaries,rows=rows),indent=2)+'\n');print(json.dumps(summaries,indent=2))
if __name__=='__main__':main()
