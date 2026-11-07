#!/usr/bin/env python3
"""Generate frequency figures and tables from the saved numerical results."""
import argparse,csv,gzip,json,subprocess,sys
from pathlib import Path
from scripts.figures import plot_combined_violation_frequency_panels as combined
from scripts.figures import plot_unconditioned_violation_frequency_panels as unconditional
from scripts.figures import plot_theory_change_conditioned_magnitude_boxplot as magnitudes
from scripts.figures import plot_commutativity_violation_graphs as commplot
from scripts.figures import plot_nontrivial_reference_update_frequency as nontrivial

MODELS={'nemo':'Nemo','qwen25':'Qwen2.5','qwen3':'Qwen3'}
ALIASES={m:m+'_base_strip_identity' for m in MODELS}
def write_csv(path,rows):
 path.parent.mkdir(parents=True,exist_ok=True)
 with path.open('w') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
def read_records(path):
 with gzip.open(path,'rt') as f:return [json.loads(s) for s in f]
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--numerical-dir',type=Path,default=Path('results/audits/numerical-2026-10-28'))
 p.add_argument('--comm-dir',type=Path,default=Path('results/audits/commutativity-batched-2026-10-28'))
 p.add_argument('--data-output',type=Path,default=Path('results/audits/replacement-figure-data-2026-10-28'))
 p.add_argument('--pdf-output',type=Path,default=Path('output/pdf/camera-ready-audit-2026-10-28'))
 a=p.parse_args();summary=list(csv.DictReader((a.numerical_dir/'summary.csv').open()))
 cs=list(csv.DictReader((a.comm_dir/'summary.csv').open()))
 assert len(summary)==180 and len(cs)==60
 assert all(int(r['failed_unique_solves'])==0 for r in summary)
 assert all(int(r['profiles_with_failures'])==0 for r in cs)
 a.data_output.mkdir(parents=True,exist_ok=True);a.pdf_output.mkdir(parents=True,exist_ok=True)
 baseline=[]
 for temp in [1.,2.]:
  prefix='' if temp==1 else 'temperature_2_';out=a.data_output/('T1' if temp==1 else 'T2');out.mkdir(exist_ok=True)
  cr=[];ur=[];conditioned_summary=[]
  for r in summary:
   if float(r['temperature'])!=temp:continue
   panel=r['rule'].upper()+' '+r['axiom'].capitalize()+' Violation'
   common=dict(panel=panel,model=MODELS[r['model']],param_name='tau' if r['rule']=='nlhf' else 'beta',param_value=float(r['param']),profiles_with_witness=int(r['profiles_with_witness']))
   cr.append(dict(common,profiles_eligible=int(r['profiles_eligible']),percent_with_witness=float(r['conditioned_percent'])))
   ur.append(dict(condition='all',threshold=.01,model_alias=ALIASES[r['model']],source='single_voter',rule='nlhf_tie_norm' if r['rule']=='nlhf' else 'rtbt',axiom=r['axiom'],param_name=common['param_name'],param_value=common['param_value'],profiles_total=int(r['profiles_total']),profiles_with_witness=common['profiles_with_witness'],percent_with_witness=float(r['unconditioned_percent'])))
   conditioned_summary.append(dict(change_threshold=.01,effect_threshold=.01,model_alias=ALIASES[r['model']],rule=ur[-1]['rule'],axiom=r['axiom'],param_name=common['param_name'],param_value=common['param_value'],profiles_eligible=int(r['profiles_eligible']),profiles_with_witness=common['profiles_with_witness'],percent_with_witness=float(r['conditioned_percent'])))
  cp=out/'conditioned_frequencies.csv';up=out/'unconditioned_summary.csv'
  write_csv(cp,cr);write_csv(up,ur);write_csv(out/'profile_conditioned_on_theory_change.csv',conditioned_summary)
  cc=[dict(model=MODELS[r['model']],param_name='tau',param_value=float(r['tau']),profiles_total=int(r['total_profiles']),profiles_with_witness=int(r['profiles_with_witness']),percent_with_witness=100*int(r['profiles_with_witness'])/int(r['total_profiles'])) for r in cs if float(r['temperature'])==temp]
  commpath=out/'commutativity_frequencies.csv';write_csv(commpath,cc)
  combined_rows=combined.load_conditioned_rows(cp)+combined.load_commutativity_rows(commpath)
  combined.write_plot_data(out/'four_panel_plot_data.csv',combined_rows)
  stem=prefix+'violation_frequency_four_panel_min_effect_0p01'
  combined.plot_rows(combined_rows,a.pdf_output/(stem+'.png'),None,a.pdf_output/(stem+'.pdf'))
  mags=[];effects={}
  for model in MODELS:
   for rule,param in [('nlhf',.01),('rtbt',.1)]:
    rows=read_records(a.numerical_dir/f'{model}_{rule}_{param:g}_T{temp:g}.jsonl.gz')
    for r in rows:
     for ax,kind in ([('monotonicity','mono'),('involvement','inv')] if rule=='nlhf' else [('involvement','inv')]):
      if r[kind+'_effect']>=.01:mags.append(dict(category=rule.upper()+' '+ax,model=MODELS[model],profile_key=r['case_key'],effect=r[kind+'_effect'],threshold=.01,change_threshold=.01))
   for r in read_records(a.comm_dir/f'{model}_tau0.01_T{temp:g}.jsonl.gz'):effects[(ALIASES[model],.01,r['case_key'])]=r['effect']
  mpath=out/'single_voter_magnitudes.csv';write_csv(mpath,mags)
  grouped,effect_threshold,change_threshold=magnitudes.load_grouped_rows(mpath)
  stem=prefix+'effect_size_conditional_ge_0p01_and_theory_change_ge_0p01_boxplot'
  magnitudes.plot_boxplot(grouped,a.pdf_output/(stem+'.png'),None,a.pdf_output/(stem+'.pdf'),effect_threshold,change_threshold)
  commmags=commplot.build_magnitude_rows(effects,.01,.01);commplot.write_magnitude_rows(commmags,out/'commutativity_magnitudes.csv')
  stem=prefix+'commutativity_magnitude_tau0p01_min_effect_0p01_boxplot'
  commplot.plot_magnitudes(commmags,a.pdf_output/(stem+'.png'),None,a.pdf_output/(stem+'.pdf'),.01,.01)
  urows=unconditional.load_rows(up,.01);unconditional.write_plot_data(out/'unconditioned_plot_data.csv',urows)
  if temp==1:
   stem='violation_frequency_unconditioned_three_panel_min_effect_0p01'
   unconditional.plot_rows(urows,a.pdf_output/(stem+'.png'),None,a.pdf_output/(stem+'.pdf'))
   subprocess.run([sys.executable,'-m','scripts.figures.generate_frequency_data_tables','--input',str(cp),'--unconditioned-input',str(up),'--output',str(out/'nlhf_conditioned_table.tex'),'--unconditioned-output',str(out/'nlhf_unconditioned_table.tex'),'--rtbt-output',str(out/'rtbt_conditioned_table.tex'),'--rtbt-unconditioned-output',str(out/'rtbt_unconditioned_table.tex')],check=True,stdout=subprocess.DEVNULL)
 for path in sorted(a.numerical_dir.glob('*T1.jsonl.gz')):
  rs=[r for r in read_records(path) if r['in_domain']]
  assert all('baseline_tv' in r for r in rs)
  r=rs[0];eligible=sum(s['baseline_tv']>=.01 for s in rs)
  baseline.append(dict(model_alias=ALIASES[r['model']],rule='nlhf_tie_norm' if r['rule']=='nlhf' else 'rtbt',param_name='tau' if r['rule']=='nlhf' else 'beta',param_value=r['param'],profiles_total=len(rs),profiles_with_nontrivial_update=eligible,percent_tv_ge_threshold=100*eligible/len(rs)))
 write_csv(a.data_output/'nontrivial_reference_update_frequency.csv',baseline)
 nontrivial.plot_rows(baseline,a.pdf_output/'nontrivial_reference_update_frequency.pdf',.01)
 print('Prepared eight PDF figures and four LaTeX tables under',a.pdf_output,a.data_output)
if __name__=='__main__':main()
