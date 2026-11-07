"""Rebuild the final 17 figures using saved data and original rendering functions.

No model, training, target solver, frequency search, or numerical audit is run.
Export adjustments are font embedding, the DPO canvas size, and DPO selection labels.
"""
import argparse
import csv
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

os.environ.setdefault('MPLCONFIGDIR', str(Path(tempfile.gettempdir()) / 'ptpv-matplotlib'))
from scripts.figures import plot_combined_violation_frequency_panels as combined
from scripts.figures import plot_unconditioned_violation_frequency_panels as unconditional
from scripts.figures import plot_theory_change_conditioned_magnitude_boxplot as magnitudes
from scripts.figures import plot_commutativity_violation_graphs as commplot
from scripts.figures import plot_nontrivial_reference_update_frequency as nontrivial
from scripts.figures import plot_rtbt_involvement_dpo_agreement as involvement
from scripts.figures import plot_nashmd_commutativity_agreement_panels as nash
from scripts.figures import plot_qwen25_bubble_agreement_panels as bubble
from scripts.figures import plot_qwen25_joint_dpo_bubble_agreement as joint
import matplotlib

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'results/audits/replacement-figure-data-2026-10-28'

def rows(path):
    with path.open(newline='') as f:
        return list(csv.DictReader(f))

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir', type=Path, default=Path('output/camera-ready-figures'))
    a = p.parse_args()
    out = a.output_dir.resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit('Choose an empty output directory to preserve included figures.')
    gs = shutil.which('gs')
    if not gs:
        raise SystemExit('Ghostscript (gs) is required to embed the seven bubble-plot fonts.')
    out.mkdir(parents=True, exist_ok=True)
    os.chdir(ROOT)
    with tempfile.TemporaryDirectory(prefix='ptpv-figure-export-') as temp:
        scratch = Path(temp)
        def paths(stem):
            return scratch/(stem+'.png'), out/(stem+'.pdf')
        with matplotlib.rc_context({'pdf.fonttype': 42}):
            for t in (1, 2):
                folder = DATA/f'T{t}'
                prefix = '' if t == 1 else 'temperature_2_'
                values = rows(folder/'four_panel_plot_data.csv')
                assert len(values) == 120
                for r in values:
                    for k in ('param_value','percent_with_witness'): r[k] = float(r[k])
                    for k in ('profiles_denominator','profiles_with_witness'): r[k] = int(r[k])
                png,pdf = paths(prefix+'violation_frequency_four_panel_min_effect_0p01')
                combined.plot_rows(values,png,None,pdf)
                grouped,effect,change = magnitudes.load_grouped_rows(folder/'single_voter_magnitudes.csv')
                png,pdf = paths(prefix+'effect_size_conditional_ge_0p01_and_theory_change_ge_0p01_boxplot')
                magnitudes.plot_boxplot(grouped,png,None,pdf,effect,change)
                png,pdf = paths(prefix+'commutativity_magnitude_tau0p01_min_effect_0p01_boxplot')
                commplot.plot_magnitudes(rows(folder/'commutativity_magnitudes.csv'),png,None,pdf,.01,.01)
            panel_map = {title:(rule,axiom) for rule,axiom,title,_ in unconditional.PANELS}
            alias = {style['label']:name for name,style in unconditional.MODEL_STYLES.items()}
            values = []
            for r in rows(DATA/'T1/unconditioned_plot_data.csv'):
                rule,axiom = panel_map[r['panel']]
                values.append(dict(model_alias=alias[r['model']],rule=rule,axiom=axiom,param_name=r['param_name'],param_value=float(r['param_value']),profiles_total=int(r['profiles_total']),profiles_with_witness=int(r['profiles_with_witness']),percent_with_witness=float(r['percent_with_witness'])))
            png,pdf = paths('violation_frequency_unconditioned_three_panel_min_effect_0p01')
            unconditional.plot_rows(values,png,None,pdf)
            nontrivial.plot_rows(rows(DATA/'nontrivial_reference_update_frequency.csv'),out/'nontrivial_reference_update_frequency.pdf',.01)
            points = involvement.load_points([(name,ROOT/path) for name,path in involvement.DEFAULT_INPUTS])
            assert len(points) == 67
            from matplotlib.figure import Figure
            original_save = Figure.savefig
            def save_at_original_size(fig,*args,**kwargs):
                fig.set_size_inches(942.48/72,447.84/72,forward=False)
                return original_save(fig,*args,**kwargs)
            Figure.savefig = save_at_original_size
            try: involvement.render_matplotlib(points,out/'rtbt_involvement_single_profile_dpo_agreement.pdf',None)
            finally: Figure.savefig = original_save
            points = {model:[] for model in nash.MODEL_ORDER}
            for r in rows(ROOT/'results/figure_plot_data/nlhf_commutativity_single_profile_nashmd_agreement_plot_data.csv'):
                points[r['model']].append(nash.Point(r['model'],int(r['witness_index']),r['prompt_id'],r['block_name'],float(r['theory_commutativity_magnitude']),float(r['empirical_commutativity_magnitude']),float(r['abs_error']),r['empirical_violation']=='True',r['theory_source']))
            assert [(len(points[m]),sum(x.empirical_violation for x in points[m])) for m in nash.MODEL_ORDER] == [(88,31),(83,37),(78,34)]
            nash.render(points,out/'nlhf_commutativity_single_profile_nashmd_agreement.pdf',None,'NLHF-predicted commutativity magnitude','NLHF vs. Nash-MD: commutativity violations')
        def bubble_export(values,stem,title,subtitle):
            target = bubble.PdfTarget(900,430)
            bubble.render(values,target,title=title,subtitle=subtitle,y_max=1.0)
            raw = scratch/(stem+'.pdf');target.finish(raw)
            subprocess.run([gs,'-q','-sDEVICE=pdfwrite','-dCompatibilityLevel=1.5','-dEmbedAllFonts=true','-dSubsetFonts=true','-dAutoRotatePages=/None','-o',str(out/(stem+'.pdf')),'-c','<</NeverEmbed []>> setdistillerparams','-f',str(raw)],check=True)
            joint.write_plot_data(values,out/(stem+'_plot_data.csv'))
        for model,name,dpo_count,nlhf_count in [('qwen25','Qwen2.5',154,215),('qwen3','Qwen3',167,221),('nemo','Mistral-Nemo',199,279)]:
            for kind,rule,method,count in [('dpo','dpo_rtbt','DPO',dpo_count),('nlhf','nlhf_nashmd','Nash-MD',nlhf_count)]:
                values = bubble.load_rows(ROOT/f'results/empirical/{rule}/filtered_profile_sweeps/{model}.jsonl')
                assert len(values) == count
                title = f'{name} '+('RTBT vs. DPO' if kind=='dpo' else 'NLHF vs. Nash-MD')+': theory vs. experiment'
                subtitle = f'{len(values)} profiles selected for DPO training' if kind=='dpo' else f'{len(values)} profiles with TV(theory, reference) >= 0.01'
                bubble_export(values,f'filtered_{model}_{kind}_bubble_agreement',title,subtitle)
        values = joint.load_rows(ROOT/'results/empirical/dpo_rtbt/joint_qwen25/run.json')
        bubble_export(values,'joint_qwen25_dpo_bubble_agreement','Qwen2.5 RTBT vs. joint DPO: theory vs. experiment',f'{len(values)} profiles; one shared LoRA adapter trained jointly')
    assert len(list(out.glob('*.pdf'))) == 17
    print(f'Wrote 17 figures to {out}')

if __name__ == '__main__':
    main()
