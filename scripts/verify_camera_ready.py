#!/usr/bin/env python3
"""Verify shipped bytes and saved-result consistency without scientific reruns."""
import ast
import csv
import gzip
import hashlib
import json
import math
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LOCAL_ONLY = {'.git','__pycache__','.lake','output','local_models','.ruff_cache'}
def local_only(path):
    # Gitignored working directories created by setup, reproduction runs and Lean builds.
    parts=path.relative_to(ROOT).parts
    return bool(LOCAL_ONLY&set(parts)) or any(p.startswith('.venv') for p in parts) or parts[:2]==('results','intermediate')
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def readj(rel):
    return json.loads((ROOT/rel).read_text())
def jsonl(rel):
    with (gzip.open(ROOT/rel,'rt') if str(rel).endswith('.gz') else (ROOT/rel).open()) as f:
        return [json.loads(line) for line in f if line.strip()]
def csvrows(rel):
    with (ROOT/rel).open(newline='') as f:
        return list(csv.DictReader(f))
def require(condition,message):
    if not condition: raise AssertionError(message)

def verify():
    formalization_documents = {
        'ASSUMPTION_SUMMARY.md',
        'CITATION_AND_PROVENANCE.md',
        'FORMALIZATION_COVERAGE.md',
        'FORMALIZATION_INDEX.md',
        'FORMALIZATION_STATUS.md',
        'LEAN_DOCKER_NOTES.md',
        'PROOF_FAITHFULNESS.md',
    }
    require({path.name for path in (ROOT/'formalization').glob('*.md')} == formalization_documents,
            'Unexpected formalization document inventory')
    require(not any(ROOT.rglob('.DS_Store')), 'Unexpected filesystem metadata')
    require(not any((ROOT/'formalization').glob('*.log')),
            'Unexpected formalization development log')
    audit_directories = {path.name for path in (ROOT/'formalization/audits').iterdir() if path.is_dir()}
    require(audit_directories == {'verification-2026-11-03-comment-fix'},
            'Unexpected formalization audit directory')
    public_prose = [ROOT/'README.md', ROOT/'SUPPLEMENT_MANIFEST.md', ROOT/'artifact_instructions.txt']
    public_prose.extend((ROOT/'docs').glob('*.md'))
    public_prose.extend(path for path in (ROOT/'formalization').rglob('*')
                        if path.is_file() and not local_only(path) and path.suffix in {'.md', '.lean', '.sh', '.json', '.log'})
    private_wording = re.compile(
        r'\bconversation\b|\bOverleaf\b|\brebuttal\b|\bmain_[A-Za-z0-9_]+\.tex\b|'
        r'coauthor draft|agreed with the author|author chose|author accepts',
        re.IGNORECASE,
    )
    for path in public_prose:
        require(not private_wording.search(path.read_text()),
                'Internal wording in public documentation: '+str(path.relative_to(ROOT)))
    declared={}
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        h,rel=line.split('  ',1)
        require(rel not in declared,'Duplicate manifest file: '+rel)
        declared[rel]=h
        require(digest(ROOT/rel)==h,'Changed packaged file: '+rel)
    shipped={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and not local_only(p)}
    require(shipped==set(declared)|{'SHA256SUMS'},'Unexpected or omitted package file')
    for version in ['historical','completion_2026_11_01','initial_theory_audit']:
        manifest=readj(f'code_versions/{version}/SOURCE_MANIFEST.json')
        for rel,h in {**manifest['files'],**manifest.get('additional_uninvoked_support_files',{})}.items():
            require(digest(ROOT/f'code_versions/{version}'/rel)==h,'Source version differs: '+version+'/'+rel)
    source_map=readj('docs/PACKAGE_SOURCE_MAP.json')
    require(set(source_map['files']) == set(declared)-{'docs/PACKAGE_SOURCE_MAP.json'},
            'Source map inventory differs')
    original_files=source_map['original_files']
    for rel,entry in source_map['files'].items():
        require(entry['sha256']==declared[rel], 'Source map hash differs: '+rel)
        expected_paths=sorted(path for path,h in original_files.items() if h==entry['sha256'])
        require(entry.get('submission_paths',[])==expected_paths,
                'Submission source attribution differs: '+rel)
        require(entry.get('submission_sha256')==original_files.get(rel),
                'Submission path hash differs: '+rel)
    for rel,h in source_map['training_source_sha256'].items():
        require(digest(ROOT/rel)==h,'Training source differs: '+rel)
        require(original_files[rel]==h,'Training source differs from submission inventory: '+rel)
    worked_examples=source_map['worked_example_reference_source']
    for rel,entry in worked_examples['files'].items():
        require(digest(ROOT/rel)==entry['sha256'],'Worked-example reference source differs: '+rel)
    example_references=jsonl('results/reference_distributions/worked_examples/nemo_pytorch_rho_strip_identity.jsonl')
    example_ids={r['prompt_id'] for r in example_references}
    require(len(example_references)==len(example_ids)==worked_examples['reference_count'],
            'Worked-example reference count or uniqueness differs')
    require(set(worked_examples['paper_prompt_ids'])<=example_ids,
            'Missing worked-example reference')
    counts={}
    for model,dc,nc in [('qwen25',154,215),('qwen3',167,221),('nemo',199,279)]:
        for rule,group,count in [('dpo','dpo_rtbt',dc),('nlhf','nlhf_nashmd',nc)]:
            rows=jsonl(f'results/empirical/{group}/filtered_profile_sweeps/{model}.jsonl')
            require(len(rows)==len({r['case_key'] for r in rows})==count,'Cohort count/uniqueness: '+model+rule)
            require(all(not r.get('error') for r in rows),'Error in final cohort')
            for r in rows:
                for field in ['reference_probs','theoretical_probs','final_probs']:
                    values=list(r[field].values())
                    require(all(math.isfinite(x) and -1e-12<=x<=1+1e-12 for x in values),'Invalid saved probabilities')
                    require(abs(sum(values)-1)<1e-8,'Saved probability normalization')
                if rule=='nlhf':require(r['nlhf_exploration_epsilon']==.0001,'Wrong epsilon cohort')
            keys=(ROOT/f'results/case_keys/{model}_{rule}.case_keys.txt').read_text().splitlines()
            require(keys==[r['case_key'] for r in rows],'Case list differs from cohort')
            counts[model+'_'+rule]=count
    batch=readj('results/empirical/nlhf_nashmd/completion_batches.json')
    expected=readj('code_versions/completion_2026_11_01/SOURCE_MANIFEST.json')['files']
    for name,b in batch['batches'].items():
        require(b['provenance']['sources']==expected,'Recorded batch sources do not match snapshot')
    completion=jsonl('results/empirical/nlhf_nashmd/completion85.jsonl')
    successes={r['case_key']:r for r in completion}
    require(len(completion)==len(successes)==85 and all(not r.get('error') for r in completion),'Successful completion cohort differs')
    final={r['case_key']:r for r in jsonl('results/empirical/nlhf_nashmd/filtered_profile_sweeps/nemo.jsonl')}
    for key,r in successes.items():
        for field in ['final_probs','reference_probs','train_seconds']:
            require(final[key][field]==r[field],'Saved trained result changed: '+key+'/'+field)
    runs=jsonl('results/audits/commutativity-training-2026-10-28/all_current_documented_runs.jsonl.gz')
    require(len(runs)==502,'Two-stage run count')
    require(all(r['run']['exploration_epsilon']==.0001 and r['run']['steps_per_stage']==300 for r in runs),'Two-stage protocol')
    points=csvrows('results/figure_plot_data/nlhf_commutativity_single_profile_nashmd_agreement_plot_data.csv')
    require(len(points)==249,'Commutativity figure membership')
    expected_counts={'Qwen2.5':(88,31),'Qwen3':(78,34),'Nemo':(83,37)}
    for model,(n,v) in expected_counts.items():
        rr=[r for r in points if r['model']==model]
        require((len(rr),sum(r['empirical_violation']=='True' for r in rr))==(n,v),'Commutativity counts '+model)
    # Check the preserved optimizer is constructed in the outer function, before training stages.
    tree=ast.parse((ROOT/'code_versions/historical/scripts/post_training/train_coval_nash_md_commutativity.py').read_text())
    main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
    optimizer=[i for i,n in enumerate(main.body) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='optimizer' for t in n.targets)]
    require(len(optimizer)==1,'Historical optimizer is not constructed once in main')
    loop=[i for i,n in enumerate(main.body) if isinstance(n,ast.For) and any(isinstance(x,ast.Attribute) and x.attr=='step' for x in ast.walk(n))]
    require(len(loop)==1 and optimizer[0]<loop[0],'Historical optimizer stage carryover differs')
    for temp in ['T1','T2']:
        base=f'results/audits/replacement-figure-data-2026-10-28/{temp}/'
        cond={(r['panel'],r['model'],r['param_value']):r for r in csvrows(base+'conditioned_frequencies.csv')}
        unc={(r['panel'],r['model'],r['param_value']):r for r in csvrows(base+'unconditioned_plot_data.csv')}
        require(len(cond)==len(unc)==90 and cond.keys()==unc.keys(),'Frequency grids differ')
        for k,r in cond.items():
            a,b=int(r['profiles_with_witness']),int(r['profiles_eligible']);u=unc[k]
            require(a==int(u['profiles_with_witness']) and 0<=a<=b<=int(u['profiles_total']),'Frequency numerators/denominators disagree')
            require(math.isclose(float(r['percent_with_witness']),100*a/b if b else 0,abs_tol=1e-8),'Frequency percentage')
    figure_hashes=readj('results/figure_plot_data/FINAL_FIGURE_HASHES.json')
    require(len(figure_hashes)==17,'Figure count')
    for name,h in figure_hashes.items():require(digest(ROOT/'paper/figures'/name)==h,'Final figure differs: '+name)
    figure_checks=readj('docs/FIGURE_CHECKS.json')
    for rel,h in {**figure_checks['input_sha256'],**figure_checks['render_source_sha256']}.items():
        require(digest(ROOT/rel)==h,'Figure input/source differs: '+rel)
    require({item['figure'] for item in figure_checks['figures']}==set(figure_hashes),
            'Figure verification inventory differs')
    for item in figure_checks['figures']:
        require(figure_hashes[item['figure']]==item['sha256'],'Figure export hash differs')
        require(item['all_fonts_embedded'] and item['no_type3'],'Figure font check failed')
        if item['figure'].startswith('filtered_') and '_dpo_' in item['figure']:
            model=item['figure'].split('_')[1]
            require(item['selection_subtitle']==str(counts[model+'_dpo'])+' profiles selected for DPO training',
                    'Figure selection subtitle differs')
    lean=readj('formalization/audits/verification-2026-11-03-comment-fix/verification.json')
    require(lean['result']=='passed' and lean['exit_code']==0 and lean['export_count']==57,
            'Lean receipt differs')
    require(lean['all_exports_standard_axioms_only'], 'Lean axiom audit differs')
    require(digest(ROOT/'formalization/audits/verification-2026-11-03-comment-fix/lean-artifact-audit.log')
            ==lean['verification_log_sha256'], 'Lean verification log differs')
    for rel,h in lean['checked_source_sha256'].items():
        require(digest(ROOT/rel)==h,'Lean source differs: '+rel)
    for rel,h in lean['checked_document_sha256'].items():
        require(digest(ROOT/rel)==h,'Lean documentation differs: '+rel)
    # Syntax and internal import closure only. Do not import scientific or model code.
    python_count=0
    for scope in [ROOT,*[ROOT/'code_versions'/v for v in ['historical','completion_2026_11_01','initial_theory_audit']]]:
        for f in (scope/'scripts').rglob('*.py'):
            tree=ast.parse(f.read_text());python_count+=1
            for n in ast.walk(tree):
                modules=[n.module] if isinstance(n,ast.ImportFrom) and n.module else [x.name for x in n.names] if isinstance(n,ast.Import) else []
                for m in modules:
                    if m.startswith('scripts.'):
                        path=scope/Path(*m.split('.'))
                        require(path.with_suffix('.py').is_file() or (path/'__init__.py').is_file(),'Missing module '+m+' used by '+str(f))
    return {'status':'PASS','checked_files':len(declared),'python_modules':python_count,'cohort_counts':counts,'completion_successes':85,'detailed_failed_attempt_logs_included':False,'commutativity_runs':502,'commutativity_plotted_pairs':249,'figure_pdfs':17,'lean_source_files_checked':len(lean['checked_source_sha256']),'lean_exact_source_hashes':len(lean['checked_source_sha256']),'lean_public_declarations_in_saved_audit':57,'training_or_numerical_audits_rerun':False,'lean_rerun':False}

if __name__=='__main__':
    print(json.dumps(verify(),indent=2))
