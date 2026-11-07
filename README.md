# Supplementary material for “An Axiomatic Analysis of DPO and NLHF as Reference-Dependent Probabilistic Voting Rules”

by **Wesley H. Holliday, Adam Lesnikowski, and Roberto-Rafael Maura-Rivero**

This repository provides the code, data, figures, and Lean 4 formalizations supporting the paper. The code and documentation were written by Claude Code and Codex under the instruction of the authors.

It includes figure PDFs, CoVal input data, PyTorch-derived reference distributions, numerical search outputs, empirical DPO/RTBT and NLHF/Nash-MD results, and the scripts used to generate the figures and empirical checks.

For the shortest supplement overview, see `SUPPLEMENT_MANIFEST.md`.

Experiment groups use the source versions identified in
`docs/CODE_AND_RESULT_PROVENANCE.md`.
Use the versioned training commands in `docs/TRAINING_REPRODUCTION.md` to
select the source tree and recorded settings for each experiment.

## Licenses and data attribution

The authors' original software and documentation are licensed under the MIT
license in `LICENSE`. OpenAI's CoVal comparison data are distributed under
CC BY 4.0. Dataset attribution, license links, the source revision and the
packaging change are documented in `THIRD_PARTY_NOTICES.md`.

## Repository Layout

- `paper/figures/`
  Final figure PDFs included in the paper.
- `data/`
  The CoVal comparison file used by the scripts.
- `scripts/`
  Reproducibility scripts organized by workflow stage: `coval/`, `reference_distributions/`, `theory/`, `post_training/`, `figures/`, `additional_checks/`, and `orchestration/`.
- `results/`
  Lightweight result files used by the current paper figures and empirical appendix.
- `formalization/`
  Lean 4 formalization files and Lake project included with the project.
  See `formalization/CITATION_AND_PROVENANCE.md` for formalization-specific
  source attribution and third-party code/license notes.
- `docs/`
  Reproducibility notes, model details, result manifest, and current empirical findings.
  See `docs/SUPPLEMENT_PACKAGING.md` for final supplement packaging checks.

## Workflow

The repository separates the reproduction pipeline into four main stages.

1. Extract CoVal preference profiles from `data/coval_comparisons.jsonl` using `scripts/coval/`.
2. Elicit model reference distributions over each profile's candidate responses using `scripts/reference_distributions/`.
3. Run closed-form PB, RTBT, and NLHF computations and axiom-violation searches using `scripts/theory/`.
4. Compare the closed-form predictions with actual LoRA post-training runs using `scripts/post_training/`.

Figure scripts in `scripts/figures/` consume the compact result files from these stages and write the PDFs used by the paper.

## Included Results

The final single-profile DPO cohorts contain 154 / 167 / 199 profiles for
Qwen2.5 / Qwen3 / Mistral-Nemo. The final Nash-MD cohorts contain 215 / 221 / 279
successful profiles. The commutativity plot contains 88 / 78 / 83 pairs for
those models, selected from 251 documented pairs (502 two-stage runs).
Theory data, four frequency tables and all 17
figure PDFs are included. The Lean artifact has 57 public statements and no
project-specific axioms; see its saved verification receipt.

The original reference inputs for the five Nemo worked examples are included
under `results/reference_distributions/worked_examples/`. Their provenance
and distinction from the complete float32 reference file used for aggregate
analyses are described in `docs/CODE_AND_RESULT_PROVENANCE.md`.

## Setup

Create a Python 3.12 environment with the packages in `requirements.txt`. The project was developed with Python 3.12.12. On Apple Silicon, we used PyTorch with MPS when available. Plotting can run on CPU.

```zsh
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

The large base models are not included. Download them separately from Hugging Face into `local_models/` or pass explicit model paths to the scripts.

```zsh
mkdir -p local_models
hf download Qwen/Qwen2.5-7B --revision d149729398750b98c0af14eb82c78cfe92750796 --local-dir local_models/qwen25_7b_bf16
hf download Qwen/Qwen3-8B-Base --revision 49e3418fbbbca6ecbdf9608b4d22e5a407081db4 --local-dir local_models/qwen3_8b_base
hf download mistralai/Mistral-Nemo-Base-2407 --revision a4477a2f977929a969745b69bbd62e03043551a5 --local-dir local_models/mistral_nemo_base_2407
```

## Lean Formalization

The entrypoint is
`formalization/PaperFormalization/PaperStatements.lean`. The Lean 4.30.0 /
mathlib 4.30.0 artifact includes the IPO population-loss reduction and
log-mean proof alignment. All 57 public declarations were verified using only
`propext`, `Classical.choice` and `Quot.sound`, with no project-specific axiom.

`formalization/audits/verification-2026-11-03-comment-fix/verification.json` records
the completed Docker audit. All 51 recorded source files match the receipt's
SHA256 hashes exactly.
The packaging check does not rebuild Lean. To repeat the full audit, use Docker:

```zsh
make check-lean-docker LEAN_DOCKER_MEMORY=32g LEAN_DOCKER_CPUS=8
```

See `formalization/FORMALIZATION_INDEX.md`, `FORMALIZATION_STATUS.md`,
`PROOF_FAITHFULNESS.md` and `ASSUMPTION_SUMMARY.md`. Host Lean is disabled.

## Rebuilding The Paper

The paper is published separately. Its figure PDFs are provided under
`paper/figures/`, with reproduction instructions below.

## Regenerating Figures

Install `requirements-cpu.txt` and Ghostscript (`gs`), then run:

```zsh
make figures
```

This rebuilds all 17 figures from saved data with the original renderers and
font embedding. It runs no models, training, target solver or numerical search.
Figures are written to `output/figures/`, which must be empty before running the command.
See `docs/FIGURES.md` for the figure/data mapping and table locations.

## Package Check

```zsh
make check-supplement
make verify
```

The second command verifies package hashes, source versions, cohort counts,
figure inputs and the saved Lean source receipt without scientific recomputation.

## Main Empirical Pipelines

Reference distributions:

```zsh
python -m scripts.reference_distributions.extract_model_reference_pytorch \
  --dataset data/coval_comparisons.jsonl \
  --model local_models/qwen25_7b_bf16 \
  --output-dir output/reproduction/reference_distributions \
  --output output/reproduction/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl \
  --identity-mode strip_identity
```

Filtered DPO/RTBT profile sweep:

```zsh
python -m scripts.theory.select_theory_change_case_keys \
  --rule rtbt \
  --rho-cache results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl \
  --beta 0.1 \
  --tv-threshold 0.01 \
  --output-dir results/intermediate/theory_change_case_selection \
  --tag qwen25_rtbt_beta0.1

python scripts/run_version.py historical scripts.post_training.orchestrate_empirical_vs_theory_chunked \
  --dataset data/coval_comparisons.jsonl \
  --rule dpo \
  --model local_models/qwen25_7b_bf16 \
  --case-keys-file results/intermediate/theory_change_case_selection/rtbt__tvgeq_0.01__qwen25_rtbt_beta0.1.case_keys.txt \
  --beta 0.1 \
  --lr 5e-5 \
  --steps 100 \
  --dtype float16 \
  --lora-dropout 0.05 \
  --dpo-full-batch \
  --output-root output/reproduction/dpo
```

Mistral-Nemo DPO uses a different learning rate and float32:

```zsh
python -m scripts.theory.select_theory_change_case_keys \
  --rule rtbt \
  --rho-cache results/reference_distributions/nemo_pytorch_rho_strip_identity_float32.jsonl \
  --beta 0.1 \
  --tv-threshold 0.01 \
  --output-dir results/intermediate/theory_change_case_selection \
  --tag nemo_rtbt_beta0.1

python scripts/run_version.py historical scripts.post_training.orchestrate_empirical_vs_theory_chunked \
  --dataset data/coval_comparisons.jsonl \
  --rule dpo \
  --model local_models/mistral_nemo_base_2407 \
  --renderer llama2 \
  --fix-mistral-regex \
  --case-keys-file results/intermediate/theory_change_case_selection/rtbt__tvgeq_0.01__nemo_rtbt_beta0.1.case_keys.txt \
  --beta 0.1 \
  --lr 1e-5 \
  --steps 100 \
  --dtype float32 \
  --grad-clip 1.0 \
  --dpo-full-batch \
  --output-root output/reproduction/dpo
```

Filtered NLHF/Nash-MD profile sweep:

```zsh
python -m scripts.theory.select_theory_change_case_keys \
  --rule nlhf \
  --rho-cache results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl \
  --tau 0.01 \
  --tv-threshold 0.01 \
  --output-dir results/intermediate/theory_change_case_selection \
  --tag qwen25_nlhf_tau0.01

python scripts/run_version.py historical scripts.post_training.orchestrate_empirical_vs_theory_chunked \
  --dataset data/coval_comparisons.jsonl \
  --rule nlhf \
  --model local_models/qwen25_7b_bf16 \
  --case-keys-file results/intermediate/theory_change_case_selection/nlhf__tvgeq_0.01__qwen25_nlhf_tau0.01.case_keys.txt \
  --tau 0.01 \
  --lr 3e-6 \
  --steps 300 \
  --dtype float32 \
  --nlhf-exploration-epsilon 0.0001 \
  --nlhf-mixture-coef 0.0 \
  --grad-clip 1.0 \
  --weight-decay 0.0 \
  --lora-dropout 0.0 \
  --output-root output/reproduction/nlhf
```

Mistral-Nemo Nash-MD uses the same Nash-MD hyperparameters, with the
Mistral-Nemo model, renderer, and complete float32 reference cache:

```zsh
python -m scripts.theory.select_theory_change_case_keys \
  --rule nlhf \
  --rho-cache results/reference_distributions/nemo_pytorch_rho_strip_identity_float32.jsonl \
  --tau 0.01 \
  --tv-threshold 0.01 \
  --output-dir results/intermediate/theory_change_case_selection \
  --tag nemo_nlhf_tau0.01

python scripts/run_version.py historical scripts.post_training.orchestrate_empirical_vs_theory_chunked \
  --dataset data/coval_comparisons.jsonl \
  --rule nlhf \
  --model local_models/mistral_nemo_base_2407 \
  --renderer llama2 \
  --fix-mistral-regex \
  --case-keys-file results/intermediate/theory_change_case_selection/nlhf__tvgeq_0.01__nemo_nlhf_tau0.01.case_keys.txt \
  --tau 0.01 \
  --lr 3e-6 \
  --steps 300 \
  --dtype float32 \
  --nlhf-exploration-epsilon 0.0001 \
  --nlhf-mixture-coef 0.0 \
  --grad-clip 1.0 \
  --weight-decay 0.0 \
  --lora-dropout 0.0 \
  --output-root output/reproduction/nlhf
```

These are historical-protocol examples with explicit scientific settings, not
an exact replay of the final merged cohort or its batch partition. In particular,
the 85 Nemo completions used the separately preserved `completion_2026_11_01`
source version and no `--fix-mistral-regex` flag. See `docs/TRAINING_REPRODUCTION.md`
for the source versions, all three models, the joint run, and batch settings.
The final cohort case lists are under `results/case_keys/`. Recorded settings
are retained alongside the results and in `completion_batches.json`.


Training is expensive and is not needed to inspect or regenerate the included figures.

## Notes On Reproducibility

- The CoVal prompt messages are normalized with `identity_mode=strip_identity`, removing the vendor-specific sentence that identified the model as ChatGPT.
- Reference distributions are computed with PyTorch from canonical Hugging Face checkpoints.
- Generated model weights and LoRA adapters are excluded because they are large and can be regenerated.
- The large intermediate `theory_change_voter_rows.jsonl` is intentionally excluded; compact plot-data CSVs are included, and the raw file can be regenerated.
