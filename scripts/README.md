# Camera-ready script entrypoints

Use `python -m scripts.figures.rebuild_camera_ready` for all final figures,
`python scripts/verify_camera_ready.py` for saved-file checks, and the commands
in `docs/TRAINING_REPRODUCTION.md` for exact training source selection.
Original entrypoints are retained below for familiarity. Legacy renderer
paths may refer to submitted data; the camera-ready wrapper supplies the
accepted inputs and font settings.


The scripts are organized around the reproduction workflow. Run commands from the repository root with `python -m ...` so package imports resolve consistently.

## 1. CoVal Profiles

`scripts/coval/`

- `profiles.py`
  Parses CoVal ranking blocks into profile objects and pairwise win/tie matrices used by the voting-rule code.

## 2. Reference Distributions

`scripts/reference_distributions/`

- `extract_model_reference_pytorch.py`
  Scores each CoVal candidate response under a Hugging Face base model and normalizes the sequence log probabilities to obtain the reference distribution $\rho$ over the finite candidate set.

Example:

```zsh
python -m scripts.reference_distributions.extract_model_reference_pytorch \
  --dataset data/coval_comparisons.jsonl \
  --model local_models/qwen25_7b_bf16 \
  --output-dir output/reproduction/reference_distributions \
  --output output/reproduction/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl \
  --identity-mode strip_identity
```

## 3. Closed-Form Voting Rules

`scripts/theory/`

- `nlhf_tie_normalization.py`
  Tie-normalized NLHF fixed-point solver. It solves the centered fixed-point
  system from the paper using SciPy `root`; the implementation applies the
  factor-of-two KL scaling that appears when normalized supports are rewritten
  as normalized margins.
- `search_model_reference_violation_counts.py`
  RTBT model-reference witness searches used by the DPO involvement checks.
  The paper-facing NLHF searches use the tie-normalized scripts below.
- `search_nlhf_tie_normalization_examples.py`
  NLHF example/witness search under the tie-normalized rule.
- `cache_nlhf_tie_threshold_effects.py`
  Builds compact NLHF threshold caches used by figure scripts.
- `summarize_theory_change_conditioned_frequencies.py`
  Produces theory-change-conditioned violation summaries.
- `sweep_nlhf_tie_normalization_parameters.py`
  Parameter sweeps for closed-form PB, RTBT, and NLHF violation frequencies.
- `select_theory_change_case_keys.py`
  Selects profile keys satisfying a nontrivial theory-update threshold.
- `count_rtbt_domain_profiles.py`
  Counts CoVal profiles in RTBT's strongly connected domain.

RTBT values are computed by solving the Bradley-Terry likelihood equations on
the strongly connected domain. The implementation uses SciPy `root` with an
analytic Jacobian and a least-squares fallback, then applies the reference tilt
from the RTBT definition.

The remaining files in `scripts/theory/` are helper modules or legacy search
entry points retained for provenance; the paper-facing pipeline is the set
listed above.

## 4. Actual Post-Training

`scripts/post_training/`

- `train_coval_dpo.py`
  Single-profile DPO LoRA training and candidate scoring.
- `train_coval_dpo_multi_profile.py`
  Joint multi-profile DPO LoRA training.
- `train_coval_nash_md.py`
  Single-profile Nash-MD LoRA training and candidate scoring.
- `train_coval_nash_md_commutativity.py`
  Nash-MD commutativity-witness checks.
- `batch_profile_empirical_vs_theory.py`
  Runs empirical training checks over a list of profiles.
- `orchestrate_empirical_vs_theory_chunked.py`
  Restartable chunk wrapper for long empirical sweeps.
- `monitor_empirical_vs_theory_run.py`
  Lightweight progress monitor for JSONL empirical outputs.
- `summarize_empirical_vs_theory_run.py`
  Summarizes an empirical-vs.-theory JSONL run.

Example:

```zsh
python -m scripts.theory.select_theory_change_case_keys \
  --rule rtbt \
  --rho-cache results/reference_distributions/qwen25_pytorch_rho_strip_identity.jsonl \
  --beta 0.1 \
  --tv-threshold 0.01 \
  --output-dir results/intermediate/theory_change_case_selection \
  --tag qwen25_rtbt_beta0.1

python -m scripts.post_training.orchestrate_empirical_vs_theory_chunked \
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
  --output-root results/intermediate/empirical_vs_theory_qwen25_dpo
```

See the repository `README.md` for the Mistral-Nemo variants and Nash-MD
commands, whose paper settings differ from the generic CLI defaults.

## 5. Figures

`scripts/figures/`

Plotting scripts for the paper figures. See `docs/FIGURES.md` for exact commands and output filenames.

## Additional Checks

`scripts/additional_checks/`

- `smoke_test_reproducibility.py`
  Fast local checks for the NLHF solver and empirical summary schemas.
- `check_submission_artifact.py`
  Broader packaging check for parseability, core data counts, figure presence,
  and the smoke test.

## Orchestration

`scripts/orchestration/run_with_caffeinate.sh` wraps long macOS runs in `caffeinate`.

## Output Policy

Curated outputs used by the paper live under `results/`. New large or scratch outputs should go under ignored paths such as `results/intermediate/`, `results/raw/`, `local_artifacts/`, or `large_results/`.
