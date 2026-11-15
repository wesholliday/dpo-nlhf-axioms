# Experiment sources and data

The package contains the experiment cohorts and source versions used for the
camera-ready paper. Training settings are listed in
`docs/TRAINING_REPRODUCTION.md`, and figure inputs in `docs/FIGURES.md`.

`docs/PACKAGE_SOURCE_MAP.json` records the submission archive's SHA256 and
the hashes of its 224 files in `original_files`. For each shipped file,
`submission_paths` lists any byte-identical files in that archive, including
files now stored under a different path. `submission_sha256`, when present,
records the submission-time hash at the same path; comparison with `sha256`
shows whether that file has changed.

## Source versions

| Experiment group | Source version |
|---|---|
| Historical single-profile DPO and Nash-MD, joint DPO, and two-stage Nash-MD | `code_versions/historical/` |
| 85 Nemo single-profile completions | `code_versions/completion_2026_11_01/` |
| Numerical calculations recorded in the theory metadata | `code_versions/initial_theory_audit/` |
| Numerical analysis and plotting entrypoints | Root `scripts/theory/`, `scripts/additional_checks/` and `scripts/figures/` |

The historical source tree records commit
`cf160b84e0c3e9a11ed7b82e800f4a9f24f2a895` and module hashes. Its recorded
settings determine the experiment configuration where command-line defaults
differ. Older runs have source-history and settings evidence. The completion
runs additionally record runtime source hashes for all nine batches, matching
the nine modules listed in their source manifest.

Use the historical commutativity trainer for all 502 two-stage Nash-MD runs.
It creates AdamW once before the two-stage loop and carries its optimizer
state into stage 2. The completion source manifest also records a
commutativity module hash, although the 85 completion runs use the
single-profile batch entrypoint.

The numerical source manifests retain the versions associated with the saved
outputs. The root batched solver uses finer continuation for difficult
partitions, as documented in
`results/audits/commutativity-batched-2026-10-28/numerical_repair.json`.
`docs/SOURCE_COMPARISON.json` identifies the module variants and their hashes.

## Experiment cohorts

| Model | Single-profile DPO | Single-profile Nash-MD | Documented commutativity pairs | Plotted commutativity pairs |
|---|---:|---:|---:|---:|
| Qwen2.5 | 154 | 215 | 88 | 88 |
| Qwen3 | 167 | 221 | 78 | 78 |
| Mistral-Nemo | 199 | 279 | 85 | 83 |

The final Nemo single-profile cohort combines 194 historical successes with
85 completions. Of the completions, 81 ran on H100 GPUs and four on the M3
Ultra after CUDA memory limits were reached. The Qwen3 cohort includes one
M3 completion, identified in `recovered_qwen3.jsonl`.

All 251 documented commutativity pairs and their 502 two-stage run records
are included. The figure uses the 249 pairs whose predicted effect is at
least 0.01. Nemo witnesses 27 and 83 have predicted effects below that
threshold. The full comparison CSV includes these pairs.

## Reference conventions

The five Nemo worked examples use the original float16 base-model reference
evaluations recorded in
`results/reference_distributions/worked_examples/nemo_pytorch_rho_strip_identity.jsonl`.
The accompanying `.meta.json` records evaluation on MPS. Both files are exact
copies from commit `02e19295517651d77b61476dc3e18322da0ab468`; their original
paths, Git object identifiers and SHA256 hashes are recorded under
`worked_example_reference_source` in `docs/PACKAGE_SOURCE_MAP.json`.
The reference file contains 635 prompts, including these five examples.

| Worked example | CoVal prompt ID |
|---|---|
| RTBT positive involvement | `767383db-0f77-59cf-a466-2c3f8a9a90d7` |
| NLHF commutativity | `2720d0fa-c8f8-598d-a849-e73e3ddccabb` |
| NLHF monotonicity | `4d3c4a47-9c32-5a90-86b6-dd10f9b609c3` |
| NLHF positive involvement | `f28448e2-1c89-50ff-83ed-ab8b074a577c` |
| NLHF negative involvement | `5397e39f-4afd-5944-b192-a6b396295aad` |

The paper displays rounded reference probabilities. Calculations use the
full-precision saved values. Aggregate frequency analyses use the separate,
complete `nemo_pytorch_rho_strip_identity_float32.jsonl` reference file.

DPO profile selection uses the saved base-model reference distributions.
Each trained run's target and witness comparison use that run's recorded
reference. The two evaluations can differ numerically. One selected Qwen3
profile has target/reference TV about 0.0084 under its recorded reference,
and three DPO witnesses cross the 0.01 threshold if the selection reference
is substituted. The included cohorts and comparisons use the stated
selection and recorded-reference conventions.

The three DPO agreement figures label their cohorts as profiles selected for
DPO training. This identifies the selection step without asserting that
every plotted distance under the recorded training reference exceeds 0.01.
The figures retain every selected profile.

The commutativity figure's predicted values compose NLHF updates from a
common saved base reference. The trained second stage starts from the learned
first-stage policy and carries the AdamW state forward. Comparisons against
the learned reference and against the recursively computed NLHF reference
therefore measure different aspects of agreement.

The commutativity search uses an analytic TV upper bound to certify profiles
whose violation magnitude cannot reach 0.01. Those cases are recorded as
certified-small. The capped partition search supports the lower-bound
interpretation stated in the paper.

## Numerical methods and summaries

The theory calculations use normalized log probabilities, residual-certified
NLHF solves and canonical ranking-type keys. The figure and table inputs are
under `results/audits/replacement-figure-data-2026-10-28/`.

The numerical metadata store the original source SHA256 values under
package-relative path keys. Their recorded hash values are unchanged.
The `run.model` metadata in the 502 two-stage records use package-relative
model directories under `local_models/`.

Single-profile targets are calculated from their recorded references. The
commutativity summaries are reconstructed from the documented run records.
The saved learned distributions, reference distributions and comparison
values are available for independent inspection.

The Nash-MD experiments use epsilon=1e-4 with zero decay and mixture
coefficient zero. The uniform floor applies to the detached score weights.
Some recorded completion metadata use the label
`exact_finite_slate_regularized_policy_gradient`. For epsilon=1e-4, the loss
source instead implements the uniform-floor score-weighted update. The
recorded epsilon and source hashes specify the executed method.

## Seeds, software and timing

The Nemo completions use eight persistent H100 batches followed by a
separately seeded M3 batch. Seed 0 is set once per batch. The batch lists,
software versions and case assignments are recorded in
`results/empirical/nlhf_nashmd/completion_batches.json`. Hardware and batch
partition affect the RNG trajectory used for training.

The estimated 200 GPU hours in the paper concerns its reported training.
Single-profile and joint runs record approximately 94.25 device-hours.
Two-stage runs lack duration fields, and their contribution is estimated
from batch file timestamps at approximately 74 device-hours.

## Formal verification and figures

The Lean artifact has 57 public declarations. The completed Docker audit
records 51 source-file hashes and standard-axiom dependencies. The package
verifier requires an exact SHA256 match for all 51 files.

The verification receipt and unedited log are in
`formalization/audits/verification-2026-11-03-comment-fix/`. The Docker run rebuilt the
project from an empty project build directory using the pinned dependency
cache. The receipt records the command, resource limits, source hashes and
axiom dependencies. Manuscript label lookup is recorded as skipped because
the manuscript source is distributed separately.

All 17 figure PDFs have embedded fonts. The saved-data reproduction helper
uses the corresponding rendering functions and recorded export settings.
