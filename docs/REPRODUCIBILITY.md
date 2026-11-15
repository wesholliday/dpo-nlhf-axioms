# Reproducibility guide

The package preserves the original data / reference / theory / training /
figure organization. Use `docs/FIGURES.md` for a CPU-only regeneration of all
final figures. Use `docs/TRAINING_REPRODUCTION.md` for training source versions
and explicit recorded settings. `docs/CODE_AND_RESULT_PROVENANCE.md` explains
reference conventions, batch seeds and the corrected downstream calculations.

## Corrected numerical computations

The saved complete outputs are included, so rerunning these searches is not
needed to regenerate figures. To recompute the theory studies in a fresh
output directory, use the original audit entrypoints with their saved
metadata settings:

```sh
python -m scripts.additional_checks.audit_numerical_release --help
python -m scripts.additional_checks.audit_commutativity --help
```

Use the three complete files in `results/reference_distributions/` and the
unchanged `data/coval_comparisons.jsonl`. The numerical study covers both
reference temperatures, three models, and the listed tau/beta grids. The
commutativity study caps the number of distinct ranking types at 12 and
retains the lower-bound interpretation. Saved metadata and the numerical
repair note state the actual settings.

The final commutativity comparisons can be reconstructed from the included
training records using `recover_commutativity_inputs.py` and
`--runs-input results/audits/commutativity-training-2026-10-28/all_current_documented_runs.jsonl.gz`.
The comparison CSV and 502-run bundle contain the scientific records used
for the commutativity figure. The selection and target-calculation modules
are also included.
Use the curated JSONL cohorts for figure reproduction and the versioned
training commands in `docs/TRAINING_REPRODUCTION.md` for experimental
reproduction.

## Formal verification

The latest Lean sources match the saved completed Docker audit. See
`formalization/FORMALIZATION_INDEX.md`. Repeat Lean only through
`make check-lean-docker`; package inspection and figure regeneration do not
require Lean or Docker.
