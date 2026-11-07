# Camera-ready supplementary material

The package contains the source code, data, figures and formalization for the
camera-ready paper. `README.md` provides the setup and reproduction commands.

| Directory | Contents |
|---|---|
| `data/` | CoVal comparison input |
| `results/reference_distributions/` | Model-reference distributions, including original worked-example inputs |
| `results/empirical/` | DPO and Nash-MD cohorts, settings and summaries |
| `results/audits/` | Numerical outputs and commutativity reconstruction data |
| `results/case_keys/` | Single-profile cohort membership lists |
| `scripts/` | Analysis, rendering and training entrypoints |
| `code_versions/historical/` | Training source and dependencies for the historical experiment groups |
| `code_versions/completion_2026_11_01/` | Source modules and batch lists for the 85 Nemo completions |
| `code_versions/initial_theory_audit/` | Numerical source version matched to the recorded metadata |
| `paper/figures/` | 17 figure PDFs with embedded fonts |
| `formalization/` | Lean project, public documentation and verification records |
| `docs/` | Methods, reproduction instructions and source/data mappings |

`SHA256SUMS` covers every shipped file except itself.
`docs/PACKAGE_SOURCE_MAP.json` records file hashes and submission provenance.
Source-version manifests identify the corresponding
Python module hashes. `docs/VERIFICATION_REPORT.md` summarizes the checks.
