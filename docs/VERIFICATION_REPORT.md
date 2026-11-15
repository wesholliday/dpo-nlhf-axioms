# Supplement verification

The package checks cover the experiment cohorts, source versions, numerical
summaries, figures and Lean verification records.

- Single-profile DPO counts are 154, 167 and 199 for Qwen2.5, Qwen3 and Nemo.
- Single-profile Nash-MD counts are 215, 221 and 279.
- The 85 Nemo completions have matching learned distributions, references and
  training durations across the saved completion cohort and final cohort.
- All nine completion-module hashes match the nine batch metadata records.
  The historical source tree and explicit settings identify the earlier
  experiment groups. Its two-stage trainer constructs AdamW once before
  the stage loop.
- All 22 recorded initial numerical-source hashes match the corresponding
  source version. The root batched solver matches the finer-continuation
  version recorded in the numerical metadata.
- The commutativity data contain 502 two-stage runs and 251 pairs. The figure
  contains the 249 pairs meeting the predicted-effect threshold.
- Conditioned and unconditioned frequency numerators agree at both reference
  temperatures. Cohort membership and probability vectors pass consistency
  checks using the saved data.
- The 17 figure PDFs match their export hashes and contain embedded fonts.
  `FIGURE_CHECKS.json` records checks of the included PDFs, their source and
  input hashes, embedded fonts, and DPO selection subtitles.
- The Docker verification on 3 November 2026 rebuilt the Lean project and
  checked 57 public declarations. All 51 source files match the recorded
  SHA256 hashes exactly. The receipt identifies the unedited verification log
  by its SHA256 hash.
- Python syntax, internal module dependencies, package inventory and SHA256
  checks pass.
- The original Nemo worked-example reference file and metadata match their
  recorded Git-source hashes. All five example prompts are present, and their
  probabilities agree with the reference vectors displayed in the paper to
  the printed precision.

Run the package checks with these commands.

```sh
make check-supplement
python scripts/verify_camera_ready.py
```

The Lean build evidence is in
`formalization/audits/verification-2026-11-03-comment-fix/`. Use
`make check-lean-docker` to repeat the full formal verification.
`SHA256SUMS` covers the shipped files. Reproduction outputs are written under
`output/`.
