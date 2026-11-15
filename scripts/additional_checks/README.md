# Additional Checks

This package contains lightweight checks that are not part of the main paper
figure-generation path.

- `smoke_test_reproducibility.py` checks the NLHF solver on a zero-margin
  instance and validates empirical summary CSV schemas.
- `check_submission_artifact.py` checks parseability of curated result files,
  CoVal/RTBT profile counts, reference-cache row counts, included paper
  figures, and then runs the smoke test.  Pass `--run-lean` to also invoke the
  Lean artifact checker when Lake/Lean are installed.
