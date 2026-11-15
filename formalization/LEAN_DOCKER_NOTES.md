# Lean Docker Check Notes

This note records the preferred way to run the Lean artifact in an isolated
environment.  It is operational guidance only; the mathematical entrypoints are
`FORMALIZATION_INDEX.md`, `PaperFormalization/PaperStatements.lean`, and
`PROOF_FAITHFULNESS.md`.

Lean checks for this repository must run inside Docker. Direct host checks of
some large targets caused machine-level crashes on macOS, while running the
same checks inside Docker with explicit memory and CPU limits completed
without destabilizing the host.

## Recommended Check

From a fresh copy of the repository, excluding `.git` and `formalization/.lake`,
populate the mathlib cache and run the artifact audit:

```bash
docker build --memory=12g \
  -f formalization/docker/lean-check.Dockerfile \
  -t ptpv-lean-check:4.30.0 formalization/docker

docker run --rm --memory=12g --cpus=4 \
  -v /path/to/post-train-prob-voting:/work \
  -w /work/formalization ptpv-lean-check:4.30.0 \
  lake exe cache get

docker run --rm --memory=12g --cpus=4 \
  -v /path/to/post-train-prob-voting:/work \
  -w /work/formalization ptpv-lean-check:4.30.0 \
  bash -lc 'scripts/check_artifact.sh'
```

The Docker workflow keeps Linux `.lake` build products out of a host checkout
when run against an isolated copy or mounted artifact directory.

## No Host Check

Do not invoke `lean`, `lake`, or `scripts/check_artifact.sh` directly on the
host. The root `Makefile` intentionally disables `check-lean-host`; use
`make check-lean` or `make check-lean-docker`.

## Artifact Hygiene

- Keep `lakefile.lean`, `lake-manifest.json`, and `lean-toolchain` tracked.
- Do not package `formalization/.lake/`; it is a local dependency and build
  cache.
- Do not add local copies of third-party papers or unlicensed third-party Lean
  code to the supplement.
