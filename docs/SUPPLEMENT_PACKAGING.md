# Supplement Packaging Notes

This note records the final packaging hygiene checks for the repository.

## Formalization

- The Lean artifact is under `formalization/`.
- The reviewer entrypoint is
  `formalization/PaperFormalization/PaperStatements.lean`.
- The paper-facing theorem graph has no project-specific axiom. NLHF existence
  uses the proved direct Sion specialization in `NLHFExistence.lean`.
- No Brouwer/Sperner proof backend or assumed fixed-point wrapper is vendored
  in the supplementary material.
- `formalization/scripts/check_artifact.sh` checks for `sorry`/`admit`,
  unexpected project-specific axioms, `Lean.trustCompiler`, missing
  reviewer-facing docs, missing statement-shape audits, and forbidden
  fixed-point compatibility or Brouwer/Sperner imports.
- `make check-lean-docker` is the recommended isolated Lean check.
- `scripts/check_supplement.sh` runs repository packaging checks from the
  repository root and never invokes host Lean.
- `make check-supplement` is an alias for the same packaging check.
- A supplement without manuscript source still runs the complete Lean build,
  axiom audit, statement-shape audit, and documentation checks. Only the lookup
  of theorem labels in the manuscript is skipped. When source is included, the
  checker uses it; an explicitly supplied but missing `PAPER_SOURCE` is an error.

## Paper Artifacts

The paper is published separately. The supplement includes the figure PDFs
under `paper/figures/` and the data and code used to reproduce them.

The result directories contain compact CSV/JSON/JSONL inputs for rebuilding
figures and tables, not extra generated PDFs.

The source attribution for mathematical references is recorded in
`formalization/CITATION_AND_PROVENANCE.md`; local working copies of papers, if
any, should not be added to the supplement.

## Generated And Local Files

Do not package:

- `formalization/.lake/`;
- model checkpoints or LoRA adapter weights;
- unrelated local formalization experiments;
- TeX auxiliary files;
- exploratory notebooks; or
- unlicensed third-party code or paper PDFs.

Before submitting, run the packaging check:

```zsh
scripts/check_supplement.sh
```

or:

```zsh
make check-supplement
```

Then run the Lean audit in Docker:

```zsh
make check-lean-docker
```

Then inspect `git status --short --untracked-files=all` from the repository
root and make sure any untracked local working references are excluded.
