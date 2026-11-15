# Formalization Index

This is the shortest path through the Lean artifact for reviewers.

The formalization follows the camera-ready manuscript's partial-Borda
definition. The IPO and Borda-IPO minimization propositions follow the
authors' final appendix text, with public names `BIPOandPB` and `IPOandPB`.
The RTBT extension and the all-lottery NLHF variational lemma have public
wrappers and statement-shape audits.
See `FORMALIZATION_STATUS.md` for coverage limits.

## Start Here

- `PaperFormalization/PaperStatements.lean`
  is the reviewer-facing statement index.  The theorem names mirror the labels
  in the camera-ready manuscript where Lean syntax permits it.
- `PaperFormalization/AssumptionAudit.lean`
  runs `#print axioms` on every theorem in `PaperStatements.lean`.
- `PaperFormalization/PaperStatementShapeAudit.lean`
  contains Lean examples whose types match the most sensitive paper-facing
  statements, so `lake build` fails if those statement shapes drift.
- `FORMALIZATION_COVERAGE.md`
  maps the paper statements and appendix proof labels to the underlying Lean
  declarations.
- `PROOF_FAITHFULNESS.md`
  explains how the Lean proof routes track the English proofs in
  the paper, including places where Lean proves a direct substitute for
  an English citation.
- `ASSUMPTION_SUMMARY.md`
  records that the paper-facing theorem graph has no project-specific axiom
  dependency and explains the limits of `#print axioms` auditing.
- `FORMALIZATION_STATUS.md`
  gives the shortest status summary: what is formalized and what to run.
- `CITATION_AND_PROVENANCE.md`
  records mathematical sources, minimax provenance, and third-party code
  policy for the supplementary artifact.
- `LEAN_DOCKER_NOTES.md`
  records the recommended Docker-based checking workflow for isolated large
  Lean builds.

## Checking

The recommended check path is the Docker workflow in `LEAN_DOCKER_NOTES.md`.
From the repository root, run:

```zsh
make check-lean-docker
```

Run the broader supplement packaging check separately:

```zsh
scripts/check_supplement.sh
```

or:

```zsh
make check-supplement
```

The Lean artifact audit checks that:

- the Lean project builds;
- every `PaperStatements` theorem appears in `AssumptionAudit`;
- the paper-facing axiom audit has no `Lean.trustCompiler` dependency;
- the paper-facing axiom audit prints no project-specific axiom dependency;
- the active source contains no `sorry` or `admit`;
- the active source contains no project `axiom` declaration; and
- no fixed-point compatibility interface or Brouwer/Sperner backend is
  imported.

The output of `AssumptionAudit.lean` is the authoritative axiom audit;
`ASSUMPTION_SUMMARY.md` is only a reviewer-readable summary of that output.

The Docker audit command is:

```zsh
docker run --rm --memory=12g --cpus=4 \
  -v /path/to/post-train-prob-voting:/work \
  -w /work/formalization \
  ptpv-lean-check:4.30.0 \
  bash -lc 'scripts/check_artifact.sh'
```

## Main Proof Files

- IPO and Borda-IPO: `BordaIPO.lean` proves the unique zero-loss minimizer by
  equality of adjusted log ratios, exponentiation, and normalization.
  `OfflineIPO.lean` proves the three linear-profile identities, expands the
  loss difference, cancels its lottery-dependent terms, and applies the
  Borda-IPO result, and reduces the population IPO loss (finite average over
  annotators and ordered pairs) to `IPO_τ` by the bias--variance
  decomposition. All use the existing profile-level Borda and frequency
  definitions.
- Ford/Zermelo, Bradley-Terry, DPO/RTBT:
  `FordZermelo.lean`, `DPO.lean`, `RTBT.lean`, `ProfileFord.lean`,
  `ProfileRTBT.lean`, `RTBTPairMonotonicity.lean`,
  `RTBTCountMonotonicity.lean` (the count-level engine for `RTBTPM`), and
  `AndersonRanking.lean` (the paper-specific BT/Borda ranking equivalence).
- NLHF existence and fixed-point interface:
  `NLHFBasic.lean`, `NLHFExistence.lean` (direct finite Sion specialization),
  `NLHFGammaForm.lean` (the paper's `Γ_τ` / `c̄` form), and
  `WeakProfileNLHF.lean` (profile-level existence).
- NLHF monotonicity threshold:
  `NLHFMonotonicityFinite.lean`, `NLHFMonotonicityThreshold.lean`,
  `NLHFSelectedMonotonicity.lean`, and the profile-level layer
  `WeakProfileMargin.lean`, `NLHFWeakProfileMonotonicity.lean`,
  `NLHFScoreImprovementChaining.lean`, `NLHFScoreImprovementProfiles.lean`,
  and `WeakOrderScoreRepresentation.lean` (exact representation and margin
  transport from arbitrary finite complete/transitive Boolean weak orders).
- Maximal-lottery limit: `MaximalLotteryLimit.lean`,
  `SelectedMaxLottLimit.lean`.
- Weak-relation profiles and the paper's partial-Borda score `B^p`:
  `WeakProfileBorda.lean`.
- Involvement witnesses:
  `ProfileBorda.lean`, `NLHFSelectedInvolvement.lean`,
  `NLHFInvolvement.lean`, and `RTBTInvolvement.lean` (including the direct
  strict-linear profile/add-voter forms of `InvolveViolRTBT`).
- Commutativity:
  `NLHFSelectedCommutativity.lean`, `ProfileNLHFCommutativity.lean`,
  `Commutativity.lean`, and `CommutativityDomain.lean` (the generic
  domain-closure interface, `RTBTorder_domain_abstract`, and the concrete
  variable-electorate `RTBTorder_domain` using actual `B^p` and selected RTBT).

## External Theorem Use

The project uses Mathlib's proved Sion minimax theorem and proves its exact
finite-NLHF specialization locally. It has no project-specific axiom and no
Brouwer/Sperner code is imported or vendored.
