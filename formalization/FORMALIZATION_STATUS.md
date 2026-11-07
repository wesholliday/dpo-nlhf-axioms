# Formalization Status

This Lean artifact formalizes the thirteen main-result families and the
IPO and Borda-IPO minimization propositions in the camera-ready manuscript.
The two appendix proofs follow the authors' final appendix text.
`FORMALIZATION_COVERAGE.md` specifies the scope of the formalized statements
and `PROOF_FAITHFULNESS.md` compares their proof routes.

- The camera-ready partial-Borda score is `Σ (c + ½ i + ½ n)`, including
  half credit for unexpressed comparisons. `WeakProfileBorda.lean` uses
  this definition throughout the existing monotonicity, involvement, and
  commutativity results. Pair-normalized NLHF margins and preference
  frequencies retain their original expressed-comparison denominators.
- IPO and Borda-IPO are formalized in `OfflineIPO.lean` and `BordaIPO.lean`,
  following the two appendix proofs. `BIPOandPB` proves that PB is
  the unique full-support minimizer and has zero loss. `IPOandPB` proves
  the unique full-support IPO minimizer on linear-order profiles, with
  parameter `1/(τmn)`, by the displayed constant-difference identity.
  The objectives use the actual `B^p` and `c̄` profile definitions.
  `IPOremark_population` formalizes the opening paragraph of Appendix
  `IPOApp`: the population IPO loss of Azar et al. (Eq. (16)), with the
  expectation written as the finite average over annotators and ordered
  pairs, has the same full-support minimizers as `IPO_τ`, by the
  bias--variance decomposition of the per-pair expected squared loss.
- The RTBT-extension footnote is formalized in `RTBTExtension.lean`:
  existence and uniqueness of the top component on the pairwise-compared
  domain, its BT fit, zero probability outside it, inclusion of linear-order
  profiles, the singleton case, and agreement on the entire original domain.
- Lemma `nlhf-variational` follows the English saddle-point proof and
  allows every comparison lottery, including boundary lotteries. Its public
  wrapper and shape audit enforce that full scope.

- NLHF existence is proved by specializing Mathlib's
  `Sion.exists_isSaddlePointOn` theorem to the finite lottery simplex. The
  artifact proves the required simplex, KL, continuity, convexity, and affine
  margin facts in `NLHFExistence.lean`.
- The Anderson--Dandurova--Falk--Yeganova Bradley-Terry/Borda ranking
  equivalence needed by the paper is proved in `AndersonRanking.lean` for the
  paper's native finite linear-order profiles; their 2009 result is credited
  in the module and in `CITATION_AND_PROVENANCE.md`.
- All paper-facing positive results are stated at the level at which the
  paper states them (weak-relation profiles for `PBPM`, `PBPPI`, `RTBTorder`;
  Ford count matrices plus a weak-profile companion for `RTBTPM`; actual finite
  profiles under the paper's improvement conditions (i)-(iii) for `NLHFmono`).
  In particular, the `1/8` clauses quantify directly over arbitrary finite
  complete/transitive Boolean weak orders and antisymmetric linear orders.
  `WeakOrderScoreRepresentation.lean` proves their exact score representation
  and exact `paperNormalizedMargin` transport; score profiles are proof
  scaffolding rather than a restriction of the paper-facing statement.
  The full-domain theorem `RTBTorder_domain` is a concrete statement over
  bundled nonempty reflexive finite profiles (allowing the two profiles to have
  different electorate sizes), the actual `B^p`, and the actual
  Ford/Zermelo-selected RTBT rule; its reusable caller-parameterized predecessor
  is `RTBTorder_domain_abstract`.  Among the counterexample results,
  `InvolveViolNLHF` is stated with profile-level witness predicates, while
  `InvolveViolRTBT` directly exposes actual strict-linear profiles and literal
  added top-/bottom-ranking voters, both Ford-domain certificates, a shared
  full-support reference, and the strict selected-RTBT inequalities.  Here a
  strict profile is the irreflexive strict-part representation of the paper's
  reflexive linear orders.  The headline `NLHFcomm` remains matrix-level, with
  the profile content in its companion theorem `NLHFcomm_profile_witness`.
  `FORMALIZATION_COVERAGE.md` and `PROOF_FAITHFULNESS.md` identify these scope
  choices explicitly.
- The `RTBTPM` proof uses a count-level interpolation and a proved
  connectivity argument. Connectivity of both endpoint profiles implies
  connectivity at every monotone intermediate stage. See
  `PROOF_FAITHFULNESS.md` for the proof-route comparison.

Reviewer entrypoints:

- `PaperFormalization/PaperStatements.lean` for the paper-facing theorem names.
- `PaperFormalization/AssumptionAudit.lean` for `#print axioms` on each
  paper-facing theorem.
- `PaperFormalization/PaperStatementShapeAudit.lean` for build-time checks that
  statement shapes do not drift.
- `PROOF_FAITHFULNESS.md` for the paper-proof to Lean-proof map.
- `ASSUMPTION_SUMMARY.md` for the human-readable axiom summary.

## Verification

The complete Docker artifact audit verified 57 public statements using Lean
and mathlib 4.30.0 with 32 GiB memory and eight CPUs. Every public statement depends only on `propext`,
`Classical.choice` and `Quot.sound`. The log and manifest record the commands,
source hashes and axiom dependencies.

- [Verification log](audits/verification-2026-11-03-comment-fix/lean-artifact-audit.log)
- [Verification manifest](audits/verification-2026-11-03-comment-fix/verification.json)

The log-mean ratio proof uses the integral representation
`logMean_eq_mul_integral_ratio_rpow`, pointwise comparison on `[0,1]` and
positivity of the second integral. The population-IPO proof uses the per-pair
bias–variance decomposition and the finite average over annotators and
ordered completion pairs.

`scripts/check_artifact.sh` builds the project, checks the paper-facing axiom
dependencies and statement shapes, and checks for admitted proofs. From the
repository root, run `make check-lean-docker` to repeat the isolated audit.
`../scripts/check_supplement.sh` performs packaging checks.
