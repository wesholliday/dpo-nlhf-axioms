# Assumption Summary

This file is a human-readable companion to
`PaperFormalization/AssumptionAudit.lean`.  The Lean file is authoritative:
it runs `#print axioms` on every paper-facing theorem in
`PaperStatements.lean`.

## Project-Specific Axioms

No project-specific axiom is expected in the paper-facing theorem graph. NLHF
existence follows by specializing Mathlib's proved
`Sion.exists_isSaddlePointOn` theorem to the finite lottery simplex. The
specialization proves all required KL continuity/convexity, affine-margin,
simplex convexity, and compactness facts in `NLHFExistence.lean`.

## Main Statement Dependencies

The audit permits Lean/mathlib's ordinary logical axioms such as `propext`,
`Classical.choice`, and `Quot.sound`.  Among project-specific declarations,
the dependency pattern is:

| Paper-facing declarations | Project-specific axiom dependency |
| --- | --- |
| `BTProp`, `BTProp_existence`, `BTProp_profile` | none |
| `DPOasRTBT`, `DPOasRTBT_profile`, selected-BT/add-voter DPO wrappers | none |
| `Anderson` (proved BT/Borda equivalence and RTBT transport) | none |
| `BIPOandPB`, `IPOandPB`, `IPOremark_population`, `IPOremark_population_pair` (unique minimizers of the defined objectives; population-loss reduction) | none |
| `MaxLottProp_limit` (abstract limiting-saddle form) | none |
| `PBPM`, `PBPM_strict` | none |
| `RTBTPM`, `RTBTPM_profile` | none |
| finite weak/linear-order score-representation and margin-transport wrappers | none |
| `PBPPI_positive`, `PBPPI_negative`, `PBPPI` (and `_strict` variants) | none |
| `InvolveViolRTBT_positive`, `InvolveViolRTBT_negative`, `InvolveViolRTBT` | none |
| `RTBTorder`, `RTBTorder_strict`, `RTBTorder_domain`, `RTBTorder_domain_abstract` | none |
| `nlhf-existence` wrappers | none |
| `nlhf-variational` (all lottery competitors) | none |
| `RTBT_extension`, `RTBT_extension_agrees`, `RTBT_extension_linear_domain`, `RTBT_extension_singleton` | none |
| `MaxLottProp` (statement about the actual selected NLHF lotteries) | none |
| `NLHFmono` (profile-level statement), `NLHFmono_profile_improvements`, `NLHFmono_margin_score_bundle`, and the other `NLHFmono_*` wrappers and converse witnesses | none |
| `InvolveViolNLHF` wrappers | none |
| `NLHFcomm`, `NLHFcomm_domain`, `NLHFcomm_profile_witness` | none |

Thus `selectedNLHF` and every paper-facing declaration that uses it are free
of project-specific axioms. `selectedNLHF` is constructed from the proved
Sion saddle theorem and the formalized saddle-to-fixed-point bridge.

Because `#print axioms` does not reveal a mathematical theorem passed as an
ordinary theorem-valued argument, the shape audit also fixes the public type
of `PaperStatements.Anderson`.  That type has no theorem-valued ranking
premise: `AndersonRanking.lean` proves the equivalence for the paper's
linear-order profile class from the formalized Ford displayed equations.

## Checking

Run the machine-checkable audit inside Docker, from the repository root:

```zsh
make check-lean-docker
```

The container runs `scripts/check_artifact.sh`, which builds the Lean project,
checks that every theorem in
`PaperStatements.lean` appears in `AssumptionAudit.lean`, rejects
`Lean.trustCompiler`, rejects unexpected project-specific axioms, rejects
`sorry`/`admit`, and verifies that no fixed-point compatibility interface or
Brouwer/Sperner backend is imported.
