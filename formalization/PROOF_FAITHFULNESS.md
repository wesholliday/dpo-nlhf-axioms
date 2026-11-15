# Proof Faithfulness Map

This note compares the Lean proofs with the proofs in the camera-ready
manuscript. The IPO and Borda-IPO propositions follow the authors' final
appendix text. `FORMALIZATION_COVERAGE.md` maps statements to declarations,
and `ASSUMPTION_SUMMARY.md` maps public declarations to axioms.

## External Theorem Used

- NLHF existence specializes Mathlib's proved
  `Sion.exists_isSaddlePointOn` theorem. The project proves every hypothesis
  of that specialization for the finite lottery simplex and carries the
  resulting closed saddle through the fixed-point and uniqueness arguments.

## Classification

This map distinguishes mathematical proof routes from routine formal
elaboration.  Making a suppressed domain check explicit, choosing a concrete
finite encoding, or splitting one calculation into several lemmas is not by
itself a faithfulness failure.  The classifications below are:

- **Faithful:** Lean follows the English mathematical argument, while making
  implicit finite, positivity, domain, or representation obligations explicit.
- **Corrective:** Lean must depart from a false step or must supply a material
  argument that the prose does not establish.
- **Valid alternative:** the English argument is sound, but Lean proves the
  same intermediate claim by a different route.
- **Independent discharge of a citation:** the paper states or restates a
  cited result without giving an internal proof, so there is no manuscript
  proof to mirror line by line.

The public theorem statements correspond to the statements in the paper.
Lean explicitly proves the extension of NLHF existence and optimality to
arbitrary normalized margins used in the English argument. Its direct
Ford-equation proof of the `RTBTPM` comparative static differs from the
paper's cited proof. The variational lemma follows the saddle-point argument
for all lotteries. The connectivity argument for `RTBTPM` uses the
connectivity assumptions at both endpoints.

## Main Proof Routes

| Paper proof | Faithfulness status | Lean declarations |
| --- | --- | --- |
| Proposition `BTProp` | **Independent discharge of a citation.** Lean proves the Ford/Zermelo finite closed-simplex/product-objective result: boundary exclusion, first-order equations, normalization, and uniqueness up to scale.  The export `PaperStatements.BTProp` is the unique combined certificate; `BTProp_existence` is the bare existence schema. | `FordZermeloBTTheorem_finite`, `exists_unique_BTProp_certificate`, `exists_unique_BTProp_certificate_strictCountProfile_of_ford_zermelo` |
| Proposition `DPOasRTBT` | **Faithful.** Follows the English normalization argument: positive BT maximizers form a ray, the DPO simplex constraint chooses the unique scalar, and the resulting lottery is exactly RTBT. | `DPOasRTBT_from_finite_ford_zermelo`, `DPOasRTBT_selectedBTOfFordZermelo`, profile wrappers |
| RTBT-extension footnote | **Faithful construction, with graph details supplied.** Proves the unique top component exists, applies Ford/Zermelo on that induced component, forms its RTBT lottery, and extends by zero. The singleton and original-domain agreement checks are included. | `RTBTExtension.lean`, `PaperStatements.RTBT_extension`, `RTBT_extension_agrees`, `RTBT_extension_linear_domain`, `RTBT_extension_singleton` |
| Proposition `Anderson` | **Independent discharge of a citation.** There is no proof in the camera-ready manuscript to mirror. Lean factors the cited likelihood argument through the already-proved Ford displayed equations, then follows the Anderson--Dandurova--Falk--Yeganova expected-wins argument on the exact paper-native profile class. Equal pair totals identify Borda with expected wins; positive powers preserve the order for every `β > 0` under the uniform reference. | `anderson_order_iff_of_unit_pair_displayed_equations`, `selectedBTOfFordZermelo_linearProfile_order_iff_borda`, `Anderson_RTBTRanking_linearOrderProfile`, `PaperStatements.Anderson` |
| Proposition `nlhf-existence` | **Independent discharge of a citation.** The paper calls the proposition an adaptation of Munos et al. but gives no proof. Lean proves the needed finite closed saddle from Mathlib's Sion minimax theorem: simplex compactness/convexity, boundary-safe KL continuity/convexity, and affine margin hypotheses are discharged. The saddle-to-softmax bridge then gives fixed-point existence; strict KL gives uniqueness, full support, closed-saddle equivalence, and the diagonal conclusion. | `sionClosedSaddleExistence`, `fixedPointExistence_of_closedSion`, `exists_unique_nlhfFixedPoint`, `exists_unique_nlhfRegularizedClosedSaddlePair`, `regularizedClosedSaddle_left_eq_right` |
| Proposition `MaxLottProp` | **Faithful, with harmless proof factoring.** Compactness supplies a convergent subsequence, and the limiting saddle-inequality argument gives maximality of every subsequence limit. Lean obtains the selected output's diagonal-saddle property from its fixed-point certificate rather than invoking `nlhf-existence` by name; this is an already-proved equivalence, not a different mathematical argument. | `MaxLottProp`, `exists_subseq_selectedNLHF_tendsto_maximalLottery`, `maximalLottery_of_selectedNLHF_subseq_tendsto`, `selectedNLHF_saddle_margin_bound` |
| Proposition `PBPM` | **Faithful.** Follows the denominator-rewrite proof for proportional Borda: improving `x` weakly decreases all relevant score gaps in the denominator.  The paper-facing statement uses the paper's partial-Borda score `B^p = Σ (c + ½ i + ½ n)` on weak-relation profiles (indifference and noncomparability distinguished), with the paper's improvement conditions (i)-(iii) verbatim; `PBPM_strict` is the strict-domination (`B^d`) variant. | `PBPM_from_score_differences`, `PBPM_weak_from_profile_improvement`, `partialBordaScoreP` |
| Proposition `RTBTPM` | **Valid alternative, with connectivity details supplied.** The English intermediate-connectivity assertion is correct under both endpoint hypotheses. Lean uses count-level interpolants and `FordStronglyConnected_of_between`; that cut argument also validates the English intermediate profiles. The English proof's Noothigattu comparative-static route has been verified against Definition 4.1, Theorem 4.2, and Appendix D of the cited paper; Lean proves the exact heterogeneous-pair-weight comparative static directly from Ford's displayed equations and iterates it over opponents. The remaining ratio and denominator argument is faithful. | `IsCountImprovementOf`, `FordStronglyConnected_of_between`, `fordBT_max_ratio_at_improved_of_onePair`, `fordBT_ratio_monotonicity_of_countImprovement`, `RTBTPM_count_selectedBTOfFordZermelo`, `RTBTPM_profile_weak_selectedBTOfFordZermelo`, `completeMarginBT_pair_ratio_monotonicity_of_displayed_equations`, `RTBTPM_onePair_selectedCompleteMarginBTOfFordZermelo` |
| Theorem `NLHFmono`, positive direction | **Faithful, with the implicit arbitrary-margin scope justified.** The finite-odds, logarithmic-mean, finite-comparison, and `K = 3` / `K = 1` arguments follow the appendix. Lean now derives the variational inequality for all lotteries from the diagonal closed saddle's first-player inequality, as in the English proof. It also proves the arbitrary-normalized-margin existence theorem needed to license that abstract stage. The profile-level reduction, improvement chaining, and exact weak-order score representation are formal elaborations of the prose. | `nlhf_variational_inequality_of_normalized_fixedPoint`, `selectedVariationalInequality_of_fixedPointSelection`, `sionClosedSaddleExistence`, `paperNormalizedMargin_improvement_of_weakProfileImprovement`, `nlhf_scoreProfile_improvement_monotone_of_tau_ge_one_eighth_selected`, `scoreWeakProfile_weakOrderScoreProfile`, `paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile`, `NLHFmono_paper_weak_order_improvements`, `NLHFmono_paper_linear_order_improvements` |
| Theorem `NLHFmono`, low-temperature converse | **Faithful.** Follows the three-candidate secant-response proof.  Lean formalizes the limiting sign argument and then realizes every converse witness as an actual pair of finite profiles differing at exactly one voter: reflexive and transitive profiles (`nlhfSharpAllWeakProfile3`) for the `3/8` clause, whose pair-normalized margins are exactly the paper's `nlhfSharpAllMargin3 (2/N)` and its one-pair improvement, and common-electorate linear-order profiles (`nlhfSharpLinearThresholdScore3`, `nlhfSharpLinearReplicated*Score3`) for the `1/8` clauses, carrying both the explicit voterwise (i)-(iii) relation and the exact singleton block-change equation. | `threeCandidateSecant_formula_from_fixed_points_fin3`, `nlhfSharpAll_lowTempSecantDropCertificate_fin3`, `nlhfSharpAllWeak_lowTempProfileDrop_fin3`, `nlhfSharpLinearThreshold_lowTempProfileDrop_fin3`, `selectedNLHF_linear_lowTempFiniteProfileBlockDrop_fin3`, `NLHFmono_weak_order_profiles`, `NLHFmono_linear_order_profiles` |
| Proposition `PBPPI` | **Faithful.** Follows the positive/negative involvement score-gap proof for proportional Borda, with the paper's `B^p` on weak-relation profiles: the added voter strictly ranks `x` first (resp. last), earning `x` exactly `m-1` (resp. `0`) additional credit.  Strict-reading variants survive as `PBPPI_positive_strict` / `PBPPI_negative_strict`. | `PBPPI_weak_from_added_top_profile`, `PBPNI_weak_from_added_bottom_profile` |
| Proposition `InvolveViolNLHF` | **Faithful.** Follows the concrete witness strategy: prove the fixed-point characterization for the displayed profile data and compare the selected probabilities.  The paper-facing statements quantify over the profile-level predicates `LinearOrderAddsTopMargins` / `LinearOrderAddsBottomMargins`, whose witnesses are actual linear-order profiles plus an added linear voter with `RanksTop` / `RanksBottom`; the four margin-realization lemmas identify the analytic witness matrices with those profiles, and pairwise-completeness certificates show the `\|V\|`-normalization agrees with the paper's `t`-normalization there. | `selectedNLHF_involvement_violation_profileRealization`, `nlhfLinearAddsTopRealization_witness`, `nlhfLinearAddsBottomRealization_witness` |
| Proposition `InvolveViolRTBT` | **Faithful.** Follows the concrete RTBT witness strategy using Ford/Zermelo-selected BT strengths, with the entire profile realization in the paper-facing aliases.  Each half existentially exposes an actual strict-linear profile, a literal `addVoterProfile` voter ranking the affected candidate first/last, Ford connectivity before and after addition, one shared full-support reference, and the corresponding strict inequality between the actual selected-RTBT probabilities.  `IsLinearPref` here is the irreflexive strict-part representation of the paper's reflexive linear orders, so `strictCount` is exactly the paper's `c_{x,y}`. | `InvolveViolRTBT_positive_profile_of_ford_zermelo`, `InvolveViolRTBT_negative_profile_of_ford_zermelo`, `InvolveViolRTBT_profile_of_ford_zermelo` |
| Proposition `RTBTorder` | **Faithful algebra, with omitted domain obligations supplied.** Follows the multiplicative-update commutativity calculation for proportional Borda and RTBT. The prose proves the update equation but does not explicitly discharge the two domain-closure conclusions in its definition of commutativity. Lean proves the complete property over bundled finite profiles in `RTBTorder_domain`; the closure facts use positivity/full-support preservation and the connectivity hypotheses already present for the two profiles. | `proportionalBordaWeakProfile_commutative`, `RTBTorder_profile_selectedBTOfFordZermelo`, `finiteProfileRTBTorder_commutativityOn`, `finiteProfileSelectedBTOfFordZermelo_eq_on_domain` |
| Proposition `NLHFcomm` | **Faithful.** Follows the concrete non-commutativity witness strategy: the two staged selected-NLHF updates are computed from fixed-point certificates and shown unequal.  The headline theorem is the matrix-level violation, and `NLHFcomm_profile_witness` realizes the witness matrices by the paper's actual linear-order profiles (three-voter cycle and one-voter `abc`), with linearity certificates, backing the paper's "even on profiles of linear orders". | `selectedNLHF_commutativity_violation`, `NLHFcomm_profile_witness`, `cycleProfile3_normalizedStrictMargin`, `linearProfile3_normalizedStrictMargin` |

## IPO and Borda-IPO Appendix Proofs

All three arguments follow the authors' final appendix text.

1. **`BIPOandPB`.** `bordaIPOLoss_eq_zero_iff_log_eq` uses nonnegativity of
   each square to obtain equality of adjusted log ratios.
   `bordaIPOLoss_eq_zero_iff` exponentiates those equalities and writes out
   the appendix's normalization calculation
   `1 = (π(x)/(ρ(x) exp(η B(x)))) Σ_z ρ(z) exp(η B(z))`.
   The reverse implication substitutes PB into the loss.
   `bordaIPOLoss_argmin` uses nonnegativity and this unique zero to prove
   the singleton argmin, including attainment. The public wrapper
   instantiates the generic score-vector argument at `partialBordaScoreP`.
2. **`IPOandPB`.** Lean proves the three identities cited in the English
   proof: reverse preference frequencies sum to one; a frequency row sums
   to `B^p_x/n` on linear orders; and the total Borda score is
   `nm(m-1)/2`. `offlineIPO_target_balance` uses them and
   `η = 1/(τmn)` to cancel the coefficients of the log ratios.
   `pairwiseIPOLoss_sub_eq_constant` expands the squares and collects the
   mixed terms by interchanging the ordered-pair indices.
   `offlineIPOObjective_sub_bordaIPOObjective` is exactly the English
   displayed loss-difference identity.
   `fullSupportArgminSet_eq_of_sub_eq_const` makes explicit why subtracting
   a lottery-independent constant preserves all comparisons of loss values;
   the proof then applies the first proposition.
3. **`IPOremark_population`.** `populationIPOLoss` is Azar et al.'s Eq. (16)
   in the paper's notation, with the expectation written as the uniform
   average over annotators and ordered pairs of distinct completions.
   `log_ratio_div_eq_sub` is the identity turning the log of the fraction
   into the difference of log-ratios; `avg_sq_sub_eq` is the bias--variance
   decomposition `E[(a-Z)^2] = (a-EZ)^2 + Var Z` for a finite average;
   `paperNormalizedCbar_eq_strictPrefCount_div_card` identifies the label's
   mean with `c̄_{x,y}` on linear orders. `pairPopulationIPOLoss_eq` is the
   displayed per-pair identity, `populationIPOLoss_eq` averages it over the
   `m(m-1)` pairs, and `fullSupportArgminSet_eq_of_eq_mul_add_const_on`
   transfers minimizers through the positive factor and constant, after which
   `IPOandPB` applies.

The intermediate generic lemmas are proof factoring, not extra assumptions
in the paper-facing statements. There is no convexity or differentiation
replacement for either English proof. The exact objective definitions,
full-support domain, and both public theorem types are checked in
`PaperStatementShapeAudit.lean`, as is the population-loss identity.

## Profile-level `NLHFmono` clauses

`PaperStatements.NLHFmono` (also exported as `NLHFmono_profile_improvements`)
states all three `NLHFmono` clauses over actual finite relation-valued profiles under the paper's
improvement conditions (i)-(iii), rather than over margin matrices under a
single uniform block improvement or over only profiles already presented by
scores.  Lemma `profile-margin-reduction` is
`paperNormalizedMargin_improvement_of_weakProfileImprovement`
(`WeakProfileMargin.lean`); the `3/8` converse is the paper's transitive
pair-block electorate (`nlhfSharpAllWeakProfile3`,
`NLHFWeakProfileMonotonicity.lean`), whose pair-normalized margins are exactly
`nlhfSharpAllMargin3 (2/N)` and its `2/(N(m+1))` one-pair improvement; the
`1/8` positive direction first represents every finite complete/transitive
Boolean relation by its exact lower-contour-cardinality score
(`WeakOrderScoreRepresentation.lean`), then applies the paper's decomposition
of a weak-order improvement into single-voter uniform block moves
(`nlhf_scoreProfile_improvement_monotone_of_tau_ge_one_eighth_selected`,
`NLHFScoreImprovementChaining.lean`), and its converse is a
common-electorate pair of linear-order profiles differing at exactly one
voter (`nlhfSharpLinearThresholdScore3`).  In fact,
`selectedNLHFPaperWeakOrderImprovementMonotonicity_iff_score` and its linear
counterpart prove that the relation-valued and score-valued predicates are
equivalent at every temperature, not only above the threshold.

## Detailed NLHFmono Proof Checklist

The proof of Theorem `NLHFmono` is the longest proof in the paper.  The
following checklist maps its appendix proof steps to Lean.

| Appendix proof step | Locations | Lean declarations | Notes |
| --- | --- | --- | --- |
| Margin-level NLHF definition and fixed-point equation `nlhf-fixed` | Paper: the camera-ready manuscript. Lean: `Core.lean:139`, `NLHFExistence.lean:1743`, `NLHFMonotonicityThreshold.lean:1620`. | `IsNLHFFixedPoint`, `selectedNLHF`, `nlhfBacksolvedReference_fixedPoint` | Lean works directly with normalized skew margin matrices, matching the appendix's margin reformulation. |
| Variational lemma `nlhf-variational` | Paper: camera-ready manuscript, Lemma `nlhf-variational`. Lean: `NLHFMonotonicityFinite.lean`, `PaperStatements.lean`. | `nlhf_variational_inequality_of_normalized_fixedPoint`, `selectedVariationalInequality_of_fixedPointSelection`, `PaperStatements.«nlhf-variational»` | **Faithful.** Projects closed-simplex first-player optimality from the diagonal saddle, cancels constant terms, and applies skew-symmetry. All lottery competitors are included; the downstream full-support interface is a restriction. |
| Finite-odds comparison `finite-odds` | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:4397`. | `finiteOdds_from_selected_NLHF` | Formalizes the KL/variational comparison and obtains the block probability-ratio inequality. |
| Logarithmic-mean identities `log-mean` | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:90`, `NLHFMonotonicityFinite.lean:109`, `NLHFMonotonicityFinite.lean:138`, `NLHFMonotonicityFinite.lean:546`. | `logMean_pos`, `logMean_log_identity`, `logMean_log_reverse_identity`, `logMean_arithmetic_le` | Lean proves the needed algebraic identities, positivity, and arithmetic-mean bound; the logarithmic-mean integral representation is used in this development. |
| Logarithmic-mean block bounds `log-mean-sums` | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:368`, `NLHFMonotonicityFinite.lean:435`, `NLHFMonotonicityFinite.lean:456`, `NLHFMonotonicityFinite.lean:858`. | `logMean_block_sum_le`, `logMean_eq_mul_integral_ratio_rpow`, `logMean_ratio_le_of_ratio`, `logMean_block_ratio_from_sum_and_ratio` | Both parts follow the paper's proof through the integral representation `log-mean`(2): superadditivity by the pointwise weighted AM-GM bound, and ratio monotonicity by display `TwoIntegrals` (`L(P,Q) = P ∫₀¹ (Q/P)^t dt`), the pointwise comparison `(Q/P)^t ≤ (s/r)^t` on `[0,1]`, and positivity of the second integral. |
| Block improvement change equation | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:21`, `NLHFMonotonicityFinite.lean:28`. | `blockImprovementChange`, `improvePairMargin_change_eq_blockImprovementChange_singleton` | Gives the exact margin delta used by both the finite comparison and the final finite-profile witness. |
| Exact finite-comparison algebra `block-improvement-identity` / `finite-comparison` | Paper: the camera-ready manuscript, the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:1351`, `NLHFMonotonicityFinite.lean:2160`, `NLHFMonotonicityFinite.lean:2678`. | `threeCandidateSecant_formula_from_fixed_points_fin3`, `finiteComparison_from_secant`, `finiteComparison_from_fixed_points_arithmetic` | The formal proof breaks the paper's algebra into smaller endpoint/system lemmas. |
| Arbitrary-profile positive direction `general-mono-positive` | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:4916`, `NLHFSelectedMonotonicity.lean:29`, `NLHFSelectedMonotonicity.lean:854`. | `nlhf_monotone_of_tau_ge_three_eighths_selected`, `selectedNLHF_largeTau_monotone`, `NLHFmono_all_profiles` | Uses the `K = 3` bound for normalized margins, yielding `τ ≥ 3/8`. The paper's preceding `nlhf-existence` proposition is profile-scoped; Lean separately proves the generic normalized-margin existence and optimality facts needed here. |
| Weak/linear positive direction `weak-linear-mono-positive` | Paper: the camera-ready manuscript. Lean: `NLHFSelectedMonotonicity.lean`, `NLHFScoreImprovementChaining.lean`, `WeakOrderScoreRepresentation.lean`. | `selectedNLHF_scoreProfile_block_monotone_one_eighth`, `nlhf_scoreProfile_improvement_monotone_of_tau_ge_one_eighth_selected`, `selectedNLHF_paperWeakOrderImprovementMonotone_of_tau_ge_one_eighth`, `selectedNLHF_paperLinearOrderImprovementMonotone_of_tau_ge_one_eighth` | Uses the score-profile `K = 1` bound, then transports it through an exact representation of every finite paper-style weak order; the final statements quantify over arbitrary complete/transitive Boolean relations, not a score-represented subclass. |
| Profile-to-margin reduction `profile-margin-reduction` | Paper: the camera-ready manuscript. Lean: `WeakProfileMargin.lean:332`, `NLHFWeakProfileMonotonicity.lean:648`. | `paperNormalizedMargin_improvement_of_weakProfileImprovement`, `NLHFmono_weak_profile_all` | Proves the paper's lemma at the pair-normalized margin `m̄_{x,y} = m_{x,y}/t_{x,y}`, including the cases where the denominator `t_{x,y}` changes (a new expressed comparison, or a `-1` contribution deleted); this is what upgrades the `3/8` clause from margin matrices to actual finite profiles. |
| Improvement chaining and weak-order representation for the `1/8` clauses | Paper: the camera-ready manuscript (proof of `weak-linear-mono-positive`). Lean: `NLHFScoreImprovementChaining.lean`, `NLHFScoreImprovementProfiles.lean`, `WeakOrderScoreRepresentation.lean`. | `nlhf_scoreProfile_improvement_monotone_of_tau_ge_one_eighth_selected`, `scoreWeakProfile_weakOrderScoreProfile`, `paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile`, `NLHFmono_paper_weak_order_improvements`, `NLHFmono_paper_linear_order_improvements` | Formalizes the one-position-at-a-time block chain and proves that every finite complete/transitive Boolean weak order is represented exactly by scores, so the `1/8` clauses retain the paper's full relation-valued quantifiers. |
| Profile realizations of the converse witnesses | Paper: the camera-ready manuscript, the camera-ready manuscript. Lean: `NLHFWeakProfileMonotonicity.lean:481`, `NLHFScoreImprovementProfiles.lean:236`. | `nlhfSharpAllWeak_lowTempProfileDrop_fin3`, `nlhfSharpLinearThreshold_lowTempProfileDrop_fin3` | Both converse witnesses are actual pairs of finite profiles over a common electorate that differ at exactly one voter and are related by the paper's conditions (i)-(iii); the `3/8` witness is additionally certified reflexive and transitive. |
| Margin continuity in the low-temperature converse | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:3320`, `NLHFMonotonicityFinite.lean:3531`, `NLHFMonotonicityFinite.lean:3645`. | `selectedNLHF_coordinate_tendsto_of_margin_tendsto`, `exists_nlhfSharpAll_secant_drop_of_small_sequence`, `exists_nlhfSharpLinear_secant_drop_of_small_sequence` | Formalizes the limiting sign argument by extracting a sufficiently small positive secant step. |
| Three-candidate secant-response formula | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:1351`, `NLHFMonotonicityFinite.lean:741`. | `threeCandidateSecant_formula_from_fixed_points_fin3`, `exists_threeCandidateSecant_drop_of_probability_tendsto_seq` | Matches the paper's Cramer's-rule computation and sign analysis. |
| Arbitrary-profile low-temperature witness `general-mono-sharp-elementary` | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean`, `NLHFSelectedMonotonicity.lean`. | `nlhfSharpAll_lowTempSecantDropCertificate_fin3`, `NLHFmono_fin3`, `selectedNLHF_fin3_allProfileThreshold` | Produces the three-candidate counterexample for `τ < 3/8`. |
| Linear-order low-temperature witness `linear-mono-sharp` | Paper: the camera-ready manuscript. Lean: `NLHFMonotonicityFinite.lean:3905`, `NLHFMonotonicityFinite.lean:3980`, `NLHFSelectedMonotonicity.lean:571`. | `nlhfSharpLinear_lowTempWeightedProfileDrop_fin3`, `nlhfSharpLinear_lowTempFiniteProfileDrop_fin3`, `selectedNLHF_linear_lowTempFiniteProfileBlockDrop_fin3` | Lean first follows the rational-weighted proof, then clears denominators to actual finite linear-order profiles and proves the exact singleton block-change equality. |
| Bundling the iff statements | Paper: the camera-ready manuscript, the camera-ready manuscript. Lean: `PaperStatements.lean:398`, `PaperStatements.lean:522`, `PaperStatementShapeAudit.lean:228`, `PaperStatementShapeAudit.lean:324`. | `PaperStatements.NLHFmono` (profile level; alias `NLHFmono_profile_improvements`), `PaperStatements.NLHFmono_margin_score_bundle` (analytic scaffolding), `PaperStatementShapeAudit.lean` | The shape audit ensures that the theorem named `NLHFmono` is the actual finite-profile iff statement under the paper's (i)-(iii) improvement relation, and that the weighted/single-block auxiliary versions stay apart as `NLHFmono_margin_score_bundle`. |

## Material Proof-Route Deviations

### Valid connectivity argument with details supplied

#### `RTBTPM`: connectivity of intermediate profiles

The English proof says that performing all additions before all removals keeps
the strict-count graph strongly connected at every stage. This is correct
because both endpoint profiles are in the domain. If a voter already has
`(y,x)`, adding `(x,y)` creates an indifference and can delete the strict edge
`y → x`; thus a proof based only on retaining every original edge would fail.
However, every monotone intermediate stage retains the original `x`-out-edges,
the final `x`-in-edges, and all non-`x` edges. Endpoint connectivity suffices
by Ford's partition criterion.

Lean instead changes the two counts involving `x` and one opponent at a time
with `partialCountImprovement`.  It proves every interpolant connected using
`FordStronglyConnected_of_between`, derived from Ford's partition criterion:
the interpolant retains the old `x`-out counts, the final `x`-in counts, and all
non-`x` counts.  Endpoint connectivity then implies interpolant connectivity.
The same argument validates the English intermediate profiles. This supplies
details for a sound English assertion; it does not repair a false step.

### Scope for arbitrary normalized margins

Proposition `nlhf-existence` is stated for profile-induced objectives. The
abstract-margin formulation in Definition `def:nlhf-margin` uses existence,
uniqueness and optimality for an arbitrary real skew normalized margin
function. Lean proves this scope explicitly.

`sionClosedSaddleExistence` and its fixed-point and uniqueness consequences
hold for every finite normalized margin matrix. Set
`c̄(x,y) = (1 + m(x,y))/2`. The resulting matrix takes values in `[0,1]` and
satisfies `c̄(x,y) + c̄(y,x) = 1`, the properties used in the finite regularized
game. The `nlhf-existence-cbar` wrapper covers this substitution and supplies
the existence, uniqueness and saddle conclusions used by the variational
lemma.

### English proof is sound but Lean uses a different route

| Result and step | English route | Current Lean route | Proof comparison |
| --- | --- | --- | --- |
| `RTBTPM`: one-comparison BT ratio comparative static | Applies Noothigattu et al., Theorem 4.2, to each added `(x,y)` or removed `(y,x)` comparison. | Proves the exact count comparative static directly from Ford's displayed equations by a max-ratio argument (`fordBT_max_ratio_at_improved_of_onePair`), then iterates it. | Valid alternative. The citation has been verified against the original paper: fitted log-strength differences give the required strength ratios after exponentiating; arbitrary pair counts are permitted. See `CITATION_AND_PROVENANCE.md`. |
| `NLHFmono`: Lemma `nlhf-variational` | Projects first-player optimality over the whole lottery simplex from the diagonal saddle supplied by `nlhf-existence`. | Uses `regularizedClosedSaddle_of_fixedPoint`'s first-player inequality, cancels the fixed opponent's KL term, and uses skew-symmetry. | Faithful. The strengthened public result `PaperStatements.«nlhf-variational»` accepts every `IsLottery` competitor. The full-support downstream interface is only a restriction of this theorem. |

The ratio-monotonicity part of Lemma `log-mean-sums` follows the integral
comparison through `logMean_eq_mul_integral_ratio_rpow` and
`logMean_ratio_le_of_ratio`. The fixed-point-to-saddle bridge in `MaxLottProp`
factors the proof into a compactness argument, a KL bound and the limiting
margin comparison used in the appendix.

## Cited Results With No Manuscript Proof to Mirror

- `BTProp` is a restatement of Ford's result. Lean supplies a complete finite
  proof of the cited theorem.
- `Anderson` is cited and restated in the camera-ready manuscript, not proved there. Lean reuses
  the already-formalized Ford displayed equations and then proves the cited
  expected-wins/Borda order argument. Replaying likelihood differentiation
  would duplicate the stationarity work already used to obtain those equations
  and would not improve the paper-facing result.
- `nlhf-existence` is described as an adaptation of Munos et al., Proposition
  1, without an internal proof. Lean's Sion/strict-KL proof therefore discharges
  a citation rather than departing from a manuscript proof.
