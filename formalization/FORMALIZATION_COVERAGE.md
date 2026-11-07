# Formalization Coverage

This note maps the thirteen main-result families in the camera-ready
manuscript to the Lean project. The partial-Borda score includes half credit
for unexpressed comparisons. The IPO and Borda-IPO minimization propositions
follow the authors' final appendix text. The RTBT-extension footnote and the
all-lottery variational lemma have additional public wrappers below.
The tables specify the scope of each formalized statement and proof.

For a proof-route comparison with the English arguments,
see `PROOF_FAITHFULNESS.md`.  For a human-readable summary of project-specific
axiom dependencies, see `ASSUMPTION_SUMMARY.md`.

The submission-facing build has no project-specific mathematical axiom. NLHF
existence is obtained by a proved specialization of Mathlib's Sion minimax
theorem to the finite lottery simplex. The paper-specific Anderson proposition
is also formalized: its
Bradley--Terry/Borda equivalence is proved from Ford's displayed equations on
finite linear-order profiles rather than represented by a theorem-valued
premise.

The reviewer-facing Lean entrypoint is `PaperFormalization/PaperStatements.lean`.
It collects thin theorem aliases named after the paper labels.  The companion
file `PaperFormalization/AssumptionAudit.lean` runs `#print axioms` on those
aliases.  For a shorter reviewer path through the artifact, see
`FORMALIZATION_INDEX.md`.

## Main Text Statements

| Paper statement | Lean coverage | Status |
| --- | --- | --- |
| Proposition `BTProp` | `PaperStatements.BTProp` (unique combined certificate at the count level), `PaperStatements.BTProp_existence` (bare Ford existence schema), `PaperStatements.BTProp_profile`; proof declarations `FordZermeloBTTheorem_finite`, `exists_unique_BTProp_certificate`, `exists_unique_BTProp_certificate_strictCountProfile_of_ford_zermelo` | Formalized from the finite closed simplex/product objective, boundary exclusion, first-order stationarity, displayed BT equations, normalization, and uniqueness-up-to-scale arguments.  `BTProp` states, for every strongly connected finite Ford count matrix, the paper's full proposition: a unique full-support `u` satisfying Ford's displayed equations with `w_{x,y} = c_{x,y} + c_{y,x}`, whose positive multiples are exactly the maximizers of `L_𝐑`; `BTProp_existence` is only the existence schema `FordZermeloBTTheorem`.  The profile alias states the unique normalized Bradley-Terry certificate for strict counts of a finite strongly connected profile. |
| Proposition `DPOasRTBT` | `PaperStatements.DPOasRTBT`, `PaperStatements.DPOasRTBT_profile`, `PaperStatements.DPOasRTBT_profile_selectedBT`; proof declarations `DPOasRTBT_from_finite_ford_zermelo`, `exists_DPOasRTBT_strictCountProfile`, selected-BT and add-voter strict-count wrappers | Formalized from the Ford/Zermelo BT certificate.  The positive-ray interface follows from that finite theorem, and the profile aliases state both the certificate-existential singleton DPO argmax result and the selected-BT singleton matching the paper definition of RTBT. |
| Proposition `Anderson` | `PaperStatements.Anderson`; proof declarations in `AndersonRanking.lean`, especially `anderson_order_iff_of_unit_pair_displayed_equations`, `selectedBTOfFordZermelo_linearProfile_order_iff_borda`, `Anderson_RTBTRanking_linearOrderProfile`; RTBT transport `RTBTFromStrength_order_iff_of_equal_reference` | Formalized unconditionally on the paper's native finite reflexive linear-order profiles.  Both the Ford/Zermelo counts and strict-domination Borda score are computed from `strictPart R`; Ford strong connectivity supplies the selected positive BT vector, and uniform-reference RTBT preserves its order for every `β > 0`.  The proof follows Anderson--Dandurova--Falk--Yeganova's expected-wins argument on pp. 360--361, after the already-proved Ford equations, so neither their theorem nor an optimization/calculus premise is assumed. |
| Proposition `nlhf-existence` | `PaperStatements.«nlhf-existence»`, `PaperStatements.«nlhf-existence-diagonal»`, `PaperStatements.«nlhf-existence-fixed-point»`, `PaperStatements.«nlhf-existence-cbar»`, `PaperStatements.«nlhf-existence-weak-profile»`; proof declarations `sionClosedSaddleExistence`, `exists_unique_nlhfRegularizedClosedSaddlePair`, `regularizedClosedSaddle_left_eq_right`, `exists_unique_nlhfFixedPoint`, `selectedNLHF` wrappers, `NLHFGammaForm.lean`, `WeakProfileNLHF.lean` | Formalized from Mathlib's proved `Sion.exists_isSaddlePointOn`. Lean proves convexity and compactness of the finite lottery simplex, boundary continuity and convexity of KL via `InformationTheory.klFun`, the affine/continuous margin hypotheses, the closed saddle, fixed-point existence and uniqueness, and the paper's diagonal conclusion `πτ = π'τ`. The paper's own `Γ_τ` objective in `c̄` form is `nlhfGammaValue` at `cbarOfMargin M`, and Remark `NLHFreformulated` is `gammaClosedSaddle_iff_regularizedClosedSaddle`; `«nlhf-existence-weak-profile»` states the result over an actual profile with the paper's pair-specific `c̄_{x,y} = (c + ½ i)/t_{x,y}` (`paperNormalizedCbar`). |
| Proposition `MaxLottProp` | `PaperStatements.MaxLottProp`, `PaperStatements.MaxLottProp_limit`; proof declarations in `SelectedMaxLottLimit.lean` | Formalized in the paper's two-conjunct form for the actual selected NLHF lotteries: for positive `τ_n -> 0`, a convergent subsequence exists (with maximal-lottery limit), and the limit of every convergent subsequence is a maximal lottery.  The saddle hypothesis is discharged for `selectedNLHF`, and the subsequence comes from proved compactness of the lottery simplex.  `MaxLottProp_limit` gives the reusable abstract limit implication. |
| Proposition `PBPM` | `PaperStatements.PBPM`, `PaperStatements.PBPM_strict`; proof declarations `PBPM_weak_from_profile_improvement'`, `PBPM_from_score_differences'` | Formalized for the paper's partial-Borda score `B^p = Σ (c + ½ i + ½ n)` on weak-relation profiles (indifference and noncomparability distinguished), under the paper's improvement conditions (i)-(iii).  The strict-domination score `B^d` variant is `PBPM_strict`, with its score named `strictDominationBordaScore`.  The reference lottery ranges over the paper's full domain `Δ`: the paper's trivial `ρ(x) = 0` case is `proportionalBorda_eq_zero_of_ref_zero`, so no `0 < ρ x` hypothesis appears. |
| Proposition `RTBTPM` | `PaperStatements.RTBTPM`, `PaperStatements.RTBTPM_profile`; proof declarations `IsCountImprovementOf`, `FordStronglyConnected_of_between`, `fordBT_max_ratio_at_improved_of_onePair`, `fordBT_ratio_monotonicity_of_countImprovement`, `RTBTPM_count_selectedBTOfFordZermelo`, `isCountImprovementOf_strictCount_strictPart_of_weakProfileImprovement`, `RTBTPM_profile_weak_selectedBTOfFordZermelo` (all in `RTBTCountMonotonicity.lean`); the one-pair margin-level lemmas `completeMarginBT_pair_ratio_monotonicity_of_displayed_equations`, `RTBTPM_onePair_selectedCompleteMarginBTOfFordZermelo` are in `RTBTPairMonotonicity.lean` | Formalized **unconditionally**, at the Ford count-matrix level at which the paper defines `RTBT_β` (heterogeneous pair weights `w_{x,y} = c_{x,y} + c_{y,x}`, and pairs with `w_{x,y} = 0` allowed).  Both `(c,ρ)` and `(c⁺,ρ)` are required to lie in the paper's domain `𝒟` (positive-count graph strongly connected, `ρ` of full support) — exactly the quantification of the paper's probabilistic-monotonicity axiom — and the Bradley--Terry strengths are the Ford/Zermelo *selected* solutions, so there is no selector hypothesis and existence is supplied by `BTProp`.  The count-level improvement relation `IsCountImprovementOf` is the paper's conditions (i)-(iii) read through strict-win counts.  The Noothigattu-style comparative static is proved directly: `fordBT_max_ratio_at_improved_of_onePair` gives the one-pair max-ratio argument for heterogeneous weights, and `fordBT_ratio_monotonicity_of_countImprovement` iterates it over opponents.  `FordStronglyConnected_of_between` keeps every intermediate stage inside `𝒟` via Ford's partition formulation.  `RTBTPM_profile` transports the result to weak-relation profiles under `IsWeakProfileImprovement` via `strictPart`. |
| Theorem `NLHFmono` | `PaperStatements.NLHFmono`, `PaperStatements.NLHFmono_profile_improvements`, `PaperStatements.NLHFmono_profile_all`, `PaperStatements.NLHFmono_margin_score_bundle`, `PaperStatements.NLHFmono_finite_weak_order_score_representation`, `PaperStatements.NLHFmono_finite_linear_order_score_representation`, and the `NLHFmono_actual_*` witnesses; proof declarations `NLHFmono_all_profiles`, `NLHFmono_weak_profile_all`, `NLHFmono_paper_weak_order_improvements`, `NLHFmono_paper_linear_order_improvements`, `selectedNLHFPaperWeakOrderImprovementMonotonicity_iff_score`, `selectedNLHFPaperLinearOrderImprovementMonotonicity_iff_score`, `scoreWeakProfile_weakOrderScoreProfile`, `paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile`, `nlhf_scoreProfile_improvement_monotone_of_tau_ge_one_eighth_selected`, `paperNormalizedMargin_improvement_of_weakProfileImprovement`, `nlhfSharpAllWeak_lowTempProfileDrop_fin3`, `nlhfSharpLinearThreshold_lowTempProfileDrop_fin3` | Formalized as paper-facing iff wrappers at two levels.  `NLHFmono` is the **exact profile-level form** (also exported under its former name `NLHFmono_profile_improvements`); `NLHFmono_margin_score_bundle` is the analytic margin/score-profile bundle, whose `1/8` clauses are single-block score-profile scaffolding rather than the paper's clause.  The `3/8` clause of `NLHFmono` ranges over arbitrary reflexive-relation profiles and its `1/8` clauses range directly over arbitrary finite complete/transitive Boolean weak orders and their antisymmetric linear-order specialization, all under the paper's voterwise improvement conditions (i)-(iii) and using `paperNormalizedMargin`.  `WeakOrderScoreRepresentation.lean` proves that every such weak order is represented exactly by the canonical lower-contour-cardinality score, preserves the Boolean relation and normalized margin, and is tie-free under antisymmetry; the paper-native and score-profile monotonicity predicates are equivalent at every temperature, so the analytic proof is transported without narrowing the paper's quantifiers.  Every converse direction has a genuine finite-profile witness.  Weighted and score-profile clauses are internal proof scaffolding. |
| Proposition `PBPPI` | `PaperStatements.PBPPI`, `PaperStatements.PBPPI_positive`, `PaperStatements.PBPPI_negative` (plus `_strict` variants); proof declarations `PBPPI_weak_from_added_top_profile'`, `PBPNI_weak_from_added_bottom_profile'` | Formalized for the explicit positive and negative involvement profile operations with the paper's `B^p` on weak-relation profiles (added voter strictly first/last), both separately and as the paper's bundled `resp.` statement.  As for `PBPM`, `ρ` ranges over all of `Δ` (the `ρ(x) = 0` case is `proportionalBorda_eq_zero_of_ref_zero`). |
| Proposition `InvolveViolNLHF` | `PaperStatements.InvolveViolNLHF`, `PaperStatements.InvolveViolNLHF_positive`, `PaperStatements.InvolveViolNLHF_negative`; proof declarations `selectedNLHF_involvement_violation_profileRealization`, `selectedNLHF_involvement_violation` | Formalized with profile-level witness predicates (`LinearOrderAddsTopMargins` / `LinearOrderAddsBottomMargins`): the margin matrices are proved equal to the normalized margins of actual four-candidate linear-order profiles and of those profiles plus one added linear voter with `RanksTop` / `RanksBottom`, using the selected NLHF rule obtained from the proved Sion specialization. |
| Proposition `InvolveViolRTBT` | `PaperStatements.InvolveViolRTBT`, `PaperStatements.InvolveViolRTBT_positive`, `PaperStatements.InvolveViolRTBT_negative`; proof declarations `InvolveViolRTBT_positive_profile_of_ford_zermelo`, `InvolveViolRTBT_negative_profile_of_ford_zermelo`, `InvolveViolRTBT_profile_of_ford_zermelo` (`RTBTInvolvement.lean`) | Formalized directly over actual three-candidate strict-linear profiles and literal `addVoterProfile` extensions.  Each public half exposes the original profile, the added voter with `RanksTop` / `RanksBottom`, both Ford-domain connectivity certificates, one shared full-support reference lottery, and the strict inequality between the actual Ford/Zermelo-selected RTBT probabilities before and after the addition.  In this strict-profile convention, `IsLinearPref` represents the irreflexive strict part of the paper's reflexive linear order, and `strictCount R` is the paper's `c_{x,y}`. |
| Proposition `RTBTorder` | `PaperStatements.RTBTorder`, `PaperStatements.RTBTorder_strict`, `PaperStatements.RTBTorder_domain`, `PaperStatements.RTBTorder_domain_abstract`; proof declarations `RTBTorder_profile_selectedBTOfFordZermelo`, `proportionalBordaWeakProfile_commutative`, `finiteProfileRTBTorder_commutativityOn`, `finiteProfileSelectedBTOfFordZermelo_eq_on_domain` (`CommutativityDomain.lean`) | `RTBTorder` gives the equation-level profile result for proportional Borda (with the paper's `B^p`) and Ford/Zermelo-selected RTBT over strict-preference counts.  `RTBTorder_domain` is the concrete full-domain theorem for the paper's complete commutativity definition, including both closure clauses: `FiniteProfile` bundles the electorate size, so the quantified profiles may have different electorate sizes; both domains require nonempty reflexive weak-relation profiles; the PB rule uses the actual `B^p` on all `ρ ∈ Δ`; and the RTBT rule uses actual strict counts, Ford connectivity, selected Ford/Zermelo strengths, and `ρ ∈ Δ°`.  `RTBTorder_domain_abstract` is the reusable caller-parameterized algebraic theorem. |
| Proposition `NLHFcomm` | `PaperStatements.NLHFcomm`, `PaperStatements.NLHFcomm_domain`, `PaperStatements.NLHFcomm_profile_witness`; proof declarations `selectedNLHF_commutativity_violation`, `selectedNLHF_profile_commutativity_violation`, `violatesCommutativityOn_of_violatesCommutativity_selectedNLHF` | Formalized for the selected NLHF rule on concrete three-candidate cycle/linear witnesses; the realization lemmas `cycleProfile3_normalizedStrictMargin` / `linearProfile3_normalizedStrictMargin` and `cycleProfile3_paperNormalizedMargin` / `linearProfile3_paperNormalizedMargin` prove these are the margin matrices of the paper's linear-order example profiles under both the `|V|`-normalization and the paper's pair normalization `m̄`, with strict-linear-order certificates for every voter.  `NLHFcomm_domain` upgrades the violation to the paper's full commutativity definition: `NLHF_τ` maps `Δ°` into `Δ°` (`selectedNLHF_preserves_fullSupport`), so the domain-closure clauses hold automatically and the equation failure refutes the paper's property itself. |

## IPO and Borda-IPO

| Appendix assertion | Public wrapper | Coverage |
| --- | --- | --- |
| Proposition `BIPOandPB` | `PaperStatements.BIPOandPB` | `BordaIPO.lean` proves that `fullSupportArgminSet (bordaIPOObjective η R ρ)` is exactly the singleton containing PB, and that its loss is zero. It uses the actual `partialBordaScoreP R`, permits arbitrary finite relation-valued profiles, and assumes a full-support reference and `η > 0`. The generic score-vector proof also establishes `bordaIPOLoss_eq_zero_iff`. |
| First claim of Remark `IPOremark` (population loss has the same minimizers as `IPO_τ`), justified in the opening paragraph of Appendix `IPOApp` | `PaperStatements.IPOremark_population`, `PaperStatements.IPOremark_population_pair` | `OfflineIPO.lean` defines `populationIPOLoss` as the paper writes it, a log of a fraction minus the scaled `0/1` annotator label, with the expectation taken as the uniform average over annotators and over ordered pairs of distinct completions. `pairPopulationIPOLoss_eq` is the displayed per-pair identity (bias--variance decomposition `avg_sq_sub_eq`, label mean `c̄_{x,y}`, log identity `log_ratio_div_eq_sub`); `populationIPOLoss_eq` averages it; `populationIPOLoss_argmin_eq_offline` and `populationIPOLoss_argmin` give the equal minimizer sets and the PB singleton. Hypotheses: linear-order profile, nonempty electorate, at least two candidates, `τ > 0`, full-support `ρ`. |
| The following unlabelled IPO proposition | `PaperStatements.IPOandPB` | `OfflineIPO.lean` proves the singleton argmin for `offlineIPOObjective τ R ρ` on finite nonempty linear-order profiles and full-support references, with `τ > 0` and PB parameter `1/(τmn)`. The objective uses the actual `paperNormalizedCbar`. `offlineIPOObjective_sub_bordaIPOObjective` proves the exact displayed constant-difference identity from the English proof. |

The singleton argmin statements include feasibility, attainment, and
uniqueness over precisely the full-support lottery domain. The shape audit
fixes both literal ordered-pair objectives and that domain. No count or
frequency identity is assumed: Lean derives them from the paper's native
reflexive linear-order profiles. The first proposition in fact holds for
all finite Boolean relations, so imposing the paper's reflexivity and
nonempty-electorate conventions requires no extra argument.

These results concern the objectives defined in Remark `IPOremark`. The
remark's opening claim, that the population IPO loss of Azar et al.
(Eq. (16)) has the same minimizers as the deterministic squared-frequency
objective, is formalized as `IPOremark_population`, following the paragraph
that opens Appendix `IPOApp` in the camera-ready manuscript.

## Camera-Ready Extension and Variational Lemma

| Paper assertion | Public wrappers | Coverage |
| --- | --- | --- |
| RTBT-extension footnote | `RTBT_extension`, `RTBT_extension_agrees`, `RTBT_extension_linear_domain`, `RTBT_extension_singleton` | `RTBTExtension.lean` proves the finite graph has a unique top strongly connected component when each distinct pair has a positive count in some direction. It applies the proved Ford/Zermelo certificate to the induced component, forms RTBT there and extends by zero. The extended rule agrees with original RTBT on every strongly connected graph, even when some pairs are unobserved. Linear-order profiles are included; a singleton top component yields a point mass. |
| Lemma `nlhf-variational` | `PaperStatements.«nlhf-variational»` | Maximization over all lotteries, including boundary points, by projecting the diagonal closed saddle's first-player inequality and cancelling the fixed opponent's KL term, exactly as in the English proof. Internal downstream interfaces may request only full-support competitors, but are restrictions of this proved all-lottery result. |

The extension formalization does not assert new monotonicity or other axioms
on the enlarged domain, or an extension of the DPO equivalence beyond its
original strong-connectivity hypotheses.

## Appendix Proof Components

**Count-level engine and connectivity argument for `RTBTPM`.**  The
English proof of Proposition `RTBTPM` decomposes the move from `𝐑` to `𝐑⁺`
into single-comparison additions followed by single-comparison removals, and
asserts parenthetically that "the graph associated with the profile at each
stage remains strongly connected". That assertion is correct under the
theorem's connectivity assumptions on both endpoints. Although adding a weak
comparison can delete a strict edge by creating indifference, every monotone
intermediate stage retains the original outgoing edges of `x`, the final
incoming edges of `x`, and all edges not involving `x`. The cut argument in
`FordStronglyConnected_of_between`
(`RTBTCountMonotonicity.lean`) shows that any matrix `d` whose `x`-out-edges
dominate those of `c`, whose `x`-in-edges dominate those of `c⁺`, and which
dominates both off `x`, is strongly connected as soon as `c` and `c⁺` are.  The
induction in `fordBT_ratio_monotonicity_of_countImprovement` runs over the
explicit interpolants `partialCountImprovement c c' x S`, each of which is of
that form, so every stage of the Lean argument is certified to lie in the
paper's domain `𝒟`.  The relation-level statement is connected to the
count-level statement by
`isCountImprovementOf_strictCount_strictPart_of_weakProfileImprovement`.

**Profile-level form of `NLHFmono`.**  All three clauses are
available over *actual finite profiles* related by the paper's improvement
conditions (i)-(iii), via `PaperStatements.NLHFmono` (also exported as
`NLHFmono_profile_improvements`; with `PaperStatements.NLHFmono_profile_all`
as the `3/8` clause on its own):

* `SelectedNLHFWeakProfileAllMonotonicity τ ↔ 3/8 ≤ τ` quantifies over all
  finite profiles of reflexive binary relations `V → α → α → Bool`, read
  through the paper's pair-normalized margin
  `paperNormalizedMargin` (`m̄_{x,y} = m_{x,y}/t_{x,y}`, with `m̄ = 0` when
  `t_{x,y} = 0`).  The right-to-left direction is Lemma
  `profile-margin-reduction`
  (`paperNormalizedMargin_improvement_of_weakProfileImprovement`), and the
  left-to-right direction is the paper's transitive pair-block electorate
  (`nlhfSharpAllWeakProfile3`), realized as an actual pair of finite
  reflexive transitive profiles differing at one voter
  (`PaperStatements.NLHFmono_actual_transitive_profile_converse_witness`).
* `SelectedNLHFPaperWeakOrderImprovementMonotonicity τ ↔ 1/8 ≤ τ` and its
  linear-order specialization quantify directly over arbitrary finite
  complete/transitive Boolean weak orders (and antisymmetric linear orders)
  related by conditions (i)-(iii).  `WeakOrderScoreRepresentation.lean`
  constructs the canonical score `|{z | R(a,z)}|`, proves
  `scoreWeakProfile score = R`, preserves `paperNormalizedMargin` exactly,
  and proves injectivity under antisymmetry.  The existing score-profile
  chaining argument therefore applies to the paper's full domain; the
  converse uses a common-electorate pair of linear-order profiles differing
  at one voter
  (`PaperStatements.NLHFmono_actual_linear_profile_voterwise_converse_witness`).

The finite-secant and logarithmic-mean development used for `NLHFmono` is
mainly in `NLHFMonotonicityThreshold.lean`, `NLHFMonotonicityFinite.lean`, and
`NLHFExistence.lean`.

| Paper label | Lean declarations |
| --- | --- |
| `nlhf-variational` | `nlhf_variational_inequality_of_normalized_fixedPoint`, `selectedVariationalInequality_of_fixedPointSelection` |
| `finite-odds` | `finiteOdds_from_selected_NLHF` |
| `log-mean` | `logMean_*` lemmas in `NLHFMonotonicityFinite.lean` |
| `log-mean-sums` | `logMean_block_sum_le`, `logMean_eq_mul_integral_ratio_rpow`, `logMean_ratio_le_of_ratio`, `logMean_block_ratio_from_sum_and_ratio` |
| `block-improvement-identity` | `threeCandidateSecant_formula_from_fixed_points_fin3`, `finiteComparison_from_*` |
| `finite-comparison` | `finiteComparison_from_secant`, `finiteComparison_from_fixed_points_arithmetic` and wrappers |
| `profile-margin-reduction` | `paperNormalizedMargin_other_eq_of_weakProfileImprovement`, `paperNormalizedMargin_improvement_of_weakProfileImprovement` (`WeakProfileMargin.lean`) |
| `general-mono-positive` | `nlhf_monotone_of_tau_ge_three_eighths_selected`, `selectedNLHF_largeTau_monotone`, `NLHFmono_weak_profile_all` (profile-level `⇐`), strict-KL and closed-Sion interfaces |
| `swo-bound` | `paperNormalizedMargin_coordinate_abs_le_one_of_weakOrderProfile`; score-level engine `scoreProfileMargin_coordinate_abs_le_one` and exact transport via `paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile` |
| `weak-linear-mono-positive` | `selectedNLHF_scoreProfile_block_monotone_one_eighth`, `nlhf_scoreProfile_improvement_monotone_of_tau_ge_one_eighth_selected` (score-level chaining), then `selectedNLHF_paperWeakOrderImprovementMonotone_of_tau_ge_one_eighth` and its linear specialization for arbitrary paper-style relations (`WeakOrderScoreRepresentation.lean`) |
| `general-mono-sharp-elementary` | `nlhfSharpAll_lowTempSecantDropCertificate_fin3`; profile realization `nlhfSharpAllWeakProfile3`, `nlhfSharpAllWeak_lowTempProfileDrop_fin3` (`NLHFWeakProfileMonotonicity.lean`) |
| `linear-mono-sharp` | `selectedNLHF_linear_lowTempWeightedProfileDrop_fin3`, `selectedNLHF_linear_lowTempFiniteProfileDrop_fin3`, `selectedNLHF_linear_lowTempFiniteProfileBlockDrop_fin3`; common-electorate profile realization `nlhfSharpLinearThresholdScore3`, `nlhfSharpLinearThreshold_lowTempProfileDrop_fin3` (`NLHFScoreImprovementProfiles.lean`); strict-KL and closed-Sion interfaces |
| `Z-decreasing` and `p-comparison` | `Z_strictly_decreasing_from_lower_fixed_selection_fin3`, `nlhfP_comparison`, `nlhfP_strictly_increasing` |

## Project-Specific Axioms

- There are no project-specific axioms in the active theorem graph.
- NLHF existence uses Mathlib's proved Sion minimax theorem through the local
  theorem `sionClosedSaddleExistence`.
- The paper-specific Anderson et al. BT-vs-Borda ranking equivalence is proved
  in `AndersonRanking.lean` and has no project-specific axiom dependency.
- All other main-text propositions listed above are represented by Lean
  declarations in the active `PaperFormalization` import graph.
