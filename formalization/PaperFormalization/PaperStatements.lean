import PaperFormalization.AndersonRanking
import PaperFormalization.OfflineIPO
import PaperFormalization.Commutativity
import PaperFormalization.CommutativityDomain
import PaperFormalization.NLHFGammaForm
import PaperFormalization.WeakProfileNLHF
import PaperFormalization.FordZermelo
import PaperFormalization.MaximalLotteryLimit
import PaperFormalization.SelectedMaxLottLimit
import PaperFormalization.NLHFExistence
import PaperFormalization.NLHFSelectedCommutativity
import PaperFormalization.ProfileNLHFCommutativity
import PaperFormalization.NLHFSelectedInvolvement
import PaperFormalization.NLHFSelectedMonotonicity
import PaperFormalization.NLHFWeakProfileMonotonicity
import PaperFormalization.NLHFScoreImprovementProfiles
import PaperFormalization.WeakOrderScoreRepresentation
import PaperFormalization.ProfileBorda
import PaperFormalization.WeakProfileBorda
import PaperFormalization.ProfileFord
import PaperFormalization.ProfileRTBT
import PaperFormalization.RTBTPairMonotonicity
import PaperFormalization.RTBTCountMonotonicity
import PaperFormalization.RTBTInvolvement
import PaperFormalization.RTBTExtension

open scoped BigOperators
open scoped Topology
open Filter

namespace PaperFormalization
namespace PaperStatements

/-!
This module is the reviewer-facing index of paper statements.  Each theorem
below is a thin alias or bundle for the declaration that carries the real
proof.  The names match the labels used in `paper/main.tex` whenever Lean's
identifier syntax allows it.
-/

section FordZermelo

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Ford's existence clause only: every strongly connected finite Ford count
matrix admits a positive solution of the displayed Bradley--Terry equations.
This is the schema `FordZermeloBTTheorem`, discharged by
`FordZermeloBTTheorem_finite`; the paper's full Proposition `BTProp` is
`BTProp` below. -/
theorem BTProp_existence : FordZermeloBTTheorem α :=
  FordZermeloBTTheorem_finite

/-- Formal version of Proposition `BTProp` in `paper/main.tex`, at the level
of finite Ford count matrices `c_{x,y}` with pair weights
`w_{x,y} = c_{x,y} + c_{y,x}`: for every strongly connected count matrix
there is a unique `u` carrying the `BTProp` certificate, i.e. `u` is a
full-support lottery satisfying Ford's displayed equations
`B^d_x = Σ_{y ≠ x} w_{x,y} u_x / (u_x + u_y)`, the positive maximizers of the
likelihood `L_R` are exactly the ray `{a • u | a > 0}`, and `u` is the only
normalized solution of the displayed equations.  `BTProp_profile` below is
the same statement for the strict counts of an actual finite profile. -/
theorem BTProp
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasBTPropCertificate (fordPairTotal c) c u :=
  exists_unique_BTProp_certificate hc hconn

/-- Profile-count certificate form of Proposition `BTProp`: the normalized
Bradley--Terry vector for a strongly connected finite profile is unique and
carries both the displayed BT equations and Ford likelihood-maximizer
certificate. -/
theorem BTProp_profile
    {V : Type*} [Fintype V]
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      HasBTPropCertificate
        (fordPairTotal (strictCount R)) (strictCount R) u :=
  exists_unique_BTProp_certificate_strictCountProfile_of_ford_zermelo
    FordZermeloBTTheorem_finite hR hconn

/-- Formal version of Proposition `DPOasRTBT` in `paper/main.tex`, stated for
finite Ford count matrices. -/
theorem DPOasRTBT
    {β : ℝ} (hβ : 0 < β)
    {c : α → α → ℝ} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal c) c u ∧
        dpoArgmaxSet β c ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_finite_ford_zermelo hβ hρ hc hconn

/-- Profile-count form of Proposition `DPOasRTBT`: for a strongly connected
finite irreflexive profile, the DPO argmax set is the singleton RTBT lottery
selected by the formal Ford/Zermelo theorem. -/
theorem DPOasRTBT_profile
    {V : Type*} [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃ u : α → ℝ,
      HasBTPropCertificate
          (fordPairTotal (strictCount R)) (strictCount R) u ∧
        dpoArgmaxSet β (strictCount R) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  exists_DPOasRTBT_strictCountProfile hβ hR hconn hρ

/-- Selected-BT profile-count form of Proposition `DPOasRTBT`, matching the
definition of `RTBT` that uses the unique Ford/Zermelo-selected normalized
Bradley--Terry vector. -/
theorem DPOasRTBT_profile_selectedBT
    {V : Type*} [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    dpoArgmaxSet β (strictCount R) ρ =
      ({RTBTFromStrength β ρ
          (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
            (strictCount R) (strictCount_isFordCountMatrix hR) hconn)} :
        Set (α → ℝ)) :=
  DPOasRTBT_strictCountProfile_selectedBT
    FordZermeloBTTheorem_finite hβ hR hconn hρ

/-- Add-voter profile-count form of Proposition `DPOasRTBT`, used by the
involvement development: after adding an irreflexive voter, the DPO argmax set
is still the singleton RTBT lottery selected by Ford/Zermelo. -/
theorem DPOasRTBT_profile_addVoter
    {V : Type*} [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {p : α → α → Bool} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃ u : α → ℝ,
      HasBTPropCertificate
          (fordPairTotal (strictCount (addVoterProfile R p)))
          (strictCount (addVoterProfile R p)) u ∧
        dpoArgmaxSet β (strictCount (addVoterProfile R p)) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  exists_DPOasRTBT_strictCountProfile_addVoter hβ hR hp hconn hρ

/-- Selected-BT add-voter profile-count form of Proposition `DPOasRTBT`. -/
theorem DPOasRTBT_profile_addVoter_selectedBT
    {V : Type*} [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {p : α → α → Bool} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    dpoArgmaxSet β (strictCount (addVoterProfile R p)) ρ =
      ({RTBTFromStrength β ρ
          (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
            (strictCount (addVoterProfile R p))
            (strictCount_addVoterProfile_isFordCountMatrix hR hp)
            (FordStronglyConnected_strictCount_addVoterProfile p hconn))} :
        Set (α → ℝ)) :=
  DPOasRTBT_strictCountProfile_addVoter_selectedBT
    FordZermeloBTTheorem_finite hβ hR hp hconn hρ

/-- Formal version of Proposition `Anderson`: on a finite profile of
paper-style linear orders, the actual Ford/Zermelo-selected RTBT rule with a
uniform reference induces the strict-domination Borda ranking.  The
Anderson--Dandurova--Falk--Yeganova ranking argument is proved in
`AndersonRanking.lean`; it is not supplied as a premise. -/
theorem Anderson
    {V : Type*} [Fintype V] [Nonempty V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool}
    (hlinear : IsLinearOrderProfile R)
    (hconn : FordStronglyConnected (strictCount (strictPart R)))
    (x y : α) :
    RTBTFromStrength β (finiteUniformLottery α)
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount (strictPart R))
          (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R))
          hconn) x ≥
      RTBTFromStrength β (finiteUniformLottery α)
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount (strictPart R))
          (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R))
          hconn) y ↔
      strictDominationBordaScore (strictPart R) x ≥
        strictDominationBordaScore (strictPart R) y :=
  Anderson_RTBTRanking_linearOrderProfile hβ hlinear hconn x y

end FordZermelo

section IPO

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Proposition `BIPOandPB` in Appendix `IPOApp`: the actual partial-Borda
objective has exactly the PB lottery as minimizer, with minimum value zero. -/
theorem BIPOandPB
    {V : Type*} [Fintype V]
    {η : ℝ} (hη : 0 < η) (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (bordaIPOObjective η R ρ) =
        ({proportionalBorda η ρ (partialBordaScoreP R)} : Set (α → ℝ)) ∧
      bordaIPOObjective η R ρ (proportionalBorda η ρ (partialBordaScoreP R)) = 0 :=
  bordaIPOObjective_argmin_and_zero hη R hρ

/-- The second, unlabelled proposition of Appendix `IPOApp`: on linear
orders, the defined offline-IPO objective is uniquely minimized by PB with
the stated `1/(τmn)` parameter. -/
theorem IPOandPB
    {V : Type*} [Fintype V] [Nonempty V]
    {τ : ℝ} (hτ : 0 < τ)
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (offlineIPOObjective τ R ρ) =
      ({proportionalBorda
        (1 / (τ * (Fintype.card α : ℝ) * (Fintype.card V : ℝ)))
        ρ (partialBordaScoreP R)} : Set (α → ℝ)) :=
  offlineIPOObjective_argmin hτ hR hρ

/-- The first claim of Remark `IPOremark`, justified in the opening paragraph
of Appendix `IPOApp`: the population offline IPO loss of Azar et al.
(Eq. (16)), written in the paper's notation with the expectation taken as the
uniform average over annotators and over ordered pairs of distinct
completions, has the same full-support minimizers as `IPO_τ`, namely the PB
lottery with parameter `1/(τmn)`.  Profiles have at least two candidates. -/
theorem IPOremark_population
    {V : Type*} [Fintype V] [Nonempty V]
    (hm : 2 ≤ Fintype.card α)
    {τ : ℝ} (hτ : 0 < τ)
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (populationIPOLoss τ R ρ) =
        fullSupportArgminSet (offlineIPOObjective τ R ρ) ∧
      fullSupportArgminSet (populationIPOLoss τ R ρ) =
        ({proportionalBorda
          (1 / (τ * (Fintype.card α : ℝ) * (Fintype.card V : ℝ)))
          ρ (partialBordaScoreP R)} : Set (α → ℝ)) :=
  ⟨populationIPOLoss_argmin_eq_offline hm hR hρ,
    populationIPOLoss_argmin hm hτ hR hρ⟩

/-- The per-pair identity displayed in Appendix `IPOApp`: for a fixed ordered
pair of distinct completions, the expected squared loss (the average over
annotators of the squared deviation from the scaled `0/1` label) equals the
`IPO_τ` summand plus the `π`-independent term `V_{x,y}`. -/
theorem IPOremark_population_pair
    {V : Type*} [Fintype V] [Nonempty V]
    {τ : ℝ} {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ π : α → ℝ} (hρ : IsFullSupportLottery ρ) (hπ : IsFullSupportLottery π)
    {x y : α} (hxy : x ≠ y) :
    (∑ i : V, (Real.log (π x * ρ y / (π y * ρ x)) -
        voterPreferenceLabel R i x y / τ) ^ 2) / (Fintype.card V : ℝ) =
      (Real.log (π x / ρ x) - Real.log (π y / ρ y) -
          paperNormalizedCbar R x y / τ) ^ 2 +
        pairLabelVariance τ R x y :=
  pairPopulationIPOLoss_eq hR hρ.1 hπ.1 hxy

end IPO

section NLHFExistence

/-- Formal version of Proposition `nlhf-existence` in the closed-simplex
saddle-pair form, including the paper's diagonal conclusion
`πτ = π'τ`.  Existence is obtained from the proved finite-dimensional
specialization of Sion's minimax theorem in `NLHFExistence.lean`. -/
theorem «nlhf-existence»
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    (∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedClosedSaddle τ M ρ pq.1 pq.2) ∧
      ∀ p q : α → ℝ,
        IsNLHFRegularizedClosedSaddle τ M ρ p q → p = q :=
  ⟨exists_unique_nlhfRegularizedClosedSaddlePair hτ hM hρ,
    fun _ _ hsaddle =>
      regularizedClosedSaddle_left_eq_right hτ hM hρ hsaddle⟩

/-- Unique-lottery diagonal form of Proposition `nlhf-existence`. -/
theorem «nlhf-existence-diagonal»
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ, IsNLHFRegularizedClosedSaddle τ M ρ π π := by
  rcases exists_unique_nlhfRegularizedClosedSaddlePair hτ hM hρ with
    ⟨pq, hpq, huniq⟩
  have hdiag :
      pq.1 = pq.2 :=
    regularizedClosedSaddle_left_eq_right hτ hM hρ hpq
  refine ⟨pq.2, ?_, ?_⟩
  · simpa [hdiag] using hpq
  · intro π hπ
    have hpair : (π, π) = pq := huniq (π, π) hπ
    exact congrArg Prod.snd hpair

/-- Fixed-point form of Proposition `nlhf-existence`, matching the definition
of the selected NLHF lottery used later in the paper. -/
theorem «nlhf-existence-fixed-point»
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ, IsNLHFFixedPoint τ M ρ π :=
  exists_unique_nlhfFixedPoint hτ hM hρ

/-- Proposition `nlhf-existence` for the paper's *own* objective `Γ_τ`, which
is written with the normalized comparison probabilities
`c̄_{x,y} = (1 + m̄_{x,y})/2` rather than with `m̄` directly.  The equivalence
with the `m̄` form is Remark `NLHFreformulated`
(`gammaClosedSaddle_iff_regularizedClosedSaddle`); note that
`nlhfSionValue τ M ρ` is `Γ̄_{2τ}`, since `1 / nlhfLambda τ = 2τ`. -/
theorem «nlhf-existence-cbar»
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    (∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFGammaClosedSaddle τ (cbarOfMargin M) ρ pq.1 pq.2) ∧
      (∀ p q : α → ℝ,
        IsNLHFGammaClosedSaddle τ (cbarOfMargin M) ρ p q → p = q) ∧
      (∀ p q : α → ℝ,
        IsNLHFGammaClosedSaddle τ (cbarOfMargin M) ρ p q ↔
          IsNLHFRegularizedClosedSaddle τ M ρ p q) :=
  ⟨exists_unique_nlhfGammaClosedSaddlePair hτ hM hρ,
    fun _ _ hsaddle => gammaClosedSaddle_left_eq_right hτ hM hρ hsaddle,
    fun _ _ => gammaClosedSaddle_iff_regularizedClosedSaddle⟩

/-- Proposition `nlhf-existence` over an *actual* finite profile of reflexive
binary relations, with the paper's pair-normalized comparison probabilities
`c̄_{x,y}(𝐑) = (c_{x,y} + ½ i_{x,y}) / t_{x,y}` (and the `t = 0 ↦ ½`
convention) and the paper's objective `Γ_τ(𝐑,ρ)`.  Unlike the `|V|`-normalized
profile-level wrappers, this uses the pair-specific normalization of
`paper/main.tex`. -/
theorem «nlhf-existence-weak-profile»
    {α V : Type*} [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ) (R : V → α → α → Bool)
    (hρ : IsFullSupportLottery ρ) :
    (∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFGammaClosedSaddle τ (paperNormalizedCbar R) ρ pq.1 pq.2) ∧
      (∀ p q : α → ℝ,
        IsNLHFGammaClosedSaddle τ (paperNormalizedCbar R) ρ p q → p = q) ∧
      (∀ x y : α,
        paperNormalizedMargin R x y = 2 * paperNormalizedCbar R x y - 1) :=
  ⟨exists_unique_nlhfGammaClosedSaddlePair_weakProfile hτ R hρ,
    fun _ _ hsaddle =>
      gammaClosedSaddle_weakProfile_left_eq_right hτ R hρ hsaddle,
    fun x y =>
      paperNormalizedMargin_eq_two_mul_paperNormalizedCbar_sub_one R x y⟩

end NLHFExistence

/-- Lemma `nlhf-variational`: the selected lottery maximizes the regularized
margin objective over the entire closed simplex, following the English
first-player saddle-point proof. -/
theorem «nlhf-variational»
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ) (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∀ r : α → ℝ, IsLottery r →
      marginValue M r (selectedNLHF τ M ρ) - (1 / nlhfLambda τ) * KL r ρ ≤
        marginValue M (selectedNLHF τ M ρ) (selectedNLHF τ M ρ) -
          (1 / nlhfLambda τ) * KL (selectedNLHF τ M ρ) ρ := by
  intro r hr
  simpa only [marginValue_self_eq_zero_of_normalized _ hM, zero_sub, neg_mul] using
    nlhf_variational_inequality_of_normalized_fixedPoint hM
      (selectedNLHF_selection hτ hM hρ) hr

section MaxLott

variable {α : Type*} [Fintype α]

/-- Formal version of Proposition `MaxLottProp` in `paper/main.tex`: for any
sequence of positive regularization parameters `τ_n → 0`, the selected NLHF
lotteries have a convergent subsequence whose limit is a maximal lottery,
and the limit of every convergent subsequence is a maximal lottery. -/
theorem MaxLottProp
    {M : α → α → ℝ} {ρ : α → ℝ} {τn : ℕ → ℝ}
    (hτpos : ∀ n : ℕ, 0 < τn n)
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    (∃ π : α → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ x : α,
          Tendsto (fun n => selectedNLHF (τn (φ n)) M ρ x) atTop (𝓝 (π x))) ∧
        IsMaximalLottery M π) ∧
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ π : α → ℝ,
        (∀ x : α,
          Tendsto (fun n => selectedNLHF (τn (φ n)) M ρ x) atTop (𝓝 (π x))) →
        IsMaximalLottery M π :=
  ⟨exists_subseq_selectedNLHF_tendsto_maximalLottery hτpos hτ hM hρ,
    fun _φ hφ _π hπn =>
      maximalLottery_of_selectedNLHF_subseq_tendsto hτpos hτ hM hρ hφ hπn⟩

/-- Abstract limiting-saddle form of Proposition `MaxLottProp` for arbitrary
sequences satisfying the saddle inequality. -/
theorem MaxLottProp_limit
    {M : α → α → ℝ} {π : α → ℝ} {πn : ℕ → α → ℝ}
    {τn : ℕ → ℝ} {ρ : α → ℝ}
    (hπlot : IsLottery π)
    (hρ : IsFullSupportLottery ρ)
    (hπn : ∀ x : α, Tendsto (fun n => πn n x) atTop (𝓝 (π x)))
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hsaddle : ∀ n : ℕ, ∀ ν : α → ℝ, IsLottery ν →
      2 * τn n * (KL (πn n) ρ - KL ν ρ) ≤ marginValue M (πn n) ν) :
    IsMaximalLottery M π :=
  PaperFormalization.MaxLottProp hπlot hρ hπn hτ hsaddle

end MaxLott

section Monotonicity

/-- Formal version of Proposition `PBPM` in `paper/main.tex`: proportional
Borda with the camera-ready partial-Borda score `B^p = Σ (c + ½ i + ½ n)` is
probabilistically monotone.  Profiles are read as weak relations
(indifference and noncomparability distinguished), and the improvement
hypothesis is the paper's conditions (i)–(iii) verbatim.  The reference `ρ`
ranges over the paper's full domain `Δ`: the paper's proof disposes of the
case `ρ(x) = 0` separately, so no `0 < ρ x` hypothesis is needed. -/
theorem PBPM
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R R' : V → α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (h : IsWeakProfileImprovement R R' x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
      proportionalBorda η ρ (partialBordaScoreP R') x :=
  PBPM_weak_from_profile_improvement' hη hρnonneg h

/-- Strict-reading specialization of Proposition `PBPM`, with the
strict-domination score `B^d` (the variant the paper's footnote sets
aside).  Kept for the `B^d` development; the paper-facing statement is
`PBPM` above. -/
theorem PBPM_strict
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R R' : V → α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (h : IsProfileImprovement R R' x) :
    proportionalBorda η ρ (strictDominationBordaScore R) x ≤
      proportionalBorda η ρ (strictDominationBordaScore R') x :=
  PBPM_from_profile_improvement' hη hρnonneg h

/-- Formal version of Proposition `RTBTPM` in `paper/main.tex`, stated at the
level at which the paper defines `RTBT_β`: Ford count matrices `c_{x,y}` with
the heterogeneous pair weights `w_{x,y} = c_{x,y} + c_{y,x}`.  Both `(c,ρ)`
and `(c⁺,ρ)` are required to lie in the paper's domain `𝒟` (positive-count
graph strongly connected, `ρ` of full support), which is exactly the
quantification of the paper's probabilistic-monotonicity axiom.  The
Bradley--Terry strengths are the Ford/Zermelo selected solutions, so the
statement is unconditional: no selector hypothesis, and existence is supplied
by `BTProp`. -/
theorem RTBTPM
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {β : ℝ} (hβ : 0 < β)
    {c c' : α → α → ℝ} {ρ : α → ℝ} {x : α}
    (hc : IsFordCountMatrix c) (hc' : IsFordCountMatrix c')
    (hconn : FordStronglyConnected c) (hconn' : FordStronglyConnected c')
    (hρ : IsFullSupportLottery ρ)
    (himp : IsCountImprovementOf c c' x) :
    RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite c hc hconn) x ≤
      RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite c' hc' hconn')
          x :=
  RTBTPM_count_selectedBTOfFordZermelo hβ hc hc' hconn hconn' hρ himp

/-- Formal version of Proposition `RTBTPM` on weak-relation profiles.  Voters
hold arbitrary weak relations (indifference and noncomparability
distinguished), the improvement hypothesis is the paper's conditions
(i)–(iii) verbatim, the Bradley--Terry strengths are computed from the strict
preference counts `c_{x,y}` exactly as in `RTBTorder`, and both profiles are
required to lie in the paper's domain `𝒟` — precisely the quantification of
the probabilistic-monotonicity axiom. -/
theorem RTBTPM_profile
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hconn : FordStronglyConnected (strictCount (strictPart R)))
    (hconn' : FordStronglyConnected (strictCount (strictPart R')))
    (hρ : IsFullSupportLottery ρ)
    (himp : IsWeakProfileImprovement R R' x) :
    RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount (strictPart R))
          (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R))
          hconn) x ≤
      RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount (strictPart R'))
          (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R'))
          hconn') x :=
  RTBTPM_profile_weak_selectedBTOfFordZermelo hβ hconn hconn' hρ himp

/-- Analytic companion bundle for Theorem `NLHFmono`, retained as proof
scaffolding.  Its first clause is matrix-level monotonicity over all finite
normalized margin matrices; its `1/8` clauses
(`SelectedNLHFWeakOrderProfileMonotonicity`,
`SelectedNLHFLinearOrderProfileMonotonicity`) compare an arbitrary normalized
margin matrix with a score profile differing from it by a single uniform
block improvement, which is *not* the paper's quantification over two
weak-order profiles related by conditions (i)–(iii).  The paper's theorem is
`NLHFmono` below. -/
theorem NLHFmono_margin_score_bundle
    {τ : ℝ} (hτ : 0 < τ) :
    (SelectedNLHFAllProfileMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ) ∧
      (SelectedNLHFWeakOrderProfileMonotonicity τ ↔
        (1 : ℝ) / 8 ≤ τ) ∧
        (SelectedNLHFLinearOrderProfileMonotonicity τ ↔
          (1 : ℝ) / 8 ≤ τ) :=
  ⟨NLHFmono_all_profiles hτ,
    NLHFmono_weak_order_profiles hτ,
    NLHFmono_linear_order_profiles hτ⟩

/-- Actual finite-profile positive clauses used in the right-to-left direction
of Theorem `NLHFmono`: for `τ ≥ 1/8`, selected NLHF is monotone on weak-order
score profiles and on their linear-order specialization. -/
theorem NLHFmono_actual_profile_positive_clauses
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFWeakOrderProfileMonotonicity τ ∧
      SelectedNLHFLinearOrderProfileMonotonicity τ :=
  ⟨selectedNLHF_weakOrderProfileMonotone_of_tau_ge_one_eighth hτge,
    selectedNLHF_linearOrderProfileMonotone_of_tau_ge_one_eighth hτge⟩

/-- Denominator-cleared actual finite-profile linear-order witness for the
left-to-right direction of the `1/8` clause of Theorem `NLHFmono`.  The
statement includes the exact singleton block-change equation used to refute
actual finite linear-order profile monotonicity below the threshold. -/
theorem NLHFmono_actual_linear_profile_converse_witness
    {τ : ℝ} (hτ : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
    ∃ N m : ℕ, ∃ b δ : ℝ,
    ∃ B : Finset {z : Fin 3 // z ≠ 0},
      0 < N ∧ 0 < b ∧ b < 1 ∧ 0 < δ ∧ B.Nonempty ∧
      IsFullSupportLottery
        (nlhfBacksolvedReference τ
          (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
          (nlhfSharpSymLottery3 b)) ∧
      IsLinearScoreProfile (nlhfSharpLinearReplicatedOldScore3 N m) ∧
      IsLinearScoreProfile (nlhfSharpLinearReplicatedMovedScore3 N m) ∧
      IsImprovementOf
        (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
        (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
        0 ∧
      (∀ a b' : Fin 3,
        scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m) a b' -
            scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m) a b' =
          blockImprovementChange 0
            (B.map (Function.Embedding.subtype
              (fun z : Fin 3 => z ≠ 0))) δ a b') ∧
      selectedNLHF (α := Fin 3) τ
          (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) 0 <
        selectedNLHF (α := Fin 3) τ
          (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) 0 :=
  selectedNLHF_linear_lowTempFiniteProfileBlockDrop_fin3 τ hτ hτlt

/-- Profile-level completion of the all-profiles clause of Theorem
`NLHFmono`.  Here "all profiles" means all actual finite profiles of
reflexive binary relations (indifference and noncomparability distinguished),
read through the paper's pair-normalized margin `m̄_{x,y} = m_{x,y}/t_{x,y}`,
and "improvement" is the paper's conditions (i)–(iii) verbatim.  The
right-to-left direction is Lemma `profile-margin-reduction` composed with the
matrix-level theorem; the left-to-right direction is the paper's transitive
pair-block electorate, realized as an actual pair of finite profiles. -/
theorem NLHFmono_profile_all
    {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFWeakProfileAllMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_weak_profile_all hτ

/-- The paper's transitive-profile witness for the left-to-right direction of
the all-profiles clause of Theorem `NLHFmono`.  Both profiles are actual
finite profiles of reflexive *and transitive* binary relations over a common
electorate, they differ at exactly one voter, the change is an improvement of
`x = 0` in the paper's sense (i)–(iii), and selected NLHF strictly drops. -/
theorem NLHFmono_actual_transitive_profile_converse_witness
    {τ : ℝ} (hτ : 0 < τ) (hτlt : τ < (3 : ℝ) / 8) :
    ∃ N m : ℕ, ∃ b : ℝ,
      0 < N ∧ 0 < b ∧ b < 1 ∧
      IsReflexiveProfile
        (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))) ∧
      IsReflexiveProfile
        (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1)) ∧
      IsTransitiveProfile
        (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))) ∧
      IsTransitiveProfile
        (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1)) ∧
      IsWeakProfileImprovement
        (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1)))
        (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1))
        (0 : Fin 3) ∧
      IsFullSupportLottery
        (nlhfBacksolvedReference τ
          (paperNormalizedMargin
            (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
          (nlhfSharpSymLottery3 b)) ∧
      selectedNLHF (α := Fin 3) τ
          (paperNormalizedMargin
            (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1)))
          (nlhfBacksolvedReference τ
            (paperNormalizedMargin
              (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
            (nlhfSharpSymLottery3 b)) 0 <
        selectedNLHF (α := Fin 3) τ
          (paperNormalizedMargin
            (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
          (nlhfBacksolvedReference τ
            (paperNormalizedMargin
              (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
            (nlhfSharpSymLottery3 b)) 0 :=
  nlhfSharpAllWeak_lowTempProfileDrop_fin3
    (selectedNLHF (α := Fin 3))
    (selectedNLHF_selection (α := Fin 3))
    (selectedNLHF_isTheNLHF (α := Fin 3)) τ hτ hτlt

/-- Reviewer-facing bridge showing that every finite paper-style weak-order
profile has an exact real-score representation, with no change to the
paper-normalized margin. -/
theorem NLHFmono_finite_weak_order_score_representation
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsWeakOrderProfile R) :
    ∃ score : V → α → ℝ,
      scoreWeakProfile score = R ∧
        paperNormalizedMargin R = scoreProfileMargin score :=
  ⟨weakOrderScoreProfile R,
    scoreWeakProfile_weakOrderScoreProfile hR,
    paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile hR⟩

/-- Antisymmetry makes the representing scores injective, giving the
corresponding exact bridge for finite linear-order profiles. -/
theorem NLHFmono_finite_linear_order_score_representation
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R) :
    ∃ score : V → α → ℝ,
      IsLinearScoreProfile score ∧
        scoreWeakProfile score = R ∧
          paperNormalizedMargin R = scoreProfileMargin score :=
  ⟨weakOrderScoreProfile R,
    weakOrderScoreProfile_linear hR,
    scoreWeakProfile_weakOrderScoreProfile hR.1,
    paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile hR.1⟩

/-- Formal version of Theorem `NLHFmono` in `paper/main.tex`.  All three
clauses are stated over *actual finite profiles* related by the paper's
improvement conditions (i)-(iii): the `3/8` clause over arbitrary profiles of
reflexive binary relations with the pair-normalized margin `m̄`, and the
`1/8` clauses directly over arbitrary complete/transitive Boolean weak orders
and their antisymmetric (linear-order) specialization.  The finite
score-representation theorems above transport these relation-valued profiles
exactly to the one-position-at-a-time chaining proof. -/
theorem NLHFmono
    {τ : ℝ} (hτ : 0 < τ) :
    (SelectedNLHFWeakProfileAllMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ) ∧
      (SelectedNLHFPaperWeakOrderImprovementMonotonicity τ ↔
        (1 : ℝ) / 8 ≤ τ) ∧
        (SelectedNLHFPaperLinearOrderImprovementMonotonicity τ ↔
          (1 : ℝ) / 8 ≤ τ) :=
  ⟨NLHFmono_weak_profile_all hτ,
    NLHFmono_paper_weak_order_improvements hτ,
    NLHFmono_paper_linear_order_improvements hτ⟩

/-- `NLHFmono` under its former name, kept so that existing documentation
references remain valid. -/
theorem NLHFmono_profile_improvements
    {τ : ℝ} (hτ : 0 < τ) :
    (SelectedNLHFWeakProfileAllMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ) ∧
      (SelectedNLHFPaperWeakOrderImprovementMonotonicity τ ↔
        (1 : ℝ) / 8 ≤ τ) ∧
        (SelectedNLHFPaperLinearOrderImprovementMonotonicity τ ↔
          (1 : ℝ) / 8 ≤ τ) :=
  NLHFmono hτ

/-- Common-electorate linear-order witness for the left-to-right direction of
the `1/8` clauses.  Both profiles are actual finite linear-order profiles on
the *same* voter set `Fin (N (m+1))`, they differ at exactly one voter, and
the change satisfies the paper's improvement conditions (i)-(iii) for `x = 0`
-- so the voter-by-voter improvement relation is explicit, not implicit. -/
theorem NLHFmono_actual_linear_profile_voterwise_converse_witness
    {τ : ℝ} (hτ : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
    ∃ N m : ℕ, ∃ b : ℝ,
      0 < N ∧ 0 < b ∧ b < 1 ∧
      IsLinearScoreProfile
        (nlhfSharpLinearThresholdScore3 (N * (m + 1)) ((N - 1) * (m + 1))) ∧
      IsLinearScoreProfile
        (nlhfSharpLinearThresholdScore3 (N * (m + 1))
          ((N - 1) * (m + 1) + 1)) ∧
      IsWeakProfileImprovement
        (scoreWeakProfile (nlhfSharpLinearThresholdScore3 (N * (m + 1))
          ((N - 1) * (m + 1))))
        (scoreWeakProfile (nlhfSharpLinearThresholdScore3 (N * (m + 1))
          ((N - 1) * (m + 1) + 1)))
        (0 : Fin 3) ∧
      IsFullSupportLottery
        (nlhfBacksolvedReference τ
          (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
            ((N - 1) * (m + 1))))
          (nlhfSharpSymLottery3 b)) ∧
      selectedNLHF (α := Fin 3) τ
          (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
            ((N - 1) * (m + 1) + 1)))
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
              ((N - 1) * (m + 1))))
            (nlhfSharpSymLottery3 b)) 0 <
        selectedNLHF (α := Fin 3) τ
          (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
            ((N - 1) * (m + 1))))
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
              ((N - 1) * (m + 1))))
            (nlhfSharpSymLottery3 b)) 0 :=
  nlhfSharpLinearThreshold_lowTempProfileDrop_fin3
    (selectedNLHF (α := Fin 3))
    (selectedNLHF_selection (α := Fin 3))
    (selectedNLHF_isTheNLHF (α := Fin 3)) τ hτ hτlt

end Monotonicity

section Involvement

/-- Positive-involvement half of Proposition `PBPPI`, for the paper's
partial-Borda score `B^p` on weak-relation profiles: the added voter ranks
`x` uniquely (strictly) first. -/
theorem PBPPI_positive
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pTop : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hcard : 2 ≤ Fintype.card α)
    (htop : RanksStrictlyTop pTop x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
      proportionalBorda η ρ
        (partialBordaScoreP (addVoterProfile R pTop)) x :=
  PBPPI_weak_from_added_top_profile' hη hρnonneg hcard htop

/-- Negative-involvement half of Proposition `PBPPI`, for the paper's
partial-Borda score `B^p` on weak-relation profiles. -/
theorem PBPPI_negative
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pBottom : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hbottom : RanksStrictlyBottom pBottom x) :
    proportionalBorda η ρ
        (partialBordaScoreP (addVoterProfile R pBottom)) x ≤
      proportionalBorda η ρ (partialBordaScoreP R) x :=
  PBPNI_weak_from_added_bottom_profile' hη hρnonneg hbottom

/-- Formal version of Proposition `PBPPI` in `paper/main.tex`, bundled for
positive and negative involvement, with the paper's partial-Borda score
`B^p` on weak-relation profiles. -/
theorem PBPPI
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pTop pBottom : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hcard : 2 ≤ Fintype.card α)
    (htop : RanksStrictlyTop pTop x)
    (hbottom : RanksStrictlyBottom pBottom x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
        proportionalBorda η ρ
          (partialBordaScoreP (addVoterProfile R pTop)) x ∧
      proportionalBorda η ρ
          (partialBordaScoreP (addVoterProfile R pBottom)) x ≤
        proportionalBorda η ρ (partialBordaScoreP R) x :=
  ⟨PBPPI_positive hη hρnonneg hcard htop,
    PBPPI_negative hη hρnonneg hbottom⟩

/-- Strict-reading specialization of the positive-involvement half of
`PBPPI`, with the strict-domination score `B^d`. -/
theorem PBPPI_positive_strict
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pTop : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hcard : 2 ≤ Fintype.card α)
    (hasymmTop : IsAsymmetricPref pTop) (htop : RanksTop pTop x) :
    proportionalBorda η ρ (strictDominationBordaScore R) x ≤
      proportionalBorda η ρ
        (strictDominationBordaScore (addVoterProfile R pTop)) x :=
  PBPPI_from_added_top_profile'
    hη hρnonneg hcard hasymmTop htop

/-- Strict-reading specialization of the negative-involvement half of
`PBPPI`, with the strict-domination score `B^d`. -/
theorem PBPPI_negative_strict
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pBottom : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hasymmBottom : IsAsymmetricPref pBottom)
    (hbottom : RanksBottom pBottom x) :
    proportionalBorda η ρ
        (strictDominationBordaScore (addVoterProfile R pBottom)) x ≤
      proportionalBorda η ρ (strictDominationBordaScore R) x :=
  PBPNI_from_added_bottom_profile'
    hη hρnonneg hasymmBottom hbottom

/-- Positive-involvement violation half of Proposition `InvolveViolNLHF`:
the witness predicate `LinearOrderAddsTopMargins` carries genuine profile
content — `M` and `M'` are the normalized margin matrices of an actual
linear-order profile and of that profile plus one added linear voter who
ranks `x` first (on linear-order profiles this normalization agrees with
the paper's `t_{x,y}`-normalization; see
`paperNormalizedMargin_eq_normalizedStrictMargin_of_linearProfile`). -/
theorem InvolveViolNLHF_positive
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesPositiveInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsTopMargins :=
  (selectedNLHF_involvement_violation_profileRealization hτ).1

/-- Negative-involvement violation half of Proposition `InvolveViolNLHF`,
with the profile-level witness predicate (added linear voter ranking `x`
last). -/
theorem InvolveViolNLHF_negative
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesNegativeInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsBottomMargins :=
  (selectedNLHF_involvement_violation_profileRealization hτ).2

/-- Formal version of Proposition `InvolveViolNLHF` in `paper/main.tex`,
with profile-level witness predicates. -/
theorem InvolveViolNLHF
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesPositiveInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsTopMargins ∧
      ViolatesNegativeInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsBottomMargins :=
  ⟨InvolveViolNLHF_positive hτ, InvolveViolNLHF_negative hτ⟩

/-- Positive-involvement violation half of Proposition `InvolveViolRTBT`,
stated as an actual strict-linear-order profile plus one added voter.  In this
strict-profile convention `IsLinearPref` is the irreflexive strict part of the
paper's reflexive linear order, so `strictCount R` is exactly its
`c_{x,y}`.  Both the original and enlarged profiles carry the RTBT domain
certificate, and the rule is the actual Ford/Zermelo-selected RTBT. -/
theorem InvolveViolRTBT_positive
    {β : ℝ} (hβ : 0 < β) :
    ∃ (R : Fin 3 → Fin 3 → Fin 3 → Bool)
        (p : Fin 3 → Fin 3 → Bool) (x : Fin 3),
      (∀ i, IsLinearPref (R i)) ∧
        IsLinearPref p ∧ RanksTop p x ∧
        ∃ (hR : IsIrreflexiveProfile R)
          (hp : ∀ z, p z z = false)
          (hconnR : FordStronglyConnected (strictCount R))
          (hconnPlus :
            FordStronglyConnected (strictCount (addVoterProfile R p))),
          ∃ ρ : Fin 3 → ℝ,
            IsFullSupportLottery ρ ∧
              RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
                    (strictCount (addVoterProfile R p))
                    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
                    hconnPlus) x <
                RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
                    (strictCount R)
                    (strictCount_isFordCountMatrix hR) hconnR) x :=
  InvolveViolRTBT_positive_profile_of_ford_zermelo
    (FordZermeloBTTheorem_finite (α := Fin 3)) hβ

/-- Negative-involvement violation half of Proposition `InvolveViolRTBT`,
again on an actual strict-linear-order profile and literal added voter who
ranks the affected candidate last. -/
theorem InvolveViolRTBT_negative
    {β : ℝ} (hβ : 0 < β) :
    ∃ (R : Fin 3 → Fin 3 → Fin 3 → Bool)
        (p : Fin 3 → Fin 3 → Bool) (x : Fin 3),
      (∀ i, IsLinearPref (R i)) ∧
        IsLinearPref p ∧ RanksBottom p x ∧
        ∃ (hR : IsIrreflexiveProfile R)
          (hp : ∀ z, p z z = false)
          (hconnR : FordStronglyConnected (strictCount R))
          (hconnPlus :
            FordStronglyConnected (strictCount (addVoterProfile R p))),
          ∃ ρ : Fin 3 → ℝ,
            IsFullSupportLottery ρ ∧
              RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
                    (strictCount R)
                    (strictCount_isFordCountMatrix hR) hconnR) x <
                RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
                    (strictCount (addVoterProfile R p))
                    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
                    hconnPlus) x :=
  InvolveViolRTBT_negative_profile_of_ford_zermelo
    (FordZermeloBTTheorem_finite (α := Fin 3)) hβ

/-- Formal version of Proposition `InvolveViolRTBT` in `paper/main.tex`,
bundling the genuine profile-level positive and negative witnesses. -/
theorem InvolveViolRTBT
    {β : ℝ} (hβ : 0 < β) :
    (∃ (R : Fin 3 → Fin 3 → Fin 3 → Bool)
        (p : Fin 3 → Fin 3 → Bool) (x : Fin 3),
      (∀ i, IsLinearPref (R i)) ∧
        IsLinearPref p ∧ RanksTop p x ∧
        ∃ (hR : IsIrreflexiveProfile R)
          (hp : ∀ z, p z z = false)
          (hconnR : FordStronglyConnected (strictCount R))
          (hconnPlus :
            FordStronglyConnected (strictCount (addVoterProfile R p))),
          ∃ ρ : Fin 3 → ℝ,
            IsFullSupportLottery ρ ∧
              RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
                    (strictCount (addVoterProfile R p))
                    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
                    hconnPlus) x <
                RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
                    (strictCount R)
                    (strictCount_isFordCountMatrix hR) hconnR) x) ∧
      (∃ (R : Fin 3 → Fin 3 → Fin 3 → Bool)
          (p : Fin 3 → Fin 3 → Bool) (x : Fin 3),
        (∀ i, IsLinearPref (R i)) ∧
          IsLinearPref p ∧ RanksBottom p x ∧
          ∃ (hR : IsIrreflexiveProfile R)
            (hp : ∀ z, p z z = false)
            (hconnR : FordStronglyConnected (strictCount R))
            (hconnPlus :
              FordStronglyConnected (strictCount (addVoterProfile R p))),
            ∃ ρ : Fin 3 → ℝ,
              IsFullSupportLottery ρ ∧
                RTBTFromStrength β ρ
                    (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
                      (strictCount R)
                      (strictCount_isFordCountMatrix hR) hconnR) x <
                  RTBTFromStrength β ρ
                    (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
                      (strictCount (addVoterProfile R p))
                      (strictCount_addVoterProfile_isFordCountMatrix hR hp)
                      hconnPlus) x) :=
  ⟨InvolveViolRTBT_positive hβ, InvolveViolRTBT_negative hβ⟩

end Involvement

section Commutativity

/-- Formal version of Proposition `RTBTorder` in `paper/main.tex`: `PB_η^p`
(with the paper's partial-Borda score on weak-relation profiles) and
Ford/Zermelo-selected `RTBT_β` are commutative.  The Bradley–Terry strengths
are computed from the strict-preference counts `c_{x,y}` of each profile,
i.e. from `strictPart`. -/
theorem RTBTorder
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η β : ℝ} (hβ : 0 < β)
    {R S : V → α → α → Bool} {ρ : α → ℝ}
    (hconnR : FordStronglyConnected (strictCount (strictPart R)))
    (hconnS : FordStronglyConnected (strictCount (strictPart S)))
    (hρ : IsFullSupportLottery ρ) :
    proportionalBorda η
        (proportionalBorda η ρ (partialBordaScoreP R))
        (partialBordaScoreP S) =
      proportionalBorda η
        (proportionalBorda η ρ (partialBordaScoreP S))
        (partialBordaScoreP R) ∧
    RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
            (strictCount (strictPart R))
            (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R))
            hconnR))
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount (strictPart S))
          (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart S))
          hconnS) =
      RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
            (strictCount (strictPart S))
            (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart S))
            hconnS))
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount (strictPart R))
          (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R))
          hconnR) :=
  ⟨proportionalBordaWeakProfile_commutative R S hρ,
    (RTBTorder_profile_selectedBTOfFordZermelo
      (η := η) FordZermeloBTTheorem_finite hβ
      (isIrreflexiveProfile_strictPart R) (isIrreflexiveProfile_strictPart S)
      hconnR hconnS hρ).2⟩

/-- Strict-reading specialization of Proposition `RTBTorder`, with the
strict-domination score `B^d` on strict profiles. -/
theorem RTBTorder_strict
    {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η β : ℝ} (hβ : 0 < β)
    {R S : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hS : IsIrreflexiveProfile S)
    (hconnR : FordStronglyConnected (strictCount R))
    (hconnS : FordStronglyConnected (strictCount S))
    (hρ : IsFullSupportLottery ρ) :
    proportionalBorda η
        (proportionalBorda η ρ (strictDominationBordaScore R))
        (strictDominationBordaScore S) =
      proportionalBorda η
        (proportionalBorda η ρ (strictDominationBordaScore S))
        (strictDominationBordaScore R) ∧
    RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
            (strictCount R) (strictCount_isFordCountMatrix hR) hconnR))
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount S) (strictCount_isFordCountMatrix hS) hconnS) =
      RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
            (strictCount S) (strictCount_isFordCountMatrix hS) hconnS))
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount R) (strictCount_isFordCountMatrix hR) hconnR) :=
  RTBTorder_profile_selectedBTOfFordZermelo
    FordZermeloBTTheorem_finite hβ hR hS hconnR hconnS hρ

/-- Reusable abstract algebraic engine behind the full-domain statement. -/
theorem RTBTorder_domain_abstract
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (η : ℝ) {β : ℝ} (hβ : 0 < β)
    (B : (α → α → ℝ) → α → ℝ)
    (P : (α → α → ℝ) → Prop) {BT : (α → α → ℝ) → α → ℝ}
    (hBTpos : ∀ M : α → α → ℝ, P M → ∀ x : α, 0 < BT M x) :
    SatisfiesCommutativityOn (fun _ ρ => IsLottery ρ)
        (fun M ρ => proportionalBorda η ρ (B M)) ∧
      SatisfiesCommutativityOn (fun M ρ => P M ∧ IsFullSupportLottery ρ)
        (fun M ρ => RTBTFromStrength β ρ (BT M)) :=
  ⟨proportionalBordaMatrixRule_commutativityOn η B,
    RTBTFromStrength_commutativityOn hβ P hBTpos⟩

/-- Proposition `RTBTorder` against the paper's *full* commutativity
definition, instantiated with no caller-supplied score, domain, or BT rule.
`FiniteProfile` bundles the electorate size, so the two quantified profiles
may have different electorates.  Both domains require a nonempty electorate
of reflexive weak relations.  `PB_η^p` uses the actual partial-Borda score on
all reference lotteries `Δ`; `RTBT_β` uses strict-preference counts, Ford
connectivity, the actual Ford/Zermelo-selected BT vector, and full-support
references `Δ°`.  The selector's explicit total fallback is outside this
domain and agrees with selected Ford BT on-domain by
`finiteProfileSelectedBTOfFordZermelo_eq_on_domain`. -/
theorem RTBTorder_domain
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (η : ℝ) {β : ℝ} (hβ : 0 < β) :
    SatisfiesCommutativityOn
        (finiteProfileProportionalBordaDomain (α := α))
        (finiteProfileProportionalBordaRule (α := α) η) ∧
      SatisfiesCommutativityOn
        (finiteProfileRTBTDomain (α := α))
        (finiteProfileRTBTRule
          (FordZermeloBTTheorem_finite (α := α)) β) :=
  finiteProfileRTBTorder_commutativityOn
    (FordZermeloBTTheorem_finite (α := α)) η hβ

/-- Formal version of Proposition `NLHFcomm` in `paper/main.tex`. -/
theorem NLHFcomm
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesCommutativity ((selectedNLHF (α := Fin 3)) τ) :=
  selectedNLHF_commutativity_violation hτ

/-- Proposition `NLHFcomm` against the *full* commutativity definition of
`paper/main.tex`: `NLHF_τ` maps its domain `{(𝐑,ρ) | ρ ∈ Δ°}` into `Δ°`, so
the domain-closure clauses are automatically satisfied and the failure is
genuinely a failure of the paper's property, not an artifact of dropping
them. -/
theorem NLHFcomm_domain
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesCommutativityOn
      (fun (M : Fin 3 → Fin 3 → ℝ) (ρ : Fin 3 → ℝ) =>
        IsNormalizedMarginMatrix M ∧ IsFullSupportLottery ρ)
      ((selectedNLHF (α := Fin 3)) τ) :=
  violatesCommutativityOn_of_violatesCommutativity_selectedNLHF hτ
    (selectedNLHF_commutativity_violation hτ)

/-- Profile-level companion to Proposition `NLHFcomm`, matching the paper's
parenthetical "even on profiles of linear orders": the violation witnesses
are realized by the paper's actual profiles — the three-voter cycle `𝐂`
(rankings `abc`, `bca`, `cab`) and the one-voter profile `𝐋` (`abc`) —
both certified to consist of strict linear orders, with the uniform
reference; the selected NLHF rule gives different results depending on the
order in which the two profiles are incorporated.  The witness margin
matrices are certified both as the `|V|`-normalized strict margins and as the
paper's pair-normalized margins `m̄` (`paperNormalizedMargin`), which coincide
on linear-order profiles. -/
theorem NLHFcomm_profile_witness
    {τ : ℝ} (hτ : 0 < τ) :
    IsStrictLinearOrderProfile cycleProfile3 ∧
      IsStrictLinearOrderProfile linearProfile3 ∧
        normalizedStrictMargin cycleProfile3 = cycleMargin3 ∧
          normalizedStrictMargin linearProfile3 = linearMargin3 ∧
            paperNormalizedMargin cycleProfile3 = cycleMargin3 ∧
              paperNormalizedMargin linearProfile3 = linearMargin3 ∧
                IsFullSupportLottery uniform3 ∧
                  selectedNLHF (α := Fin 3) τ
                      (normalizedStrictMargin cycleProfile3)
                      (selectedNLHF (α := Fin 3) τ
                        (normalizedStrictMargin linearProfile3) uniform3) ≠
                    selectedNLHF (α := Fin 3) τ
                      (normalizedStrictMargin linearProfile3)
                      (selectedNLHF (α := Fin 3) τ
                        (normalizedStrictMargin cycleProfile3) uniform3) :=
  ⟨cycleProfile3_isStrictLinearOrderProfile,
    linearProfile3_isStrictLinearOrderProfile,
    cycleProfile3_normalizedStrictMargin,
    linearProfile3_normalizedStrictMargin,
    cycleProfile3_paperNormalizedMargin,
    linearProfile3_paperNormalizedMargin,
    uniform3_fullSupport,
    selectedNLHF_profile_commutativity_violation hτ⟩

end Commutativity

section RTBTExtension

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The RTBT-extension footnote: a top component exists, is strongly
connected, has no incoming edges, and its BT fit gives the extended lottery
with exactly that support. -/
theorem RTBT_extension (β : ℝ) {ρ : α → ℝ} (hρ : ∀ x, 0 < ρ x)
    {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (hpair : HasStrictComparisonEachPair c) :
    let π := extendedRTBT β ρ c hc (Or.inr hpair)
    (fordTopComponent c).Nonempty ∧
      FordStronglyConnected (fordTopCount c) ∧
      (∀ x ∉ fordTopComponent c, ∀ y ∈ fordTopComponent c, ¬ fordCountEdge c x y) ∧
      IsLottery π ∧ IsTopComponentRTBT β c ρ π ∧
      (∀ x, 0 < π x ↔ x ∈ fordTopComponent c) ∧
      (∀ x ∉ fordTopComponent c, π x = 0) :=
  ⟨fordTopComponent_nonempty hpair, fordTopCount_stronglyConnected c,
    fun _ hx _ hy => fordTopComponent_no_incoming hx hy,
    extendedRTBT_isLottery β hρ hc _, topComponentRTBT_certificate β ρ hc _,
    fun x => topComponentRTBT_pos_iff β hρ hc _ x,
    fun _ hx => topComponentRTBT_zero_outside β ρ hc _ hx⟩

/-- The construction is an extension on the entire original connected
domain, including connected profiles with missing pairwise comparisons. -/
theorem RTBT_extension_agrees (β : ℝ) (ρ : α → ℝ)
    {c : α → α → ℝ} (hc : IsFordCountMatrix c) (hdom : RTBTExtensionDomain c)
    (hconn : FordStronglyConnected c) :
    extendedRTBT β ρ c hc hdom =
      RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite c hc hconn) :=
  extendedRTBT_agrees β ρ hc hdom hconn

/-- The footnote includes every finite linear-order profile with at least
one voter, using the strict part of the paper's weak relation. -/
theorem RTBT_extension_linear_domain
    {V : Type*} [Fintype V] [Nonempty V] {R : V → α → α → Bool}
    (hR : IsLinearOrderProfile R) :
    RTBTExtensionDomain (strictCount (strictPart R)) :=
  Or.inr (hasStrictComparisonEachPair_of_linearProfile hR)

/-- Singleton top components give the point mass without a special case in
the construction. -/
theorem RTBT_extension_singleton (β : ℝ) {ρ : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (hdom : RTBTExtensionDomain c) {x : α}
    (hsingle : fordTopComponent c = {x}) :
    extendedRTBT β ρ c hc hdom = fun y => if y = x then 1 else 0 :=
  topComponentRTBT_singleton β hρ hc _ hsingle

end RTBTExtension

end PaperStatements
end PaperFormalization
