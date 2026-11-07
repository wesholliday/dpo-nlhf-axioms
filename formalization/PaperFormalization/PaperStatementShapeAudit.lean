import PaperFormalization.PaperStatements

open scoped Topology
open scoped BigOperators
open Filter

namespace PaperFormalization

/-!
Statement-shape audit for the paper-facing declarations.

These examples are intentionally redundant with `PaperStatements.lean`: their
purpose is to make `lake build` fail if a key paper-facing theorem is
accidentally weakened or shifted to a less faithful formulation.
-/

section Monotonicity

/-- `BTProp` is the paper's full proposition at the count level: for every
strongly connected finite Ford count matrix, a unique normalized
Bradley-Terry certificate (displayed equations, positive-maximizer ray,
uniqueness). -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasBTPropCertificate (fordPairTotal c) c u :=
  PaperStatements.BTProp hc hconn

/-- `BTProp_existence` remains the bare finite Ford/Zermelo existence
schema. -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] :
    FordZermeloBTTheorem α :=
  PaperStatements.BTProp_existence

/-- The profile-count `BTProp` wrapper keeps the unique normalized certificate
for strongly connected finite profiles. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      HasBTPropCertificate
        (fordPairTotal (strictCount R)) (strictCount R) u :=
  PaperStatements.BTProp_profile hR hconn

/-- `DPOasRTBT` stays at the finite Ford-count-matrix level. -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {β : ℝ} (hβ : 0 < β)
    {c : α → α → ℝ} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal c) c u ∧
        dpoArgmaxSet β c ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  PaperStatements.DPOasRTBT hβ hρ hc hconn

/-- The profile `DPOasRTBT` wrapper keeps the certificate-existential
singleton argmax statement. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
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
  PaperStatements.DPOasRTBT_profile hβ hρ hR hconn

/-- The selected-BT `DPOasRTBT` wrapper keeps the concrete Ford/Zermelo
selected RTBT lottery. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
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
  PaperStatements.DPOasRTBT_profile_selectedBT hβ hρ hR hconn

/-- The add-voter DPO wrapper stays at the finite-profile certificate level. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
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
  PaperStatements.DPOasRTBT_profile_addVoter hβ hρ hR hp hconn

/-- The selected-BT add-voter DPO wrapper keeps the concrete selected RTBT
lottery after adding a voter. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
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
  PaperStatements.DPOasRTBT_profile_addVoter_selectedBT
    hβ hρ hR hp hconn

/-- `Anderson` must be the unconditional result on the paper's native
relation-valued linear-order profiles, with the actual Ford/Zermelo selector,
uniform reference, strict-part counts, and strict-domination Borda score. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype V] [Nonempty V]
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
  PaperStatements.Anderson hβ hlinear hconn x y

/-- The closed-saddle `nlhf-existence` wrapper keeps uniqueness and the
diagonal conclusion. -/
example {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    (∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedClosedSaddle τ M ρ pq.1 pq.2) ∧
      ∀ p q : α → ℝ,
        IsNLHFRegularizedClosedSaddle τ M ρ p q → p = q :=
  PaperStatements.«nlhf-existence» hτ hM hρ

/-- The diagonal selected-lottery form of `nlhf-existence` remains exposed. -/
example {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ, IsNLHFRegularizedClosedSaddle τ M ρ π π :=
  PaperStatements.«nlhf-existence-diagonal» hτ hM hρ

/-- The fixed-point form of `nlhf-existence` remains exposed. -/
example {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ, IsNLHFFixedPoint τ M ρ π :=
  PaperStatements.«nlhf-existence-fixed-point» hτ hM hρ

/-- The `c̄`-form of `nlhf-existence` must be stated with the paper's own
`Γ_τ` objective (`IsNLHFGammaClosedSaddle` at `cbarOfMargin M`), keep the
diagonal conclusion, and carry Remark `NLHFreformulated` as an `iff` with the
`m̄`/`Γ̄_{2τ}` form. -/
example {α : Type*} [Fintype α]
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
  PaperStatements.«nlhf-existence-cbar» hτ hM hρ

/-- The profile-level `nlhf-existence` statement must use the paper's
*pair-specific* normalization `c̄_{x,y} = (c + ½ i)/t_{x,y}` of an actual
profile, not a `|V|`-normalized surrogate, and must record `m̄ = 2c̄ − 1`. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ) (R : V → α → α → Bool)
    (hρ : IsFullSupportLottery ρ) :
    (∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFGammaClosedSaddle τ (paperNormalizedCbar R) ρ pq.1 pq.2) ∧
      (∀ p q : α → ℝ,
        IsNLHFGammaClosedSaddle τ (paperNormalizedCbar R) ρ p q → p = q) ∧
      (∀ x y : α,
        paperNormalizedMargin R x y = 2 * paperNormalizedCbar R x y - 1) :=
  PaperStatements.«nlhf-existence-weak-profile» hτ R hρ

/-- `MaxLottProp` is the paper-shape two-conjunct statement about the actual
selected NLHF lotteries: a convergent subsequence exists (with maximal-lottery
limit), and the limit of every convergent subsequence is maximal. -/
example {α : Type*} [Fintype α]
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
  PaperStatements.MaxLottProp hτpos hτ hM hρ

/-- The abstract limiting saddle-inequality form is available as
`MaxLottProp_limit`. -/
example {α : Type*} [Fintype α]
    {M : α → α → ℝ} {π : α → ℝ} {πn : ℕ → α → ℝ}
    {τn : ℕ → ℝ} {ρ : α → ℝ}
    (hπlot : IsLottery π)
    (hρ : IsFullSupportLottery ρ)
    (hπn : ∀ x : α, Tendsto (fun n => πn n x) atTop (𝓝 (π x)))
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hsaddle : ∀ n : ℕ, ∀ ν : α → ℝ, IsLottery ν →
      2 * τn n * (KL (πn n) ρ - KL ν ρ) ≤ marginValue M (πn n) ν) :
    IsMaximalLottery M π :=
  PaperStatements.MaxLottProp_limit hπlot hρ hπn hτ hsaddle

/-- The theorem named `NLHFmono` must be the paper's statement: all three
clauses over actual finite relation-valued profiles related by the paper's
improvement conditions (i)-(iii), with the pair-normalized margin. -/
example {τ : ℝ} (hτ : 0 < τ) :
    (SelectedNLHFWeakProfileAllMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ) ∧
      (SelectedNLHFPaperWeakOrderImprovementMonotonicity τ ↔
        (1 : ℝ) / 8 ≤ τ) ∧
        (SelectedNLHFPaperLinearOrderImprovementMonotonicity τ ↔
          (1 : ℝ) / 8 ≤ τ) :=
  PaperStatements.NLHFmono hτ

/-- The analytic companion bundle keeps its matrix-level clause and its
single-block score-profile clauses, separately from `NLHFmono`. -/
example {τ : ℝ} (hτ : 0 < τ) :
    (SelectedNLHFAllProfileMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ) ∧
      (SelectedNLHFWeakOrderProfileMonotonicity τ ↔
        (1 : ℝ) / 8 ≤ τ) ∧
        (SelectedNLHFLinearOrderProfileMonotonicity τ ↔
          (1 : ℝ) / 8 ≤ τ) :=
  PaperStatements.NLHFmono_margin_score_bundle hτ

/-- The positive `1/8` profile clauses are exposed for actual finite profiles. -/
example {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFWeakOrderProfileMonotonicity τ ∧
      SelectedNLHFLinearOrderProfileMonotonicity τ :=
  PaperStatements.NLHFmono_actual_profile_positive_clauses hτge

/-- The low-temperature linear-order witness must be denominator-cleared to
actual finite profiles and include the exact singleton block-change equation. -/
example {τ : ℝ} (hτ : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
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
  PaperStatements.NLHFmono_actual_linear_profile_converse_witness hτ hτlt

/-- The all-profiles `3/8` clause must also be available over *actual finite
profiles* of reflexive binary relations, with the paper's pair-normalized
margins and the paper's improvement conditions (i)-(iii). -/
example {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFWeakProfileAllMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ :=
  PaperStatements.NLHFmono_profile_all hτ

/-- The low-temperature all-profiles witness must be an actual pair of finite
profiles of reflexive transitive relations over a common electorate, related
by the paper's improvement conditions (i)-(iii). -/
example {τ : ℝ} (hτ : 0 < τ) (hτlt : τ < (3 : ℝ) / 8) :
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
  PaperStatements.NLHFmono_actual_transitive_profile_converse_witness hτ hτlt

/-- Every finite paper-style weak-order profile must be represented exactly
by scores, including equality of the induced pair-normalized margins. -/
example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsWeakOrderProfile R) :
    ∃ score : V → α → ℝ,
      scoreWeakProfile score = R ∧
        paperNormalizedMargin R = scoreProfileMargin score :=
  PaperStatements.NLHFmono_finite_weak_order_score_representation hR

/-- The representation of a paper-style linear order must be tie-free. -/
example {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R) :
    ∃ score : V → α → ℝ,
      IsLinearScoreProfile score ∧
        scoreWeakProfile score = R ∧
          paperNormalizedMargin R = scoreProfileMargin score :=
  PaperStatements.NLHFmono_finite_linear_order_score_representation hR

/-- All three `NLHFmono` clauses must be available over actual finite
relation-valued profiles related by the paper's improvement conditions
(i)-(iii), not only over score-represented profiles or under a single uniform
block improvement of the margin matrix. -/
example {τ : ℝ} (hτ : 0 < τ) :
    (SelectedNLHFWeakProfileAllMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ) ∧
      (SelectedNLHFPaperWeakOrderImprovementMonotonicity τ ↔
        (1 : ℝ) / 8 ≤ τ) ∧
        (SelectedNLHFPaperLinearOrderImprovementMonotonicity τ ↔
          (1 : ℝ) / 8 ≤ τ) :=
  PaperStatements.NLHFmono_profile_improvements hτ

/-- The `1/8` converse witness must be a pair of actual finite linear-order
profiles on a common electorate, related by conditions (i)-(iii). -/
example {τ : ℝ} (hτ : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
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
  PaperStatements.NLHFmono_actual_linear_profile_voterwise_converse_witness
    hτ hτlt

end Monotonicity

section RTBT

/-- `RTBTPM` must stay at the Ford count-matrix level, with the Ford/Zermelo
selected Bradley-Terry strengths and no selector hypothesis: an unconditional
statement about the actual `RTBT_β` rule on the paper's domain. -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
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
  PaperStatements.RTBTPM hβ hc hc' hconn hconn' hρ himp

/-- The profile form of `RTBTPM` must quantify over weak-relation profiles
with the paper's improvement conditions (i)-(iii), computing the
Bradley-Terry strengths from the strict-preference counts. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
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
  PaperStatements.RTBTPM_profile hβ hconn hconn' hρ himp

end RTBT

section Involvement

/-- The paper-facing `PBPM` statement uses the paper's partial-Borda score
`B^p` on weak-relation profiles, with the paper's improvement conditions
(i)–(iii). -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R R' : V → α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (h : IsWeakProfileImprovement R R' x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
      proportionalBorda η ρ (partialBordaScoreP R') x :=
  PaperStatements.PBPM hη hρnonneg h

/-- The strict-domination (`B^d`) monotonicity statement appears under
its own name. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R R' : V → α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (h : IsProfileImprovement R R' x) :
    proportionalBorda η ρ (strictDominationBordaScore R) x ≤
      proportionalBorda η ρ (strictDominationBordaScore R') x :=
  PaperStatements.PBPM_strict hη hρnonneg h

end Involvement

section InvolvementStatements

/-- Positive proportional-Borda involvement is an add-top-voter profile
statement with the paper's `B^p` (added voter strictly first). -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pTop : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hcard : 2 ≤ Fintype.card α)
    (htop : RanksStrictlyTop pTop x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
      proportionalBorda η ρ
        (partialBordaScoreP (addVoterProfile R pTop)) x :=
  PaperStatements.PBPPI_positive hη hρnonneg hcard htop

/-- Negative proportional-Borda involvement is an add-bottom-voter profile
statement with the paper's `B^p`. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pBottom : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hbottom : RanksStrictlyBottom pBottom x) :
    proportionalBorda η ρ
        (partialBordaScoreP (addVoterProfile R pBottom)) x ≤
      proportionalBorda η ρ (partialBordaScoreP R) x :=
  PaperStatements.PBPPI_negative hη hρnonneg hbottom

/-- The bundled proportional-Borda involvement theorem keeps both directions,
with the paper's `B^p`. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
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
  PaperStatements.PBPPI hη hρnonneg hcard htop hbottom

/-- The strict-domination (`B^d`) involvement statements appear under
their own names. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pTop : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hcard : 2 ≤ Fintype.card α)
    (hasymmTop : IsAsymmetricPref pTop) (htop : RanksTop pTop x) :
    proportionalBorda η ρ (strictDominationBordaScore R) x ≤
      proportionalBorda η ρ
        (strictDominationBordaScore (addVoterProfile R pTop)) x :=
  PaperStatements.PBPPI_positive_strict hη hρnonneg hcard hasymmTop htop

example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {pBottom : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hasymmBottom : IsAsymmetricPref pBottom)
    (hbottom : RanksBottom pBottom x) :
    proportionalBorda η ρ
        (strictDominationBordaScore (addVoterProfile R pBottom)) x ≤
      proportionalBorda η ρ (strictDominationBordaScore R) x :=
  PaperStatements.PBPPI_negative_strict hη hρnonneg hasymmBottom hbottom

/-- The positive NLHF involvement violation carries a profile-level
witness predicate: an actual linear-order profile plus an added linear
voter with `RanksTop`, both read via normalized margin matrices. -/
example {τ : ℝ} (hτ : 0 < τ) :
    ViolatesPositiveInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsTopMargins :=
  PaperStatements.InvolveViolNLHF_positive hτ

/-- The negative NLHF involvement violation carries the profile-level
add-bottom-voter witness predicate. -/
example {τ : ℝ} (hτ : 0 < τ) :
    ViolatesNegativeInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsBottomMargins :=
  PaperStatements.InvolveViolNLHF_negative hτ

/-- The bundled NLHF involvement violation keeps positive and negative
violations, both with profile-level witness predicates. -/
example {τ : ℝ} (hτ : 0 < τ) :
    ViolatesPositiveInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsTopMargins ∧
      ViolatesNegativeInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsBottomMargins :=
  PaperStatements.InvolveViolNLHF hτ

private abbrev RTBTPositiveProfileViolationShape (β : ℝ) : Prop :=
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
                  (strictCount_isFordCountMatrix hR) hconnR) x

private abbrev RTBTNegativeProfileViolationShape (β : ℝ) : Prop :=
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
                  hconnPlus) x

/-- The positive RTBT involvement theorem must expose an actual strict-linear
profile, a literal added top-ranking voter, both Ford-domain certificates,
one shared full-support reference, and the actual selected-BT inequality. -/
example {β : ℝ} (hβ : 0 < β) :
    RTBTPositiveProfileViolationShape β :=
  PaperStatements.InvolveViolRTBT_positive hβ

/-- The negative half has the same direct profile content with an added
bottom-ranking voter and the reversed strict inequality. -/
example {β : ℝ} (hβ : 0 < β) :
    RTBTNegativeProfileViolationShape β :=
  PaperStatements.InvolveViolRTBT_negative hβ

/-- The bundled RTBT proposition retains both direct profile witnesses. -/
example {β : ℝ} (hβ : 0 < β) :
    RTBTPositiveProfileViolationShape β ∧
      RTBTNegativeProfileViolationShape β :=
  PaperStatements.InvolveViolRTBT hβ

end InvolvementStatements

section Commutativity

/-- `RTBTorder` states finite-profile commutativity for proportional Borda
with the paper's `B^p` on weak-relation profiles, and for
Ford/Zermelo-selected RTBT over the strict-preference counts. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
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
  PaperStatements.RTBTorder hβ hconnR hconnS hρ

/-- The strict-reading commutativity statement appears under its own
name. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
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
  PaperStatements.RTBTorder_strict hβ hR hS hconnR hconnS hρ

/-- The reusable algebraic engine remains available under an explicitly
abstract name. -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (η : ℝ) {β : ℝ} (hβ : 0 < β)
    (B : (α → α → ℝ) → α → ℝ)
    (P : (α → α → ℝ) → Prop) {BT : (α → α → ℝ) → α → ℝ}
    (hBTpos : ∀ M : α → α → ℝ, P M → ∀ x : α, 0 < BT M x) :
    SatisfiesCommutativityOn (fun _ ρ => IsLottery ρ)
        (fun M ρ => proportionalBorda η ρ (B M)) ∧
      SatisfiesCommutativityOn (fun M ρ => P M ∧ IsFullSupportLottery ρ)
        (fun M ρ => RTBTFromStrength β ρ (BT M)) :=
  PaperStatements.RTBTorder_domain_abstract η hβ B P hBTpos

/-- `RTBTorder_domain` must instantiate the paper's full commutativity
property—both closure clauses and the equation—with the actual partial-Borda
and selected-Ford RTBT profile rules.  It has no abstract `B`, `P`, or `BT`
arguments, and bundled profiles may have different electorate sizes. -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (η : ℝ) {β : ℝ} (hβ : 0 < β) :
    SatisfiesCommutativityOn
        (finiteProfileProportionalBordaDomain (α := α))
        (finiteProfileProportionalBordaRule (α := α) η) ∧
      SatisfiesCommutativityOn
        (finiteProfileRTBTDomain (α := α))
        (finiteProfileRTBTRule
          (FordZermeloBTTheorem_finite (α := α)) β) :=
  PaperStatements.RTBTorder_domain η hβ

/-- `NLHFcomm` keeps the concrete three-candidate selected-NLHF
non-commutativity statement. -/
example {τ : ℝ} (hτ : 0 < τ) :
    ViolatesCommutativity ((selectedNLHF (α := Fin 3)) τ) :=
  PaperStatements.NLHFcomm hτ

/-- `NLHFcomm_domain` must refute the paper's full commutativity property (the
one with the domain-closure clauses) on `NLHF_τ`'s own domain. -/
example {τ : ℝ} (hτ : 0 < τ) :
    ViolatesCommutativityOn
      (fun (M : Fin 3 → Fin 3 → ℝ) (ρ : Fin 3 → ℝ) =>
        IsNormalizedMarginMatrix M ∧ IsFullSupportLottery ρ)
      ((selectedNLHF (α := Fin 3)) τ) :=
  PaperStatements.NLHFcomm_domain hτ

/-- `NLHFcomm_profile_witness` realizes the commutativity-violation
witnesses by the paper's actual linear-order profiles, with linearity
certificates, both margin normalizations, and the uniform reference. -/
example {τ : ℝ} (hτ : 0 < τ) :
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
  PaperStatements.NLHFcomm_profile_witness hτ

end Commutativity

section RevisedBordaDefinition

/-- Protect the count-level specification, not only theorem names that could
silently continue to compile after an incorrect score-definition change. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (x : α) :
    partialBordaScoreP R x =
      Finset.sum (Finset.univ.erase x) (fun y =>
        strictPrefCount R x y + indiffCount R x y / 2 + noCompCount R x y / 2) :=
  partialBordaScoreP_eq_counts R x

/-- A single incomplete ballot a > b, with c incomparable to both, gives
(3/2, 1/2, 1), rather than the old (1, 0, 0). The diagonal is reflexive. -/
example :
    partialBordaScoreP
      (fun (_ : Fin 1) =>
        ![![true, true, false], ![false, true, false], ![false, false, true]]) =
        ![(3 / 2 : ℝ), 1 / 2, 1] := by
  funext x
  fin_cases x <;>
    norm_num [partialBordaScoreP, relCredit, Fin.sum_univ_succ]

/-- The revised score retains a raw-margin representation even when some
comparisons are unexpressed. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (x : α) :
    2 * partialBordaScoreP R x =
      Finset.sum (Finset.univ.erase x) (fun y => strictPrefCount R x y - strictPrefCount R y x) +
        ((Fintype.card α : ℝ) - 1) * (Fintype.card V : ℝ) :=
  two_mul_partialBordaScoreP R x

end RevisedBordaDefinition

section CameraReadyAlignment

/-- The variational lemma must accept arbitrary lotteries, without a
full-support hypothesis on the competitor. -/
example {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ) (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) (r : α → ℝ) (hr : IsLottery r) :
    marginValue M r (selectedNLHF τ M ρ) - (1 / nlhfLambda τ) * KL r ρ ≤
      marginValue M (selectedNLHF τ M ρ) (selectedNLHF τ M ρ) -
        (1 / nlhfLambda τ) * KL (selectedNLHF τ M ρ) ρ :=
  PaperStatements.«nlhf-variational» hτ hM hρ r hr

/-- The extension must construct a BT fit on the top component and assign
zero elsewhere; existence of some arbitrary lottery would not suffice. -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (β : ℝ) {ρ : α → ℝ} (hρ : ∀ x, 0 < ρ x)
    {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (hpair : HasStrictComparisonEachPair c) :
    let π := extendedRTBT β ρ c hc (Or.inr hpair)
    (fordTopComponent c).Nonempty ∧
      FordStronglyConnected (fordTopCount c) ∧
      (∀ x ∉ fordTopComponent c, ∀ y ∈ fordTopComponent c, ¬ fordCountEdge c x y) ∧
      IsLottery π ∧ IsTopComponentRTBT β c ρ π ∧
      (∀ x, 0 < π x ↔ x ∈ fordTopComponent c) ∧
      (∀ x ∉ fordTopComponent c, π x = 0) :=
  PaperStatements.RTBT_extension β hρ hc hpair

/-- Agreement is required even on connected graphs that are not complete. -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (β : ℝ) (ρ : α → ℝ) {c : α → α → ℝ}
    (hc : IsFordCountMatrix c) (hconn : FordStronglyConnected c) :
    extendedRTBT β ρ c hc (Or.inl hconn) =
      RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite c hc hconn) :=
  PaperStatements.RTBT_extension_agrees β ρ hc (Or.inl hconn) hconn

example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype V] [Nonempty V] {R : V → α → α → Bool}
    (hR : IsLinearOrderProfile R) :
    RTBTExtensionDomain (strictCount (strictPart R)) :=
  PaperStatements.RTBT_extension_linear_domain hR

example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (β : ℝ) {ρ : α → ℝ} (hρ : ∀ x, 0 < ρ x)
    {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (hdom : RTBTExtensionDomain c) {x : α}
    (hsingle : fordTopComponent c = {x}) :
    extendedRTBT β ρ c hc hdom = fun y => if y = x then 1 else 0 :=
  PaperStatements.RTBT_extension_singleton β hρ hc hdom hsingle

end CameraReadyAlignment

section IPO

/-- The Borda-IPO definition uses exactly the paper's ordered-pair squares
and actual partial-Borda scores, including missing-comparison credit. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (η : ℝ) (R : V → α → α → Bool) (ρ π : α → ℝ) :
    bordaIPOObjective η R ρ π =
      ∑ x : α, ∑ y ∈ Finset.univ.erase x,
        (Real.log (π x / ρ x) - Real.log (π y / ρ y) -
          η * (partialBordaScoreP R x - partialBordaScoreP R y)) ^ 2 := rfl

/-- IPO uses the paper-normalized preference frequencies, not a surrogate
matrix supplied through a theorem-valued assumption. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (τ : ℝ) (R : V → α → α → Bool) (ρ π : α → ℝ) :
    offlineIPOObjective τ R ρ π =
      ∑ x : α, ∑ y ∈ Finset.univ.erase x,
        (Real.log (π x / ρ x) - Real.log (π y / ρ y) -
          paperNormalizedCbar R x y / τ) ^ 2 := rfl

/-- Singleton argmin sets assert both existence and uniqueness on exactly
the full-support lottery domain. -/
example {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (L : (α → ℝ) → ℝ) (π : α → ℝ) :
    π ∈ fullSupportArgminSet L ↔
      IsFullSupportLottery π ∧
        ∀ q : α → ℝ, IsFullSupportLottery q → L π ≤ L q := Iff.rfl

example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} (hη : 0 < η) (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (bordaIPOObjective η R ρ) =
        ({proportionalBorda η ρ (partialBordaScoreP R)} : Set (α → ℝ)) ∧
      bordaIPOObjective η R ρ (proportionalBorda η ρ (partialBordaScoreP R)) = 0 :=
  PaperStatements.BIPOandPB hη R hρ

example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype V] [Nonempty V]
    {τ : ℝ} (hτ : 0 < τ)
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (offlineIPOObjective τ R ρ) =
      ({proportionalBorda
        (1 / (τ * (Fintype.card α : ℝ) * (Fintype.card V : ℝ)))
        ρ (partialBordaScoreP R)} : Set (α → ℝ)) :=
  PaperStatements.IPOandPB hτ hR hρ

/-- The population-IPO claim of Remark `IPOremark` keeps both conclusions:
equality of full-support minimizer sets with `IPO_τ`, and the PB singleton. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype V] [Nonempty V]
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
  PaperStatements.IPOremark_population hm hτ hR hρ

/-- The per-pair identity keeps the paper's displayed form: a log of a
fraction minus the scaled label, averaged over annotators. -/
example {α V : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype V] [Nonempty V]
    {τ : ℝ} {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ π : α → ℝ} (hρ : IsFullSupportLottery ρ) (hπ : IsFullSupportLottery π)
    {x y : α} (hxy : x ≠ y) :
    (∑ i : V, (Real.log (π x * ρ y / (π y * ρ x)) -
        voterPreferenceLabel R i x y / τ) ^ 2) / (Fintype.card V : ℝ) =
      (Real.log (π x / ρ x) - Real.log (π y / ρ y) -
          paperNormalizedCbar R x y / τ) ^ 2 +
        pairLabelVariance τ R x y :=
  PaperStatements.IPOremark_population_pair hR hρ hπ hxy

end IPO

end PaperFormalization
