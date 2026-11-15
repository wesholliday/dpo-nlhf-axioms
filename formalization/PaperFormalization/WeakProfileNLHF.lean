import PaperFormalization.WeakProfileMargin
import PaperFormalization.NLHFGammaForm
import PaperFormalization.ProfileNLHF

open scoped BigOperators

namespace PaperFormalization

/-! # NLHF over actual profiles, at the paper's pair-normalized margins

`ProfileNLHF.lean` instantiates the NLHF existence/uniqueness theorems at
`normalizedStrictMargin R`, which divides the strict margin by `|V|`.  The
paper divides by the pair-specific count `t_{x,y}(𝐑)` (`paper/main.tex`,
formal framework); the two agree exactly on complete profiles
(`paperNormalizedMargin_eq_normalizedStrictMargin_strictPart_of_complete`) but
differ in general.  This module twins the existence/selection wrappers at the
paper's `m̄` (`paperNormalizedMargin`), and connects the profile-level `c̄`
matrix to the matrix-level `cbarOfMargin` of Remark `NLHFreformulated`.

Note that `[Nonempty V]` is *not* needed here: the `m̄` bound `|m̄| ≤ 1` holds
for the empty electorate too, because of the `t = 0 ↦ 0` convention. -/

variable {α V : Type*}

/-- The paper's profile-level `c̄` matrix is `cbarOfMargin` of the paper's
profile-level `m̄` matrix: `c̄ = (1 + m̄)/2`.  This is what lets Remark
`NLHFreformulated` be applied to actual profiles. -/
theorem paperNormalizedCbar_eq_cbarOfMargin [Fintype V]
    (R : V → α → α → Bool) :
    paperNormalizedCbar R = cbarOfMargin (paperNormalizedMargin R) := by
  funext x y
  have h := paperNormalizedMargin_eq_two_mul_paperNormalizedCbar_sub_one R x y
  unfold cbarOfMargin
  rw [h]
  ring

/-! ## Existence and uniqueness at `m̄` -/

/-- Proposition `nlhf-existence`, fixed-point form, over an actual finite
profile read through the paper's pair-normalized margin `m̄`. -/
theorem exists_unique_nlhfFixedPoint_weakProfile
    [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} (hτ : 0 < τ) (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ, IsNLHFFixedPoint τ (paperNormalizedMargin R) ρ π :=
  exists_unique_nlhfFixedPoint hτ
    (paperNormalizedMargin_isNormalizedMarginMatrix R) hρ

/-- Proposition `nlhf-existence`, full-support saddle-pair form, at `m̄`. -/
theorem exists_unique_nlhfRegularizedSaddlePair_weakProfile
    [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} (hτ : 0 < τ) (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedSaddle τ (paperNormalizedMargin R) ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedSaddlePair hτ
    (paperNormalizedMargin_isNormalizedMarginMatrix R) hρ

/-- Proposition `nlhf-existence`, closed-simplex saddle-pair form, at `m̄`. -/
theorem exists_unique_nlhfRegularizedClosedSaddlePair_weakProfile
    [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} (hτ : 0 < τ) (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedClosedSaddle τ (paperNormalizedMargin R) ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedClosedSaddlePair hτ
    (paperNormalizedMargin_isNormalizedMarginMatrix R) hρ

/-- The selected NLHF rule is the NLHF fixed point of the paper's `m̄`. -/
theorem selectedNLHF_weakProfile_fixedPoint
    [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} (hτ : 0 < τ) (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    IsNLHFFixedPoint τ (paperNormalizedMargin R) ρ
      (selectedNLHF (α := α) τ (paperNormalizedMargin R) ρ) :=
  selectedNLHF_selection hτ
    (paperNormalizedMargin_isNormalizedMarginMatrix R) hρ

/-- The selected NLHF rule equals any `m̄`-level fixed point. -/
theorem selectedNLHF_weakProfile_eq_of_fixedPoint
    [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} {R : V → α → α → Bool} {ρ π : α → ℝ}
    (hπ : IsNLHFFixedPoint τ (paperNormalizedMargin R) ρ π) :
    selectedNLHF (α := α) τ (paperNormalizedMargin R) ρ = π :=
  selectedNLHF_eq_of_fixedPoint
    (paperNormalizedMargin_isNormalizedMarginMatrix R) hπ

/-! ## The paper's own `Γ_τ` objective over actual profiles -/

/-- Proposition `nlhf-existence` exactly as stated in `paper/main.tex`: for an
actual profile `𝐑` and reference `ρ ∈ Δ°`, the objective `Γ_τ(𝐑,ρ)` built
from the paper's `c̄_{x,y}(𝐑)` has a unique closed-simplex saddle pair. -/
theorem exists_unique_nlhfGammaClosedSaddlePair_weakProfile
    [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} (hτ : 0 < τ) (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFGammaClosedSaddle τ (paperNormalizedCbar R) ρ pq.1 pq.2 := by
  rw [paperNormalizedCbar_eq_cbarOfMargin]
  exact exists_unique_nlhfGammaClosedSaddlePair hτ
    (paperNormalizedMargin_isNormalizedMarginMatrix R) hρ

/-- The diagonal conclusion `π_τ = π'_τ` of Proposition `nlhf-existence`, for
the paper's `Γ_τ` over an actual profile. -/
theorem gammaClosedSaddle_weakProfile_left_eq_right
    [Fintype α] [DecidableEq α] [Fintype V]
    {τ : ℝ} (hτ : 0 < τ) (R : V → α → α → Bool)
    {ρ p q : α → ℝ} (hρ : IsFullSupportLottery ρ)
    (hsaddle : IsNLHFGammaClosedSaddle τ (paperNormalizedCbar R) ρ p q) :
    p = q := by
  rw [paperNormalizedCbar_eq_cbarOfMargin] at hsaddle
  exact gammaClosedSaddle_left_eq_right hτ
    (paperNormalizedMargin_isNormalizedMarginMatrix R) hρ hsaddle

end PaperFormalization
