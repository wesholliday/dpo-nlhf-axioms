import PaperFormalization.NLHFExistence

open scoped BigOperators

namespace PaperFormalization

/-! # The paper's `Γ_τ` objective in `c̄` form, and Remark `NLHFreformulated`

`paper/main.tex` defines NLHF through the objective

`Γ_τ(𝐑,ρ)(π,π') = Σ_{x,y} π(x)π'(y) c̄_{x,y}(𝐑) − τ KL(π‖ρ) + τ KL(π'‖ρ)`

using the *normalized comparison probabilities* `c̄`, and Remark
`NLHFreformulated` observes that, because `m̄ = 2c̄ − 1` and
`Σ_{x,y} π(x)π'(y) = 1`, the saddle points of `Γ_τ` are exactly those of

`Γ̄_{2τ}(𝐑,ρ)(π,π') = Σ_{x,y} π(x)π'(y) m̄_{x,y}(𝐑) − 2τ KL(π‖ρ) + 2τ KL(π'‖ρ)`.

`NLHFExistence.lean` formalizes only the `m̄` form: `nlhfSionValue τ M ρ p q`
has regularization coefficient `1/nlhfLambda τ = 2τ`, so it *is* `Γ̄_{2τ}`.
This module supplies the missing `c̄` side: the matrix `c̄ = (1 + m̄)/2`, the
objective `Γ_τ`, the affine identity `Γ_τ(c̄) = ½ + ½ Γ̄_{2τ}(m̄)` on lotteries,
and hence Remark `NLHFreformulated` itself, as an `iff` between the two
closed-simplex saddle-point notions. -/

variable {α : Type*} [Fintype α]

/-- The paper's normalized comparison matrix `c̄` written in terms of the
normalized margin matrix `m̄`: `c̄_{x,y} = (1 + m̄_{x,y})/2`. -/
noncomputable def cbarOfMargin {α : Type*} (M : α → α → ℝ) : α → α → ℝ :=
  fun x y => (1 + M x y) / 2

/-- The identity `m̄ = 2c̄ − 1` of Remark `NLHFreformulated`, at matrix
level. -/
lemma two_mul_cbarOfMargin_sub_one {α : Type*} (M : α → α → ℝ) :
    (fun x y => 2 * cbarOfMargin M x y - 1) = M := by
  funext x y
  unfold cbarOfMargin
  ring

/-- `c̄_{x,y} + c̄_{y,x} = 1`, the paper's counterpart of Munos et al.'s
assumption `P(X ≻ Y) + P(Y ≻ X) = 1`. -/
lemma cbarOfMargin_add_swap {α : Type*} {M : α → α → ℝ}
    (hskew : ∀ x y : α, M y x = -M x y) (x y : α) :
    cbarOfMargin M x y + cbarOfMargin M y x = 1 := by
  unfold cbarOfMargin
  rw [hskew x y]
  ring

/-- The paper's `Γ_τ` objective, stated for an arbitrary comparison matrix
`C` (instantiated at `C = c̄`). -/
noncomputable def nlhfGammaValue [Fintype α]
    (τ : ℝ) (C : α → α → ℝ) (ρ p q : α → ℝ) : ℝ :=
  marginValue C p q - τ * KL p ρ + τ * KL q ρ

/-- `Σ_{x,y} p(x) q(y) = 1` for lotteries `p`, `q`. -/
lemma sum_sum_mul_eq_one_of_lottery {p q : α → ℝ}
    (hp : IsLottery p) (hq : IsLottery q) :
    Finset.sum Finset.univ
        (fun x => Finset.sum Finset.univ (fun y => p x * q y)) = 1 := by
  have hx : ∀ x : α, Finset.sum Finset.univ (fun y => p x * q y) = p x := by
    intro x
    rw [← Finset.mul_sum, hq.2, mul_one]
  rw [Finset.sum_congr rfl (fun x _ => hx x), hp.2]

/-- The bilinear part of `Γ_τ` in terms of the bilinear part of `Γ̄`:
`Σ π(x)π'(y) c̄_{x,y} = ½ + ½ Σ π(x)π'(y) m̄_{x,y}`, using
`Σ_{x,y} π(x)π'(y) = 1`. -/
lemma marginValue_cbarOfMargin {M : α → α → ℝ} {p q : α → ℝ}
    (hp : IsLottery p) (hq : IsLottery q) :
    marginValue (cbarOfMargin M) p q = 1 / 2 + marginValue M p q / 2 := by
  classical
  have hinner : ∀ x : α,
      Finset.sum Finset.univ (fun y => p x * q y * cbarOfMargin M x y) =
        (Finset.sum Finset.univ (fun y => p x * q y)) / 2 +
          (Finset.sum Finset.univ (fun y => p x * q y * M x y)) / 2 := by
    intro x
    have hterm : ∀ y : α,
        p x * q y * cbarOfMargin M x y =
          (p x * q y) / 2 + (p x * q y * M x y) / 2 := by
      intro y
      unfold cbarOfMargin
      ring
    calc
      Finset.sum Finset.univ (fun y => p x * q y * cbarOfMargin M x y)
        = Finset.sum Finset.univ
            (fun y => (p x * q y) / 2 + (p x * q y * M x y) / 2) :=
          Finset.sum_congr rfl (fun y _ => hterm y)
      _ = Finset.sum Finset.univ (fun y => (p x * q y) / 2) +
            Finset.sum Finset.univ (fun y => (p x * q y * M x y) / 2) :=
          Finset.sum_add_distrib
      _ = (Finset.sum Finset.univ (fun y => p x * q y)) / 2 +
            (Finset.sum Finset.univ (fun y => p x * q y * M x y)) / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_div]
  unfold marginValue
  calc
    Finset.sum Finset.univ (fun x =>
        Finset.sum Finset.univ (fun y => p x * q y * cbarOfMargin M x y))
      = Finset.sum Finset.univ (fun x =>
          (Finset.sum Finset.univ (fun y => p x * q y)) / 2 +
            (Finset.sum Finset.univ (fun y => p x * q y * M x y)) / 2) :=
        Finset.sum_congr rfl (fun x _ => hinner x)
    _ = Finset.sum Finset.univ (fun x =>
            (Finset.sum Finset.univ (fun y => p x * q y)) / 2) +
          Finset.sum Finset.univ (fun x =>
            (Finset.sum Finset.univ (fun y => p x * q y * M x y)) / 2) :=
        Finset.sum_add_distrib
    _ = (Finset.sum Finset.univ (fun x =>
            Finset.sum Finset.univ (fun y => p x * q y))) / 2 +
          (Finset.sum Finset.univ (fun x =>
            Finset.sum Finset.univ (fun y => p x * q y * M x y))) / 2 := by
        rw [← Finset.sum_div, ← Finset.sum_div]
    _ = 1 / 2 +
          (Finset.sum Finset.univ (fun x =>
            Finset.sum Finset.univ (fun y => p x * q y * M x y))) / 2 := by
        rw [sum_sum_mul_eq_one_of_lottery hp hq]

/-- `1 / nlhfLambda τ = 2τ`: `nlhfSionValue` really is the paper's `Γ̄_{2τ}`. -/
lemma one_div_nlhfLambda (τ : ℝ) : (1 : ℝ) / nlhfLambda τ = 2 * τ := by
  unfold nlhfLambda
  rw [one_div_one_div]

/-- The affine identity of Remark `NLHFreformulated`:
`Γ_τ(c̄)(π,π') = ½ + ½ Γ̄_{2τ}(m̄)(π,π')` on lotteries. -/
lemma nlhfGammaValue_cbar_eq {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hp : IsLottery p) (hq : IsLottery q) :
    nlhfGammaValue τ (cbarOfMargin M) ρ p q =
      1 / 2 + nlhfSionValue τ M ρ p q / 2 := by
  unfold nlhfGammaValue nlhfSionValue
  rw [marginValue_cbarOfMargin hp hq, one_div_nlhfLambda]
  ring

/-- A saddle point of the paper's `Γ_τ` on the closed simplex: exactly the
inequality chain `Γ_τ(μ,π') ≤ Γ_τ(π,π') ≤ Γ_τ(π,ν)` of Proposition
`nlhf-existence`. -/
def IsNLHFGammaClosedSaddle [Fintype α]
    (τ : ℝ) (C : α → α → ℝ) (ρ p q : α → ℝ) : Prop :=
  IsLottery p ∧ IsLottery q ∧
    (∀ r : α → ℝ, IsLottery r →
      nlhfGammaValue τ C ρ r q ≤ nlhfGammaValue τ C ρ p q) ∧
    (∀ s : α → ℝ, IsLottery s →
      nlhfGammaValue τ C ρ p q ≤ nlhfGammaValue τ C ρ p s)

/-- Remark `NLHFreformulated`: the saddle points of the paper's `Γ_τ`, taken
at `c̄ = (1 + m̄)/2`, are exactly the saddle points of `Γ̄_{2τ}` at `m̄`. -/
theorem gammaClosedSaddle_iff_regularizedClosedSaddle
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ} :
    IsNLHFGammaClosedSaddle τ (cbarOfMargin M) ρ p q ↔
      IsNLHFRegularizedClosedSaddle τ M ρ p q := by
  constructor
  · rintro ⟨hp, hq, hL, hR⟩
    refine ⟨hp, hq, fun r hr => ?_, fun s hs => ?_⟩
    · have h := hL r hr
      rw [nlhfGammaValue_cbar_eq hr hq, nlhfGammaValue_cbar_eq hp hq] at h
      linarith
    · have h := hR s hs
      rw [nlhfGammaValue_cbar_eq hp hq, nlhfGammaValue_cbar_eq hp hs] at h
      linarith
  · rintro ⟨hp, hq, hL, hR⟩
    refine ⟨hp, hq, fun r hr => ?_, fun s hs => ?_⟩
    · have h := hL r hr
      rw [nlhfGammaValue_cbar_eq hr hq, nlhfGammaValue_cbar_eq hp hq]
      linarith
    · have h := hR s hs
      rw [nlhfGammaValue_cbar_eq hp hq, nlhfGammaValue_cbar_eq hp hs]
      linarith

/-- Proposition `nlhf-existence` stated for the paper's own `Γ_τ` objective in
`c̄` form: a unique closed-simplex saddle pair, which is diagonal. -/
theorem exists_unique_nlhfGammaClosedSaddlePair
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFGammaClosedSaddle τ (cbarOfMargin M) ρ pq.1 pq.2 := by
  obtain ⟨pq, hpq, huniq⟩ :=
    exists_unique_nlhfRegularizedClosedSaddlePair hτ hM hρ
  refine ⟨pq, gammaClosedSaddle_iff_regularizedClosedSaddle.mpr hpq, ?_⟩
  intro rr hrr
  exact huniq rr (gammaClosedSaddle_iff_regularizedClosedSaddle.mp hrr)

/-- The diagonal conclusion `π_τ = π'_τ` for the paper's `Γ_τ` objective. -/
theorem gammaClosedSaddle_left_eq_right
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hsaddle : IsNLHFGammaClosedSaddle τ (cbarOfMargin M) ρ p q) :
    p = q :=
  regularizedClosedSaddle_left_eq_right hτ hM hρ
    (gammaClosedSaddle_iff_regularizedClosedSaddle.mp hsaddle)

end PaperFormalization
