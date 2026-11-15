import PaperFormalization.Axioms

open scoped BigOperators

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The inverse-temperature parameter used in the NLHF proofs. -/
noncomputable def nlhfLambda (τ : ℝ) : ℝ :=
  1 / (2 * τ)

omit [DecidableEq α] in
/-- Skew-symmetry lets the bilinear margin value switch the two lotteries at
the cost of a minus sign. -/
lemma marginValue_swap_eq_neg_of_skew
    {M : α → α → ℝ} (p q : α → ℝ)
    (hskew : ∀ x y : α, M y x = -M x y) :
    marginValue M p q = -marginValue M q p := by
  classical
  unfold marginValue
  rw [Finset.sum_comm]
  calc
    Finset.univ.sum (fun x =>
        Finset.univ.sum (fun y => p y * q x * M y x)) =
      Finset.univ.sum (fun x =>
        Finset.univ.sum (fun y => -(q x * p y * M x y))) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        refine Finset.sum_congr rfl ?_
        intro y _hy
        rw [hskew]
        ring
    _ = -Finset.univ.sum (fun x =>
        Finset.univ.sum (fun y => q x * p y * M x y)) := by
        simp [Finset.sum_neg_distrib]

/-- The NLHF selector supplies a fixed point for each normalized margin matrix
and full-support reference lottery.  This is the formal interface to the
cited existence/uniqueness theorem. -/
def IsNLHFFixedPointSelection
    {α : Type*} [Fintype α]
    (F : ℝ → MatrixRule α) : Prop :=
  ∀ {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ},
    0 < τ →
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ →
          IsNLHFFixedPoint τ M ρ (F τ M ρ)

/-- Existence of an NLHF fixed point for each normalized finite instance.
Together with `IsTheNLHF`, this yields `IsNLHFFixedPointSelection`. -/
def NLHFFixedPointExists
    {α : Type*} [Fintype α] : Prop :=
  ∀ {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ},
    0 < τ →
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ →
          ∃ π : α → ℝ, IsNLHFFixedPoint τ M ρ π

/-- The usual existence theorem plus the project-level uniqueness/selectability
statement `IsTheNLHF` gives the fixed-point selection interface. -/
theorem fixedPointSelection_of_exists_and_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α}
    (hexists : NLHFFixedPointExists (α := α))
    (hunique : IsTheNLHF F) :
    IsNLHFFixedPointSelection F := by
  intro τ M ρ hτpos hM hρ
  rcases hexists hτpos hM hρ with ⟨π, hπ⟩
  have hF : F τ M ρ = π := hunique hM hπ
  simpa [hF]

end PaperFormalization
