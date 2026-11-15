import PaperFormalization.Axioms

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The formal assembly step for proposition `InvolveViol`: if each of NLHF and
RTBT has a positive-involvement counterexample and a negative-involvement
counterexample, then both violate both involvement axioms. -/
theorem InvolveViol_from_parts
    (NLHF RTBT : ℝ → MatrixRule α)
    (AddsTop AddsBottom :
      (α → α → ℝ) → (α → α → ℝ) → α → Prop)
    (hNLHFpos :
      ∀ τ : ℝ, 0 < τ →
        ViolatesPositiveInvolvement (NLHF τ) AddsTop)
    (hNLHFneg :
      ∀ τ : ℝ, 0 < τ →
        ViolatesNegativeInvolvement (NLHF τ) AddsBottom)
    (hRTBTpos :
      ∀ β : ℝ, 0 < β →
        ViolatesPositiveInvolvement (RTBT β) AddsTop)
    (hRTBTneg :
      ∀ β : ℝ, 0 < β →
        ViolatesNegativeInvolvement (RTBT β) AddsBottom) :
    (∀ τ : ℝ, 0 < τ →
        ViolatesPositiveInvolvement (NLHF τ) AddsTop ∧
          ViolatesNegativeInvolvement (NLHF τ) AddsBottom) ∧
      (∀ β : ℝ, 0 < β →
        ViolatesPositiveInvolvement (RTBT β) AddsTop ∧
          ViolatesNegativeInvolvement (RTBT β) AddsBottom) := by
  constructor
  · intro τ hτ
    exact ⟨hNLHFpos τ hτ, hNLHFneg τ hτ⟩
  · intro β hβ
    exact ⟨hRTBTpos β hβ, hRTBTneg β hβ⟩

end PaperFormalization
