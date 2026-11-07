import PaperFormalization.ProportionalBorda
import PaperFormalization.RTBT

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Proposition `RTBTorder`, stated as the conjunction used in the paper:
proportional Borda is commutative, and RTBT is commutative once a positive
Bradley--Terry strength vector has been selected for each profile. -/
theorem RTBTorder_from_score_and_BT_selection
    (η : ℝ) {β : ℝ} (hβ : 0 < β)
    (B : (α → α → ℝ) → α → ℝ)
    (BT : (α → α → ℝ) → α → ℝ)
    (hBTpos : ∀ M : α → α → ℝ, ∀ x : α, 0 < BT M x) :
    SatisfiesCommutativity (fun M ρ => proportionalBorda η ρ (B M)) ∧
      SatisfiesCommutativity (fun M ρ => RTBTFromStrength β ρ (BT M)) :=
  ⟨proportionalBordaMatrixRule_commutative η B,
    RTBTorder_from_positive_BT_selection hβ hBTpos⟩

end PaperFormalization
