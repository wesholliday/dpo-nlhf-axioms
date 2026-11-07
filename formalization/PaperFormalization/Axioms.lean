import PaperFormalization.Core

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A reference-dependent probabilistic voting rule, represented at the
normalized-margin-matrix level. -/
abbrev MatrixRule (α : Type*) := (α → α → ℝ) → (α → ℝ) → α → ℝ

/-- Matrix-level probabilistic monotonicity: improving `x` in the margin matrix
does not lower `x`'s output probability. -/
def SatisfiesProbabilisticMonotonicity
    (F : MatrixRule α) : Prop :=
  ∀ (M M' : α → α → ℝ) (ρ : α → ℝ) (x : α),
    IsNormalizedMarginMatrix M →
      IsNormalizedMarginMatrix M' →
        IsFullSupportLottery ρ →
          IsImprovementOf M M' x →
            F M ρ x ≤ F M' ρ x

/-- A rule violates probabilistic monotonicity if the above property fails. -/
def ViolatesProbabilisticMonotonicity
    (F : MatrixRule α) : Prop :=
  ¬ SatisfiesProbabilisticMonotonicity F

omit [DecidableEq α] in
/-- A single strict drop along a valid improvement is a monotonicity
counterexample. -/
theorem violatesProbabilisticMonotonicity_of_strict_drop
    {F : MatrixRule α}
    {M M' : α → α → ℝ} {ρ : α → ℝ} {x : α}
    (hM : IsNormalizedMarginMatrix M)
    (hM' : IsNormalizedMarginMatrix M')
    (hρ : IsFullSupportLottery ρ)
    (himp : IsImprovementOf M M' x)
    (hdrop : F M' ρ x < F M ρ x) :
    ViolatesProbabilisticMonotonicity F := by
  intro hmono
  exact not_lt_of_ge (hmono M M' ρ x hM hM' hρ himp) hdrop

/-- Commutativity for reference-dependent rules. -/
def SatisfiesCommutativity
    (F : MatrixRule α) : Prop :=
  ∀ (M N : α → α → ℝ) (ρ : α → ℝ),
    IsNormalizedMarginMatrix M →
      IsNormalizedMarginMatrix N →
        IsFullSupportLottery ρ →
          F N (F M ρ) = F M (F N ρ)

def ViolatesCommutativity
    (F : MatrixRule α) : Prop :=
  ¬ SatisfiesCommutativity F

/-- Positive involvement is expressed abstractly relative to a predicate
`AddsTop M M' x` saying that `M'` is obtained from `M` by adding a voter who
ranks `x` top. -/
def SatisfiesPositiveInvolvement
    (F : MatrixRule α)
    (AddsTop : (α → α → ℝ) → (α → α → ℝ) → α → Prop) : Prop :=
  ∀ (M M' : α → α → ℝ) (ρ : α → ℝ) (x : α),
    IsNormalizedMarginMatrix M →
      IsNormalizedMarginMatrix M' →
        IsFullSupportLottery ρ →
          AddsTop M M' x →
            F M ρ x ≤ F M' ρ x

/-- Negative involvement is expressed abstractly relative to a predicate
`AddsBottom M M' x` saying that `M'` is obtained from `M` by adding a voter who
ranks `x` bottom. -/
def SatisfiesNegativeInvolvement
    (F : MatrixRule α)
    (AddsBottom : (α → α → ℝ) → (α → α → ℝ) → α → Prop) : Prop :=
  ∀ (M M' : α → α → ℝ) (ρ : α → ℝ) (x : α),
    IsNormalizedMarginMatrix M →
      IsNormalizedMarginMatrix M' →
        IsFullSupportLottery ρ →
          AddsBottom M M' x →
            F M' ρ x ≤ F M ρ x

def ViolatesPositiveInvolvement
    (F : MatrixRule α)
    (AddsTop : (α → α → ℝ) → (α → α → ℝ) → α → Prop) : Prop :=
  ¬ SatisfiesPositiveInvolvement F AddsTop

def ViolatesNegativeInvolvement
    (F : MatrixRule α)
    (AddsBottom : (α → α → ℝ) → (α → α → ℝ) → α → Prop) : Prop :=
  ¬ SatisfiesNegativeInvolvement F AddsBottom

omit [DecidableEq α] in
/-- A violation of positive involvement transports to any larger
add-top-voter predicate. -/
theorem violatesPositiveInvolvement_of_subpredicate
    {F : MatrixRule α}
    {A A' : (α → α → ℝ) → (α → α → ℝ) → α → Prop}
    (hsub : ∀ M M' x, A M M' x → A' M M' x)
    (hviol : ViolatesPositiveInvolvement F A) :
    ViolatesPositiveInvolvement F A' := fun hsat =>
  hviol fun M M' ρ x hM hM' hρ hA =>
    hsat M M' ρ x hM hM' hρ (hsub M M' x hA)

omit [DecidableEq α] in
/-- A violation of negative involvement transports to any larger
add-bottom-voter predicate. -/
theorem violatesNegativeInvolvement_of_subpredicate
    {F : MatrixRule α}
    {A A' : (α → α → ℝ) → (α → α → ℝ) → α → Prop}
    (hsub : ∀ M M' x, A M M' x → A' M M' x)
    (hviol : ViolatesNegativeInvolvement F A) :
    ViolatesNegativeInvolvement F A' := fun hsat =>
  hviol fun M M' ρ x hM hM' hρ hA =>
    hsat M M' ρ x hM hM' hρ (hsub M M' x hA)

end PaperFormalization
