import Mathlib

open scoped BigOperators

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finitely supported lottery, represented as a real-valued function. -/
def IsLottery (π : α → ℝ) : Prop :=
  (∀ x : α, 0 ≤ π x) ∧ Finset.sum Finset.univ (fun x => π x) = 1

/-- A lottery with full support. -/
def IsFullSupportLottery (π : α → ℝ) : Prop :=
  (∀ x : α, 0 < π x) ∧ Finset.sum Finset.univ (fun x => π x) = 1

omit [DecidableEq α] in
lemma IsFullSupportLottery.toLottery {π : α → ℝ}
    (hπ : IsFullSupportLottery π) : IsLottery π :=
  ⟨fun x => (hπ.1 x).le, hπ.2⟩

omit [DecidableEq α] in
/-- A coordinate of a finite lottery is at most `1`. -/
lemma IsLottery.apply_le_one {π : α → ℝ} (hπ : IsLottery π) (x : α) :
    π x ≤ 1 := by
  have hxmem : x ∈ (Finset.univ : Finset α) := Finset.mem_univ x
  have hle :
      π x ≤ Finset.univ.sum (fun a : α => π a) :=
    Finset.single_le_sum (fun a _ha => hπ.1 a) hxmem
  simpa [hπ.2] using hle

omit [DecidableEq α] in
/-- The finite lottery simplex is closed in the product topology. -/
lemma isClosed_setOf_isLottery :
    IsClosed {π : α → ℝ | IsLottery π} := by
  have hnonneg :
      IsClosed {π : α → ℝ | ∀ x : α, 0 ≤ π x} := by
    simpa [Set.setOf_forall] using
      (isClosed_iInter
        (fun x : α =>
          isClosed_le continuous_const (continuous_apply x)))
  have hsum_cont :
      Continuous
        (fun π : α → ℝ => Finset.univ.sum (fun x : α => π x)) :=
    continuous_finset_sum Finset.univ
      (fun x _hx => continuous_apply x)
  have hsum :
      IsClosed
        {π : α → ℝ |
          Finset.univ.sum (fun x : α => π x) = 1} :=
    isClosed_eq hsum_cont continuous_const
  simpa [IsLottery, Set.setOf_and] using hnonneg.inter hsum

omit [DecidableEq α] in
/-- Compactness of the finite lottery simplex. -/
lemma isCompact_setOf_isLottery :
    IsCompact {π : α → ℝ | IsLottery π} := by
  let box : Set (α → ℝ) := Set.pi Set.univ (fun _ : α => Set.Icc (0 : ℝ) 1)
  have hbox : IsCompact box :=
    isCompact_univ_pi (fun _ : α => isCompact_Icc)
  have hclosed : IsClosed {π : α → ℝ | IsLottery π} :=
    isClosed_setOf_isLottery
  have hsubset : {π : α → ℝ | IsLottery π} ⊆ box := by
    intro π hπ x _hx
    exact ⟨hπ.1 x, hπ.apply_le_one x⟩
  exact hbox.of_isClosed_subset hclosed hsubset

/-- A normalized margin matrix as used for NLHF. -/
def IsNormalizedMarginMatrix (M : α → α → ℝ) : Prop :=
  (∀ x : α, M x x = 0) ∧
    (∀ x y : α, M y x = -M x y) ∧
      ∀ x y : α, |M x y| ≤ 1

/-- `M'` is obtained from `M` by improving candidate `x`. -/
def IsImprovementOf (M M' : α → α → ℝ) (x : α) : Prop :=
  (∀ y : α, y ≠ x → M x y ≤ M' x y) ∧
    (∀ y : α, y ≠ x → M' y x = -M' x y) ∧
      ∀ y z : α, y ≠ x → z ≠ x → M' y z = M y z

/-- Expected normalized margin of `x` against an opponent drawn from `π`. -/
noncomputable def expectedMargin (M : α → α → ℝ) (π : α → ℝ) (x : α) : ℝ :=
  Finset.sum Finset.univ (fun y => π y * M x y)

/-- Bilinear value of lottery `π` against lottery `ν` in the margin game. -/
noncomputable def marginValue (M : α → α → ℝ) (π ν : α → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun x =>
    Finset.sum Finset.univ (fun y => π x * ν y * M x y))

omit [DecidableEq α] in
lemma marginValue_self_eq_zero_of_skew
    {M : α → α → ℝ} (π : α → ℝ)
    (hskew : ∀ x y : α, M y x = -M x y) :
    marginValue M π π = 0 := by
  classical
  let S := marginValue M π π
  have hswap :
      S =
        Finset.sum Finset.univ (fun x =>
          Finset.sum Finset.univ (fun y => π y * π x * M y x)) := by
    unfold S marginValue
    rw [Finset.sum_comm]
  have hneg :
      Finset.sum Finset.univ (fun x =>
          Finset.sum Finset.univ (fun y => π y * π x * M y x)) =
        -S := by
    calc
      Finset.sum Finset.univ (fun x =>
          Finset.sum Finset.univ (fun y => π y * π x * M y x))
          =
        Finset.sum Finset.univ (fun x =>
          Finset.sum Finset.univ (fun y => -(π x * π y * M x y))) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hskew]
            ring
      _ = -S := by
            simp [S, marginValue, Finset.sum_neg_distrib]
  have hS : S = -S := hswap.trans hneg
  linarith

omit [DecidableEq α] in
lemma marginValue_self_eq_zero_of_normalized
    {M : α → α → ℝ} (π : α → ℝ)
    (hM : IsNormalizedMarginMatrix M) :
    marginValue M π π = 0 :=
  marginValue_self_eq_zero_of_skew π hM.2.1

/-- Margin-normalized maximal lotteries. -/
def IsMaximalLottery (M : α → α → ℝ) (π : α → ℝ) : Prop :=
  IsLottery π ∧ ∀ ν : α → ℝ, IsLottery ν → 0 ≤ marginValue M π ν

/-- KL divergence on a finite set, under the paper's full-support hypotheses. -/
noncomputable def KL (π ρ : α → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun x => π x * Real.log (π x / ρ x))

/-- The NLHF fixed-point characterization from Remark `nlhffixed`. -/
noncomputable def IsNLHFFixedPoint
    (τ : ℝ) (M : α → α → ℝ) (ρ π : α → ℝ) : Prop :=
  0 < τ ∧ IsFullSupportLottery ρ ∧ IsFullSupportLottery π ∧
    ∀ x : α,
      π x =
        ρ x * Real.exp (expectedMargin M π x / (2 * τ)) /
          Finset.sum Finset.univ
            (fun z => ρ z * Real.exp (expectedMargin M π z / (2 * τ)))

/-- Abstract uniqueness of the NLHF fixed point for a normalized finite
instance.  The paper only defines NLHF on normalized margin functions, so the
uniqueness/selectability interface is intentionally restricted to that
domain. -/
def IsTheNLHF
    (F : ℝ → (α → α → ℝ) → (α → ℝ) → α → ℝ) : Prop :=
  ∀ {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ},
    IsNormalizedMarginMatrix M →
      IsNLHFFixedPoint τ M ρ π →
      F τ M ρ = π

/-- A Bradley--Terry strength vector is represented by its equations: a
full-support lottery satisfying Ford's displayed equations with pair weights
`w`.  Existence and uniqueness for strongly connected count matrices are
proved in `FordZermelo.lean` (`FordZermeloBTTheorem_finite`,
`exists_unique_BTProp_certificate`); nothing is assumed. -/
def IsBTStrength
    (w c : α → α → ℝ) (u : α → ℝ) : Prop :=
  IsFullSupportLottery u ∧
    ∀ x : α,
      Finset.sum (Finset.univ.erase x)
        (fun y => w x y * (u x / (u x + u y))) =
          Finset.sum (Finset.univ.erase x) (fun y => c x y)

/-- The RTBT lottery generated by a BT strength vector. -/
noncomputable def RTBTFromStrength
    (β : ℝ) (ρ u : α → ℝ) : α → ℝ :=
  fun x =>
    ρ x * (u x) ^ (1 / β) /
      Finset.sum Finset.univ (fun z => ρ z * (u z) ^ (1 / β))

end PaperFormalization
