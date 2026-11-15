import PaperFormalization.WeakProfileBorda

open scoped BigOperators

namespace PaperFormalization

variable {α V : Type*}

/-! # Lemma `profile-margin-reduction`

The paper (`paper/main.tex`, "Formal framework") normalizes the pairwise
margin of a profile `𝐑` of *reflexive binary relations* by the number
`t_{x,y}(𝐑) = w_{x,y}(𝐑) + i_{x,y}(𝐑)` of voters who compare `x` and `y` at
all, with the convention `m̄_{x,y} = 0` when `t_{x,y} = 0`:

`m̄_{x,y}(𝐑) = (c_{x,y}(𝐑) − c_{y,x}(𝐑)) / t_{x,y}(𝐑)`.

`paperNormalizedMargin` (`WeakProfileBorda.lean`) is exactly this matrix.  On
profiles of linear orders it agrees with the `|V|`-normalized
`normalizedStrictMargin` used elsewhere, but on profiles with indifference or
noncomparability the two genuinely differ, and it is the pair-specific
normalization that the paper's monotonicity theorem uses.

This module proves that `m̄` is a normalized margin matrix, and that the
paper's profile-level improvement conditions (i)–(iii)
(`IsWeakProfileImprovement`) induce the matrix-level improvement relation
`IsImprovementOf` on `m̄`.  That is the paper's Lemma
`profile-margin-reduction`; combined with the matrix-level monotonicity
theorem (whose proof already contains the decomposition of a margin
improvement into one-pair improvements) it yields probabilistic monotonicity
over *actual profiles* for `τ ≥ 3/8`. -/

/-! ## Elementary count facts -/

section Counts

variable [Fintype V]

lemma strictPrefCount_nonneg (R : V → α → α → Bool) (x y : α) :
    0 ≤ strictPrefCount R x y := by
  unfold strictPrefCount
  exact Finset.sum_nonneg fun i _ => prefIndicator_nonneg _

lemma indiffCount_nonneg (R : V → α → α → Bool) (x y : α) :
    0 ≤ indiffCount R x y := by
  unfold indiffCount
  exact Finset.sum_nonneg fun i _ => prefIndicator_nonneg _

lemma comparedCount_nonneg (R : V → α → α → Bool) (x y : α) :
    0 ≤ comparedCount R x y := by
  unfold comparedCount strictComparedCount
  have h1 := strictPrefCount_nonneg R x y
  have h2 := strictPrefCount_nonneg R y x
  have h3 := indiffCount_nonneg R x y
  linarith

lemma indiffRel_symm (p : α → α → Bool) (x y : α) :
    indiffRel p y x = indiffRel p x y := by
  unfold indiffRel
  exact Bool.and_comm _ _

lemma indiffCount_symm (R : V → α → α → Bool) (x y : α) :
    indiffCount R y x = indiffCount R x y := by
  unfold indiffCount
  exact Finset.sum_congr rfl fun i _ => by rw [indiffRel_symm]

lemma strictComparedCount_symm (R : V → α → α → Bool) (x y : α) :
    strictComparedCount R y x = strictComparedCount R x y := by
  unfold strictComparedCount
  ring

lemma comparedCount_symm (R : V → α → α → Bool) (x y : α) :
    comparedCount R y x = comparedCount R x y := by
  unfold comparedCount
  rw [strictComparedCount_symm, indiffCount_symm]

/-- The pairwise margin numerator, written as a single voter sum. -/
lemma strictPrefCount_sub_eq_sum (R : V → α → α → Bool) (x y : α) :
    strictPrefCount R x y - strictPrefCount R y x =
      Finset.univ.sum (fun i : V =>
        prefIndicator (strictPrefRel (R i) x y) -
          prefIndicator (strictPrefRel (R i) y x)) := by
  unfold strictPrefCount
  rw [Finset.sum_sub_distrib]

/-- `t_{x,y}`, written as a single voter sum. -/
lemma comparedCount_eq_sum (R : V → α → α → Bool) (x y : α) :
    comparedCount R x y =
      Finset.univ.sum (fun i : V =>
        prefIndicator (strictPrefRel (R i) x y) +
          prefIndicator (strictPrefRel (R i) y x) +
          prefIndicator (indiffRel (R i) x y)) := by
  unfold comparedCount strictComparedCount strictPrefCount indiffCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

lemma strictPrefCount_self_eq_zero (R : V → α → α → Bool) (x : α) :
    strictPrefCount R x x = 0 := by
  unfold strictPrefCount
  refine Finset.sum_eq_zero ?_
  intro i _hi
  unfold strictPrefRel prefIndicator
  cases hp : R i x x <;> simp [hp]

/-- `|m_{x,y}| ≤ t_{x,y}`: the unnormalized margin never exceeds the number
of voters who compare the pair. -/
lemma abs_strictPrefCount_sub_le_comparedCount
    (R : V → α → α → Bool) (x y : α) :
    |strictPrefCount R x y - strictPrefCount R y x| ≤ comparedCount R x y := by
  have h1 := strictPrefCount_nonneg R x y
  have h2 := strictPrefCount_nonneg R y x
  have h3 := indiffCount_nonneg R x y
  have ht : comparedCount R x y =
      strictPrefCount R x y + strictPrefCount R y x + indiffCount R x y := by
    unfold comparedCount strictComparedCount
    ring
  rw [abs_le, ht]
  constructor <;> linarith

end Counts

/-! ## `m̄` is a normalized margin matrix -/

theorem paperNormalizedMargin_isNormalizedMarginMatrix
    [Fintype α] [DecidableEq α] [Fintype V] (R : V → α → α → Bool) :
    IsNormalizedMarginMatrix (paperNormalizedMargin R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    unfold paperNormalizedMargin
    rw [strictPrefCount_self_eq_zero]
    split_ifs <;> simp
  · intro x y
    unfold paperNormalizedMargin
    rw [comparedCount_symm]
    by_cases ht : comparedCount R x y = 0
    · simp [ht]
    · rw [if_neg ht, if_neg ht, ← neg_div]
      ring_nf
  · intro x y
    unfold paperNormalizedMargin
    by_cases ht : comparedCount R x y = 0
    · simp [ht]
    · rw [if_neg ht]
      have htpos : 0 < comparedCount R x y :=
        lt_of_le_of_ne (comparedCount_nonneg R x y) (Ne.symm ht)
      rw [abs_div, abs_of_pos htpos, div_le_one htpos]
      exact abs_strictPrefCount_sub_le_comparedCount R x y

/-! ## Voterwise consequences of the paper's conditions (i)–(iii) -/

section VoterWise

variable {R R' : V → α → α → Bool} {x : α}

/-- Voterwise form of "the margin numerator weakly increases". -/
lemma voter_margin_num_le_of_improvement
    (h : IsWeakProfileImprovement R R' x) (i : V) {y : α} (hyx : y ≠ x) :
    prefIndicator (strictPrefRel (R i) x y) -
        prefIndicator (strictPrefRel (R i) y x) ≤
      prefIndicator (strictPrefRel (R' i) x y) -
        prefIndicator (strictPrefRel (R' i) y x) := by
  have h1 := h.1 i y hyx
  have h2 := h.2.1 i y hyx
  unfold strictPrefRel prefIndicator
  cases hP : R i x y <;> cases hQ : R i y x <;>
    cases hP' : R' i x y <;> cases hQ' : R' i y x <;>
      simp_all <;> norm_num

/-- Voterwise form of "numerator plus denominator weakly increases". -/
lemma voter_margin_num_add_compared_le_of_improvement
    (h : IsWeakProfileImprovement R R' x) (i : V) {y : α} (hyx : y ≠ x) :
    (prefIndicator (strictPrefRel (R i) x y) -
        prefIndicator (strictPrefRel (R i) y x)) +
        (prefIndicator (strictPrefRel (R i) x y) +
          prefIndicator (strictPrefRel (R i) y x) +
          prefIndicator (indiffRel (R i) x y)) ≤
      (prefIndicator (strictPrefRel (R' i) x y) -
        prefIndicator (strictPrefRel (R' i) y x)) +
        (prefIndicator (strictPrefRel (R' i) x y) +
          prefIndicator (strictPrefRel (R' i) y x) +
          prefIndicator (indiffRel (R' i) x y)) := by
  have h1 := h.1 i y hyx
  have h2 := h.2.1 i y hyx
  unfold strictPrefRel indiffRel prefIndicator
  cases hP : R i x y <;> cases hQ : R i y x <;>
    cases hP' : R' i x y <;> cases hQ' : R' i y x <;>
      simp_all <;> norm_num

/-- Voterwise form of "numerator minus denominator weakly increases". -/
lemma voter_margin_num_sub_compared_le_of_improvement
    (h : IsWeakProfileImprovement R R' x) (i : V) {y : α} (hyx : y ≠ x) :
    (prefIndicator (strictPrefRel (R i) x y) -
        prefIndicator (strictPrefRel (R i) y x)) -
        (prefIndicator (strictPrefRel (R i) x y) +
          prefIndicator (strictPrefRel (R i) y x) +
          prefIndicator (indiffRel (R i) x y)) ≤
      (prefIndicator (strictPrefRel (R' i) x y) -
        prefIndicator (strictPrefRel (R' i) y x)) -
        (prefIndicator (strictPrefRel (R' i) x y) +
          prefIndicator (strictPrefRel (R' i) y x) +
          prefIndicator (indiffRel (R' i) x y)) := by
  have h1 := h.1 i y hyx
  have h2 := h.2.1 i y hyx
  unfold strictPrefRel indiffRel prefIndicator
  cases hP : R i x y <;> cases hQ : R i y x <;>
    cases hP' : R' i x y <;> cases hQ' : R' i y x <;>
      simp_all <;> norm_num

end VoterWise

/-! ## Count-level consequences -/

section CountLevel

variable [Fintype V] {R R' : V → α → α → Bool} {x : α}

lemma margin_num_le_of_weakProfileImprovement
    (h : IsWeakProfileImprovement R R' x) {y : α} (hyx : y ≠ x) :
    strictPrefCount R x y - strictPrefCount R y x ≤
      strictPrefCount R' x y - strictPrefCount R' y x := by
  rw [strictPrefCount_sub_eq_sum, strictPrefCount_sub_eq_sum]
  exact Finset.sum_le_sum fun i _ =>
    voter_margin_num_le_of_improvement h i hyx

lemma margin_num_add_compared_le_of_weakProfileImprovement
    (h : IsWeakProfileImprovement R R' x) {y : α} (hyx : y ≠ x) :
    (strictPrefCount R x y - strictPrefCount R y x) + comparedCount R x y ≤
      (strictPrefCount R' x y - strictPrefCount R' y x) +
        comparedCount R' x y := by
  rw [strictPrefCount_sub_eq_sum, strictPrefCount_sub_eq_sum,
    comparedCount_eq_sum, comparedCount_eq_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    voter_margin_num_add_compared_le_of_improvement h i hyx

lemma margin_num_sub_compared_le_of_weakProfileImprovement
    (h : IsWeakProfileImprovement R R' x) {y : α} (hyx : y ≠ x) :
    (strictPrefCount R x y - strictPrefCount R y x) - comparedCount R x y ≤
      (strictPrefCount R' x y - strictPrefCount R' y x) -
        comparedCount R' x y := by
  rw [strictPrefCount_sub_eq_sum, strictPrefCount_sub_eq_sum,
    comparedCount_eq_sum, comparedCount_eq_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ =>
    voter_margin_num_sub_compared_le_of_improvement h i hyx

/-- Condition (iii): pairs avoiding `x` keep all four of their counts. -/
lemma strictPrefCount_other_eq_of_weakProfileImprovement
    (h : IsWeakProfileImprovement R R' x) {y z : α} (hyx : y ≠ x)
    (hzx : z ≠ x) :
    strictPrefCount R' y z = strictPrefCount R y z := by
  unfold strictPrefCount
  refine Finset.sum_congr rfl ?_
  intro i _hi
  unfold strictPrefRel
  rw [h.2.2 i y z hyx hzx, h.2.2 i z y hzx hyx]

lemma indiffCount_other_eq_of_weakProfileImprovement
    (h : IsWeakProfileImprovement R R' x) {y z : α} (hyx : y ≠ x)
    (hzx : z ≠ x) :
    indiffCount R' y z = indiffCount R y z := by
  unfold indiffCount
  refine Finset.sum_congr rfl ?_
  intro i _hi
  unfold indiffRel
  rw [h.2.2 i y z hyx hzx, h.2.2 i z y hzx hyx]

lemma comparedCount_other_eq_of_weakProfileImprovement
    (h : IsWeakProfileImprovement R R' x) {y z : α} (hyx : y ≠ x)
    (hzx : z ≠ x) :
    comparedCount R' y z = comparedCount R y z := by
  unfold comparedCount strictComparedCount
  rw [strictPrefCount_other_eq_of_weakProfileImprovement h hyx hzx,
    strictPrefCount_other_eq_of_weakProfileImprovement h hzx hyx,
    indiffCount_other_eq_of_weakProfileImprovement h hyx hzx]

theorem paperNormalizedMargin_other_eq_of_weakProfileImprovement
    (h : IsWeakProfileImprovement R R' x) {y z : α} (hyx : y ≠ x)
    (hzx : z ≠ x) :
    paperNormalizedMargin R' y z = paperNormalizedMargin R y z := by
  unfold paperNormalizedMargin
  rw [strictPrefCount_other_eq_of_weakProfileImprovement h hyx hzx,
    strictPrefCount_other_eq_of_weakProfileImprovement h hzx hyx,
    comparedCount_other_eq_of_weakProfileImprovement h hyx hzx]

end CountLevel

/-! ## The scalar core

Both the old and the new normalized margin are quotients `a/b` with `|a| ≤ b`
and `0 ≤ b`, under the `b = 0 ↦ 0` convention.  The three count inequalities
`a ≤ a'`, `a + b ≤ a' + b'`, `a − b ≤ a' − b'` (which say that the numerator
increases by at least the change in the denominator, in absolute value) force
the quotient to increase. -/

lemma ratio_mono_of_margin_bounds {a b a' b' : ℝ}
    (hb : 0 ≤ b) (hb' : 0 ≤ b') (hab : |a| ≤ b) (hab' : |a'| ≤ b')
    (h1 : a ≤ a') (h2 : a + b ≤ a' + b') (h3 : a - b ≤ a' - b') :
    (if b = 0 then (0 : ℝ) else a / b) ≤
      (if b' = 0 then (0 : ℝ) else a' / b') := by
  rcases abs_le.mp hab with ⟨hal, har⟩
  rcases abs_le.mp hab' with ⟨hal', har'⟩
  by_cases hb0 : b = 0
  · by_cases hb0' : b' = 0
    · rw [if_pos hb0, if_pos hb0']
    · rw [if_pos hb0, if_neg hb0']
      have hbpos' : 0 < b' := lt_of_le_of_ne hb' (Ne.symm hb0')
      have ha0 : a = 0 := by rw [hb0] at hal har; linarith
      have hanonneg : 0 ≤ a' := by linarith
      exact div_nonneg hanonneg hb'
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_cases hb0' : b' = 0
    · rw [if_neg hb0, if_pos hb0']
      have ha0' : a' = 0 := by rw [hb0'] at hal' har'; linarith
      have haneg : a ≤ 0 := by rw [hb0'] at h2; linarith
      have hnn : 0 ≤ (-a) / b := div_nonneg (by linarith) hb
      rw [neg_div] at hnn
      linarith
    · rw [if_neg hb0, if_neg hb0']
      have hbpos' : 0 < b' := lt_of_le_of_ne hb' (Ne.symm hb0')
      rw [div_le_div_iff₀ hbpos hbpos']
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ b + a)
          (by linarith : (0:ℝ) ≤ (a' - a) + (b - b')),
        mul_nonneg (by linarith : (0:ℝ) ≤ b - a)
          (by linarith : (0:ℝ) ≤ (a' - a) - (b - b'))]

/-! ## Lemma `profile-margin-reduction` -/

/-- The paper's improvement conditions (i)–(iii) on an actual profile of
reflexive binary relations induce the matrix-level improvement relation on
the paper's pair-normalized margin matrix `m̄`.  This is Lemma
`profile-margin-reduction` of `paper/main.tex`. -/
theorem paperNormalizedMargin_improvement_of_weakProfileImprovement
    [Fintype α] [DecidableEq α] [Fintype V]
    {R R' : V → α → α → Bool} {x : α}
    (h : IsWeakProfileImprovement R R' x) :
    IsImprovementOf (paperNormalizedMargin R) (paperNormalizedMargin R') x := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hyx
    unfold paperNormalizedMargin
    exact ratio_mono_of_margin_bounds
      (comparedCount_nonneg R x y) (comparedCount_nonneg R' x y)
      (abs_strictPrefCount_sub_le_comparedCount R x y)
      (abs_strictPrefCount_sub_le_comparedCount R' x y)
      (margin_num_le_of_weakProfileImprovement h hyx)
      (margin_num_add_compared_le_of_weakProfileImprovement h hyx)
      (margin_num_sub_compared_le_of_weakProfileImprovement h hyx)
  · intro y _hyx
    exact (paperNormalizedMargin_isNormalizedMarginMatrix R').2.1 x y
  · intro y z hyx hzx
    exact paperNormalizedMargin_other_eq_of_weakProfileImprovement h hyx hzx

/-! ## Transitive profiles

The paper's sharpness construction for the all-profiles clause uses voters
whose relations are transitive (but neither complete nor antisymmetric). -/

/-- Every voter's weak relation is transitive. -/
def IsTransitiveProfile (R : V → α → α → Bool) : Prop :=
  ∀ i a b c, R i a b = true → R i b c = true → R i a c = true

/-! ## The paper's normalized comparison probabilities `c̄`

`paper/main.tex` normalizes `c` alongside `m`:

`c̄_{x,y}(𝐑) = (c_{x,y}(𝐑) + ½ i_{x,y}(𝐑)) / t_{x,y}(𝐑)`, with `c̄ = ½` when
`t_{x,y}(𝐑) = 0`,

and the objective `Γ_τ` of Section `NLHFsection` is stated in terms of `c̄`.
Remark `NLHFreformulated` rests on the identity `m̄ = 2c̄ − 1`, which is proved
here at the profile level. -/

/-- The paper's `c̄_{x,y}(𝐑)`, with the `t_{x,y} = 0` convention `c̄ = ½`. -/
noncomputable def paperNormalizedCbar [Fintype V]
    (R : V → α → α → Bool) (x y : α) : ℝ :=
  if comparedCount R x y = 0 then 1 / 2
  else (strictPrefCount R x y + indiffCount R x y / 2) / comparedCount R x y

/-- Profile-level `m̄_{x,y} = 2 c̄_{x,y} − 1`: the premise of Remark
`NLHFreformulated` in `paper/main.tex`. -/
lemma paperNormalizedMargin_eq_two_mul_paperNormalizedCbar_sub_one
    [Fintype V] (R : V → α → α → Bool) (x y : α) :
    paperNormalizedMargin R x y = 2 * paperNormalizedCbar R x y - 1 := by
  unfold paperNormalizedMargin paperNormalizedCbar
  by_cases ht : comparedCount R x y = 0
  · rw [if_pos ht, if_pos ht]
    norm_num
  · rw [if_neg ht, if_neg ht]
    have htv : comparedCount R x y =
        strictPrefCount R x y + strictPrefCount R y x + indiffCount R x y := by
      unfold comparedCount strictComparedCount
      ring
    have hmul :
        2 * ((strictPrefCount R x y + indiffCount R x y / 2)
            / comparedCount R x y) =
          (2 * strictPrefCount R x y + indiffCount R x y)
            / comparedCount R x y := by
      rw [← mul_div_assoc]
      congr 1
      ring
    have hone : (1 : ℝ) = comparedCount R x y / comparedCount R x y :=
      (div_self ht).symm
    rw [hmul, hone, div_sub_div_same]
    congr 1
    rw [htv]
    ring

/-! ## Complete profiles

The pair-specific normalization `t_{x,y}` and the `|V|`-normalization used in
the Ford/NLHF developments agree exactly when every voter compares every pair
of distinct candidates, i.e. on *complete* profiles.  (This strictly
generalizes `paperNormalizedMargin_eq_normalizedStrictMargin_of_linearProfile`
in `WeakProfileBorda.lean`, which assumes linear orders: completeness allows
indifference and intransitivity.) -/

/-- Every voter compares every pair of distinct candidates. -/
def IsCompleteProfile (R : V → α → α → Bool) : Prop :=
  ∀ (i : V) (x y : α), x ≠ y → (R i x y = true ∨ R i y x = true)

/-- On complete profiles `t_{x,y}(𝐑) = |V|` for distinct `x`, `y`. -/
lemma comparedCount_eq_card_of_complete [Fintype V]
    {R : V → α → α → Bool} (h : IsCompleteProfile R)
    {x y : α} (hxy : x ≠ y) :
    comparedCount R x y = (Fintype.card V : ℝ) := by
  rw [comparedCount_eq_sum]
  have hone : ∀ i : V,
      prefIndicator (strictPrefRel (R i) x y) +
          prefIndicator (strictPrefRel (R i) y x) +
        prefIndicator (indiffRel (R i) x y) = 1 := by
    intro i
    rcases h i x y hxy with hxy' | hyx'
    · cases hb : R i y x <;>
        simp [prefIndicator, strictPrefRel, indiffRel, hxy', hb]
    · cases hb : R i x y <;>
        simp [prefIndicator, strictPrefRel, indiffRel, hyx', hb]
  rw [Finset.sum_congr rfl (fun i _ => hone i)]
  simp

/-- On complete profiles the paper's `t_{x,y}`-normalized margin `m̄` agrees
with the `|V|`-normalized strict margin of the profile's strict part.  This is
the exact scope of the `|V|`-normalized profile-level statements elsewhere in
the artifact. -/
theorem paperNormalizedMargin_eq_normalizedStrictMargin_strictPart_of_complete
    [Fintype α] [DecidableEq α] [Fintype V]
    {R : V → α → α → Bool} (h : IsCompleteProfile R) :
    paperNormalizedMargin R = normalizedStrictMargin (strictPart R) := by
  funext x y
  by_cases hxy : x = y
  · subst hxy
    unfold paperNormalizedMargin normalizedStrictMargin
    rw [strictMargin_self_eq_zero, strictPrefCount_self_eq_zero]
    simp
  · have hcard : comparedCount R x y = (Fintype.card V : ℝ) :=
      comparedCount_eq_card_of_complete h hxy
    unfold paperNormalizedMargin normalizedStrictMargin strictMargin
    rw [strictCount_strictPart, hcard]
    by_cases hV : (Fintype.card V : ℝ) = 0
    · rw [if_pos hV, hV, div_zero]
    · rw [if_neg hV]

end PaperFormalization
