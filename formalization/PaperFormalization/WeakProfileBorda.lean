import PaperFormalization.ProfileBorda
import PaperFormalization.ProfileFord

open scoped BigOperators

namespace PaperFormalization

variable {α V : Type*}

/-! # Weak-relation profiles: indifference vs. noncomparability

The camera-ready paper (Section "Formal framework") takes each voter's
preference relation `R_i` to be a *reflexive binary relation* on the
candidate set, from which it derives the strict preference relation
`P(R_i) = {(x,y) ∈ R_i | (y,x) ∉ R_i}` and the indifference relation
`I(R_i) = {(x,y) ∈ R_i | (y,x) ∈ R_i}`.  A pair related in neither direction
is left *noncomparable* by the voter.  This module mirrors that reading on
Boolean profiles: `R i x y = true` means `(x,y) ∈ R_i` (the weak relation).
All four states of an ordered pair `(x,y)` with `x ≠ y` are distinguishable:

* strict preference   : `R i x y = true`,  `R i y x = false`
* indifference        : `R i x y = true`,  `R i y x = true`
* reverse strict      : `R i x y = false`, `R i y x = true`
* no comparison       : `R i x y = false`, `R i y x = false`

`strictDominationBordaScore` reads profiles as strict relations and computes
the strict-domination score `B^d`.  The paper's partial-Borda score is
`B^p_x = Σ_{y≠x} (c_{x,y} + ½ i_{x,y} + ½ n_{x,y})`, formalized here as
`partialBordaScoreP`. -/

/-- Partial-Borda credit of `x` against `y` under a single weak relation `p`:
`1` for a strict win, `0` for a strict loss, and `½` for either expressed
indifference or no comparison — the voterwise summand of the paper's `B^p`. -/
noncomputable def relCredit (p : α → α → Bool) (x y : α) : ℝ :=
  if p x y then (if p y x then 1 / 2 else 1) else (if p y x then 0 else 1 / 2)

lemma relCredit_nonneg (p : α → α → Bool) (x y : α) :
    0 ≤ relCredit p x y := by
  unfold relCredit
  split_ifs <;> norm_num

lemma relCredit_le_one (p : α → α → Bool) (x y : α) :
    relCredit p x y ≤ 1 := by
  unfold relCredit
  split_ifs <;> norm_num

/-- `(x,y) ∈ P(R_i)` for a single relation: strict preference. -/
def strictPrefRel (p : α → α → Bool) (x y : α) : Bool :=
  p x y && !p y x

/-- `(x,y) ∈ I(R_i)` for a single relation: expressed indifference. -/
def indiffRel (p : α → α → Bool) (x y : α) : Bool :=
  p x y && p y x

/-- No comparison between `x` and `y` in a single relation. -/
def noCompRel (p : α → α → Bool) (x y : α) : Bool :=
  !p x y && !p y x

/-- The credit decomposes as `1·[strict] + ½·[indifferent] + ½·[missing]`. -/
lemma relCredit_eq_indicators (p : α → α → Bool) (x y : α) :
    relCredit p x y =
      prefIndicator (strictPrefRel p x y) +
        prefIndicator (indiffRel p x y) / 2 +
        prefIndicator (noCompRel p x y) / 2 := by
  unfold relCredit strictPrefRel indiffRel noCompRel prefIndicator
  cases hxy : p x y <;> cases hyx : p y x <;> simp

/-- A pair always distributes one Borda point, including missing comparisons. -/
lemma relCredit_add_reverse (p : α → α → Bool) (x y : α) :
    relCredit p x y + relCredit p y x = 1 := by
  unfold relCredit
  cases hxy : p x y <;> cases hyx : p y x <;> norm_num

/-- Missing comparisons contribute half a point, just like expressed ties. -/
lemma relCredit_of_no_comparison {p : α → α → Bool} {x y : α}
    (hxy : p x y = false) (hyx : p y x = false) :
    relCredit p x y = 1 / 2 := by
  simp [relCredit, hxy, hyx]

/-- The paper's profiles assign each voter a reflexive relation. -/
def IsReflexiveProfile (R : V → α → α → Bool) : Prop :=
  ∀ i x, R i x x = true

/-- `c_{x,y}(𝐑)`: the number of voters who strictly prefer `x` to `y`. -/
noncomputable def strictPrefCount [Fintype V]
    (R : V → α → α → Bool) (x y : α) : ℝ :=
  Finset.sum Finset.univ (fun i => prefIndicator (strictPrefRel (R i) x y))

/-- `i_{x,y}(𝐑)`: the number of voters expressing indifference. -/
noncomputable def indiffCount [Fintype V]
    (R : V → α → α → Bool) (x y : α) : ℝ :=
  Finset.sum Finset.univ (fun i => prefIndicator (indiffRel (R i) x y))

/-- `n_{x,y}(𝐑)`: the number of voters leaving the pair noncomparable. -/
noncomputable def noCompCount [Fintype V]
    (R : V → α → α → Bool) (x y : α) : ℝ :=
  Finset.sum Finset.univ (fun i => prefIndicator (noCompRel (R i) x y))

/-- The four disjoint comparison states exhaust the electorate. -/
lemma comparison_counts_partition [Fintype V]
    (R : V → α → α → Bool) (x y : α) :
    strictPrefCount R x y + strictPrefCount R y x +
      indiffCount R x y + noCompCount R x y = (Fintype.card V : ℝ) := by
  unfold strictPrefCount indiffCount noCompCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : V, (1 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      unfold strictPrefRel indiffRel noCompRel prefIndicator
      cases hxy : R i x y <;> cases hyx : R i y x <;> norm_num
    _ = _ := by simp

/-- `w_{x,y}(𝐑) = c_{x,y} + c_{y,x}`. -/
noncomputable def strictComparedCount [Fintype V]
    (R : V → α → α → Bool) (x y : α) : ℝ :=
  strictPrefCount R x y + strictPrefCount R y x

/-- `t_{x,y}(𝐑) = w_{x,y} + i_{x,y}`: the number of voters comparing `x`
and `y` at all. -/
noncomputable def comparedCount [Fintype V]
    (R : V → α → α → Bool) (x y : α) : ℝ :=
  strictComparedCount R x y + indiffCount R x y

/-- The paper's partial-Borda score
`B^p_x(𝐑) = Σ_{y ≠ x} (c_{x,y}(𝐑) + ½ i_{x,y}(𝐑) + ½ n_{x,y}(𝐑))`,
computed voterwise. -/
noncomputable def partialBordaScoreP
    [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (x : α) : ℝ :=
  Finset.sum Finset.univ (fun i =>
    Finset.sum (Finset.univ.erase x) (fun y => relCredit (R i) x y))

/-- `partialBordaScoreP` agrees with the paper's count-level formula. -/
lemma partialBordaScoreP_eq_counts
    [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (x : α) :
    partialBordaScoreP R x =
      Finset.sum (Finset.univ.erase x)
        (fun y => strictPrefCount R x y + indiffCount R x y / 2 +
          noCompCount R x y / 2) := by
  classical
  unfold partialBordaScoreP strictPrefCount indiffCount noCompCount
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y _hy
  simp_rw [Finset.sum_div]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact relCredit_eq_indicators (R i) x y

/-- Twice partial Borda is the sum of raw margins plus a candidate-independent
constant. This identity uses missing-comparison credit and holds on all profiles. -/
lemma two_mul_partialBordaScoreP
    [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (x : α) :
    2 * partialBordaScoreP R x =
      (∑ y ∈ Finset.univ.erase x, (strictPrefCount R x y - strictPrefCount R y x)) +
        ((Fintype.card α : ℝ) - 1) * (Fintype.card V : ℝ) := by
  rw [partialBordaScoreP_eq_counts, Finset.mul_sum]
  have hterm : ∀ y : α,
      2 * (strictPrefCount R x y + indiffCount R x y / 2 + noCompCount R x y / 2) =
        (strictPrefCount R x y - strictPrefCount R y x) + (Fintype.card V : ℝ) := by
    intro y
    have h := comparison_counts_partition R x y
    linarith
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hcard : ((Finset.univ.erase x : Finset α).card : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    rw [Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨x⟩), Nat.cast_one]
  rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-! ## Probabilistic monotonicity (Proposition `PBPM`)

The paper's improvement conditions (i)–(iii) (`main.tex`, probabilistic
monotonicity definition): for all voters `i` and `y, z ≠ x`,
(i) `(x,y) ∈ 𝐑_i` implies `(x,y) ∈ 𝐑⁺_i`;
(ii) `(y,x) ∉ 𝐑_i` implies `(y,x) ∉ 𝐑⁺_i`;
(iii) `(y,z) ∈ 𝐑⁺_i` iff `(y,z) ∈ 𝐑_i`. -/

def IsWeakProfileImprovement
    (R R' : V → α → α → Bool) (x : α) : Prop :=
  (∀ i y, y ≠ x → R i x y = true → R' i x y = true) ∧
    (∀ i y, y ≠ x → R i y x = false → R' i y x = false) ∧
      ∀ i y z, y ≠ x → z ≠ x → R' i y z = R i y z

/-- Under (i) and (ii), `x`'s credit against any `y ≠ x` weakly increases. -/
lemma relCredit_self_mono_of_improvement
    {R R' : V → α → α → Bool} {x : α}
    (h : IsWeakProfileImprovement R R' x) (i : V) {y : α} (hyx : y ≠ x) :
    relCredit (R i) x y ≤ relCredit (R' i) x y := by
  have h1 := h.1 i y hyx
  have h2 := h.2.1 i y hyx
  unfold relCredit
  cases hxy : R i x y <;> cases hyx' : R i y x <;>
    cases hxy' : R' i x y <;> cases hyx'' : R' i y x <;>
      simp_all <;> norm_num

/-- Under (i) and (ii), the credit of any `z ≠ x` against `x` weakly
decreases. -/
lemma relCredit_against_x_anti_of_improvement
    {R R' : V → α → α → Bool} {x : α}
    (h : IsWeakProfileImprovement R R' x) (i : V) {z : α} (hzx : z ≠ x) :
    relCredit (R' i) z x ≤ relCredit (R i) z x := by
  have h1 := h.1 i z hzx
  have h2 := h.2.1 i z hzx
  unfold relCredit
  cases hxz : R i x z <;> cases hzx' : R i z x <;>
    cases hxz' : R' i x z <;> cases hzx'' : R' i z x <;>
      simp_all <;> norm_num

lemma partialBordaScoreP_self_le_of_improvement
    [Fintype α] [DecidableEq α] [Fintype V]
    {R R' : V → α → α → Bool} {x : α}
    (h : IsWeakProfileImprovement R R' x) :
    partialBordaScoreP R x ≤ partialBordaScoreP R' x := by
  classical
  unfold partialBordaScoreP
  refine Finset.sum_le_sum ?_
  intro i _hi
  refine Finset.sum_le_sum ?_
  intro y hy
  exact relCredit_self_mono_of_improvement h i (Finset.mem_erase.mp hy).1

lemma partialBordaScoreP_other_le_of_improvement
    [Fintype α] [DecidableEq α] [Fintype V]
    {R R' : V → α → α → Bool} {x z : α}
    (h : IsWeakProfileImprovement R R' x) (hzx : z ≠ x) :
    partialBordaScoreP R' z ≤ partialBordaScoreP R z := by
  classical
  unfold partialBordaScoreP
  refine Finset.sum_le_sum ?_
  intro i _hi
  refine Finset.sum_le_sum ?_
  intro y hy
  by_cases hyx : y = x
  · subst y
    exact relCredit_against_x_anti_of_improvement h i hzx
  · have hzy := h.2.2 i z y hzx hyx
    have hyz := h.2.2 i y z hyx hzx
    unfold relCredit
    rw [hzy, hyz]

/-- The score-difference inequality feeding `PBPM_from_score_differences`,
for the paper's `B^p`. -/
theorem partialBordaScoreP_diff_le_of_improvement
    [Fintype α] [DecidableEq α] [Fintype V]
    {R R' : V → α → α → Bool} {x z : α}
    (h : IsWeakProfileImprovement R R' x) (hzx : z ≠ x) :
    partialBordaScoreP R' z - partialBordaScoreP R' x ≤
      partialBordaScoreP R z - partialBordaScoreP R x := by
  have hxle := partialBordaScoreP_self_le_of_improvement (V := V) h
  have hzle := partialBordaScoreP_other_le_of_improvement (V := V) h hzx
  linarith

/-- Proposition `PBPM` for the paper's `B^p` on weak-relation profiles. -/
theorem PBPM_weak_from_profile_improvement
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R R' : V → α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (h : IsWeakProfileImprovement R R' x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
      proportionalBorda η ρ (partialBordaScoreP R') x := by
  refine PBPM_from_score_differences hη hρnonneg hρx ?_
  intro z hzx
  exact partialBordaScoreP_diff_le_of_improvement (V := V) h hzx

/-! ## Involvement (Proposition `PBPPI`) -/

/-- The added voter ranks `x` uniquely first: strict preference for `x`
over every other candidate. -/
def RanksStrictlyTop (p : α → α → Bool) (x : α) : Prop :=
  ∀ y : α, y ≠ x → strictPrefRel p x y = true

/-- The added voter ranks `x` uniquely last. -/
def RanksStrictlyBottom (p : α → α → Bool) (x : α) : Prop :=
  ∀ y : α, y ≠ x → strictPrefRel p y x = true

/-- Partial-Borda contribution of one added voter under the weak reading. -/
noncomputable def singleVoterBordaP
    [Fintype α] [DecidableEq α] (p : α → α → Bool) (x : α) : ℝ :=
  Finset.sum (Finset.univ.erase x) (fun y => relCredit p x y)

lemma partialBordaScoreP_addVoterProfile
    [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (p : α → α → Bool) (x : α) :
    partialBordaScoreP (addVoterProfile R p) x =
      partialBordaScoreP R x + singleVoterBordaP p x := by
  classical
  unfold partialBordaScoreP singleVoterBordaP
  simp [addVoterProfile, add_comm]
  ring

lemma singleVoterBordaP_top_self
    [Fintype α] [DecidableEq α]
    {p : α → α → Bool} {x : α}
    (htop : RanksStrictlyTop p x) :
    singleVoterBordaP p x = (Fintype.card α : ℝ) - 1 := by
  classical
  unfold singleVoterBordaP
  calc
    Finset.sum (Finset.univ.erase x) (fun y => relCredit p x y)
        = Finset.sum (Finset.univ.erase x) (fun _ => (1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          have hs := htop y (Finset.mem_erase.mp hy).1
          unfold strictPrefRel at hs
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
          unfold relCredit
          simp [hs.1, hs.2]
    _ = ((Finset.univ.erase x).card : ℝ) := by simp
    _ = (Fintype.card α : ℝ) - 1 := by
          rw [Finset.cast_card_erase_of_mem (R := ℝ) (by simp)]
          simp

lemma singleVoterBordaP_top_other_le
    [Fintype α] [DecidableEq α]
    {p : α → α → Bool} {x z : α}
    (htop : RanksStrictlyTop p x) (hzx : z ≠ x) :
    singleVoterBordaP p z ≤ (Fintype.card α : ℝ) - 2 := by
  classical
  have hxmem : x ∈ (Finset.univ.erase z : Finset α) := by
    simp [hzx.symm]
  have hs := htop z hzx
  unfold strictPrefRel at hs
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
  have hzxcredit : relCredit p z x = 0 := by
    unfold relCredit
    simp [hs.1, hs.2]
  have hrestcard :
      (((Finset.univ.erase z).erase x).card : ℝ) =
        (Fintype.card α : ℝ) - 2 := by
    rw [Finset.cast_card_erase_of_mem (R := ℝ) hxmem]
    rw [Finset.cast_card_erase_of_mem (R := ℝ)
      (by simp : z ∈ (Finset.univ : Finset α))]
    simp
    ring
  unfold singleVoterBordaP
  calc
    Finset.sum (Finset.univ.erase z) (fun y => relCredit p z y)
        =
      relCredit p z x +
        Finset.sum ((Finset.univ.erase z).erase x)
          (fun y => relCredit p z y) := by
          rw [← Finset.add_sum_erase (s := Finset.univ.erase z)
            (f := fun y => relCredit p z y) hxmem]
    _ =
        Finset.sum ((Finset.univ.erase z).erase x)
          (fun y => relCredit p z y) := by
          rw [hzxcredit]; ring
    _ ≤
        Finset.sum ((Finset.univ.erase z).erase x) (fun _ => (1 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro y _hy
          exact relCredit_le_one p z y
    _ = (((Finset.univ.erase z).erase x).card : ℝ) := by simp
    _ = (Fintype.card α : ℝ) - 2 := hrestcard

lemma singleVoterBordaP_bottom_self
    [Fintype α] [DecidableEq α]
    {p : α → α → Bool} {x : α}
    (hbottom : RanksStrictlyBottom p x) :
    singleVoterBordaP p x = 0 := by
  classical
  unfold singleVoterBordaP
  refine Finset.sum_eq_zero ?_
  intro y hy
  have hs := hbottom y (Finset.mem_erase.mp hy).1
  unfold strictPrefRel at hs
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
  unfold relCredit
  simp [hs.1, hs.2]

lemma singleVoterBordaP_bottom_other_ge
    [Fintype α] [DecidableEq α]
    {p : α → α → Bool} {x z : α}
    (hbottom : RanksStrictlyBottom p x) (hzx : z ≠ x) :
    1 ≤ singleVoterBordaP p z := by
  classical
  have hxmem : x ∈ (Finset.univ.erase z : Finset α) := by
    simp [hzx.symm]
  have hs := hbottom z hzx
  unfold strictPrefRel at hs
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
  have hzxcredit : relCredit p z x = 1 := by
    unfold relCredit
    simp [hs.1, hs.2]
  unfold singleVoterBordaP
  calc
    (1 : ℝ) =
        relCredit p z x := hzxcredit.symm
    _ ≤
        relCredit p z x +
          Finset.sum ((Finset.univ.erase z).erase x)
            (fun y => relCredit p z y) := by
          have hrest_nonneg :
              0 ≤ Finset.sum ((Finset.univ.erase z).erase x)
                (fun y => relCredit p z y) := by
            refine Finset.sum_nonneg ?_
            intro y _hy
            exact relCredit_nonneg p z y
          linarith
    _ =
        Finset.sum (Finset.univ.erase z) (fun y => relCredit p z y) := by
          rw [← Finset.add_sum_erase (s := Finset.univ.erase z)
            (f := fun y => relCredit p z y) hxmem]

/-- Positive involvement for `PB^p`: adding a voter who ranks `x` uniquely
first cannot lower the probability of `x`. -/
theorem PBPPI_weak_from_added_top_profile
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hcard : 2 ≤ Fintype.card α)
    (htop : RanksStrictlyTop p x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
      proportionalBorda η ρ (partialBordaScoreP (addVoterProfile R p)) x := by
  have hscore :
      partialBordaScoreP (addVoterProfile R p) =
        fun z => partialBordaScoreP R z + singleVoterBordaP p z := by
    funext z
    exact partialBordaScoreP_addVoterProfile R p z
  rw [hscore]
  refine PBPPI_from_score_bounds hη hρnonneg hρx hcard ?_ ?_
  · rw [singleVoterBordaP_top_self htop]
  · intro z hzx
    have hz := singleVoterBordaP_top_other_le htop hzx
    linarith

/-- Negative involvement for `PB^p`: adding a voter who ranks `x` uniquely
last cannot raise the probability of `x`. -/
theorem PBPNI_weak_from_added_bottom_profile
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hbottom : RanksStrictlyBottom p x) :
    proportionalBorda η ρ (partialBordaScoreP (addVoterProfile R p)) x ≤
      proportionalBorda η ρ (partialBordaScoreP R) x := by
  have hscore :
      partialBordaScoreP (addVoterProfile R p) =
        fun z => partialBordaScoreP R z + singleVoterBordaP p z := by
    funext z
    exact partialBordaScoreP_addVoterProfile R p z
  rw [hscore]
  refine PBPNI_from_score_bounds hη hρnonneg hρx ?_ ?_
  · rw [singleVoterBordaP_bottom_self hbottom]
    ring
  · intro z hzx
    have hz := singleVoterBordaP_bottom_other_ge hbottom hzx
    linarith

/-! ## The paper's trivial `ρ(x) = 0` case for `PB^p`

`paper/main.tex` proves `PBPM` and `PBPPI` for every `ρ ∈ Δ`, splitting off
`ρ(x) = 0` as an immediate case.  The primed statements below therefore drop
the `0 < ρ x` hypothesis; see `proportionalBorda_eq_zero_of_ref_zero`. -/

/-- Proposition `PBPM` for `B^p`, over the paper's full reference domain
`ρ ∈ Δ` (no `0 < ρ x` hypothesis). -/
theorem PBPM_weak_from_profile_improvement'
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R R' : V → α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (h : IsWeakProfileImprovement R R' x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
      proportionalBorda η ρ (partialBordaScoreP R') x := by
  refine PBPM_from_score_differences' hη hρnonneg ?_
  intro z hzx
  exact partialBordaScoreP_diff_le_of_improvement (V := V) h hzx

/-- Positive involvement for `PB^p` over the paper's full reference domain. -/
theorem PBPPI_weak_from_added_top_profile'
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hcard : 2 ≤ Fintype.card α)
    (htop : RanksStrictlyTop p x) :
    proportionalBorda η ρ (partialBordaScoreP R) x ≤
      proportionalBorda η ρ (partialBordaScoreP (addVoterProfile R p)) x := by
  have hscore :
      partialBordaScoreP (addVoterProfile R p) =
        fun z => partialBordaScoreP R z + singleVoterBordaP p z := by
    funext z
    exact partialBordaScoreP_addVoterProfile R p z
  rw [hscore]
  refine PBPPI_from_score_bounds' hη hρnonneg hcard ?_ ?_
  · rw [singleVoterBordaP_top_self htop]
  · intro z hzx
    have hz := singleVoterBordaP_top_other_le htop hzx
    linarith

/-- Negative involvement for `PB^p` over the paper's full reference domain. -/
theorem PBPNI_weak_from_added_bottom_profile'
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hbottom : RanksStrictlyBottom p x) :
    proportionalBorda η ρ (partialBordaScoreP (addVoterProfile R p)) x ≤
      proportionalBorda η ρ (partialBordaScoreP R) x := by
  have hscore :
      partialBordaScoreP (addVoterProfile R p) =
        fun z => partialBordaScoreP R z + singleVoterBordaP p z := by
    funext z
    exact partialBordaScoreP_addVoterProfile R p z
  rw [hscore]
  refine PBPNI_from_score_bounds' hη hρnonneg ?_ ?_
  · rw [singleVoterBordaP_bottom_self hbottom]
    ring
  · intro z hzx
    have hz := singleVoterBordaP_bottom_other_ge hbottom hzx
    linarith

/-! ## Commutativity (`RTBTorder`, PB half) -/

/-- Proposition `RTBTorder`, proportional-Borda half, for the paper's `B^p`
on weak-relation profiles. -/
theorem proportionalBordaWeakProfile_commutative
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ}
    (R S : V → α → α → Bool)
    (hρ : IsFullSupportLottery ρ) :
    proportionalBorda η
        (proportionalBorda η ρ (partialBordaScoreP R))
        (partialBordaScoreP S) =
      proportionalBorda η
        (proportionalBorda η ρ (partialBordaScoreP S))
        (partialBordaScoreP R) :=
  proportionalBorda_commutative (η := η) hρ.1

/-! ## The strict part of a weak profile

For the RTBT side of Proposition `RTBTorder`, the paper computes
Bradley–Terry strengths from the strict-preference counts `c_{x,y}` of the
(weak-relation) profile.  `strictPart` extracts `P(𝐑_i)` as a Boolean
strict profile, so the existing Ford/Zermelo development applies. -/

/-- The strict part `P(𝐑_i)` of each voter's weak relation, as a Boolean
strict profile. -/
def strictPart (R : V → α → α → Bool) : V → α → α → Bool :=
  fun i x y => strictPrefRel (R i) x y

/-- The strict part is automatically irreflexive; no well-formedness
hypothesis on the weak profile is needed. -/
lemma isIrreflexiveProfile_strictPart (R : V → α → α → Bool) :
    IsIrreflexiveProfile (strictPart R) := by
  intro i x
  unfold strictPart strictPrefRel
  cases h : R i x x <;> simp [h]

/-- The strict-count matrix of the strict part is the paper's `c_{x,y}`. -/
lemma strictCount_strictPart [Fintype V] (R : V → α → α → Bool) :
    strictCount (strictPart R) = strictPrefCount R := by
  funext x y
  rfl

/-! ## Linear orders and the paper's `t`-normalized margins

A voter's Boolean relation is a strict linear order when it is irreflexive,
asymmetric, total on distinct candidates, and transitive.  On profiles of
linear orders every voter compares every pair, so `t_{x,y} = |V|` and the
paper's `t_{x,y}`-normalized margin agrees with the `|V|`-normalized
`normalizedStrictMargin` used in the Ford/NLHF developments. -/

/-- A single voter's Boolean relation is a strict linear order. -/
def IsLinearPref (p : α → α → Bool) : Prop :=
  (∀ x, p x x = false) ∧
    (∀ ⦃x y : α⦄, p x y = true → p y x = false) ∧
      (∀ x y : α, x ≠ y → p x y = true ∨ p y x = true) ∧
        ∀ ⦃x y z : α⦄, p x y = true → p y z = true → p x z = true

lemma isAsymmetricPref_of_isLinearPref {p : α → α → Bool}
    (h : IsLinearPref p) : IsAsymmetricPref p := h.2.1

lemma strictPrefRel_eq_of_asymm {p : α → α → Bool}
    (h : IsAsymmetricPref p) (x y : α) :
    strictPrefRel p x y = p x y := by
  unfold strictPrefRel
  cases hxy : p x y
  · simp
  · simp [h hxy]

lemma indiffRel_eq_false_of_asymm {p : α → α → Bool}
    (h : IsAsymmetricPref p) (x y : α) : indiffRel p x y = false := by
  unfold indiffRel
  cases hxy : p x y
  · simp
  · simp [h hxy]

lemma isLinearPref_addVoterProfile {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : ∀ i, IsLinearPref (R i)) (hp : IsLinearPref p) :
    ∀ i, IsLinearPref (addVoterProfile R p i) := by
  intro i
  cases i with
  | none => exact hp
  | some i => exact hR i

lemma strictPrefCount_eq_strictCount_of_asymmProfile [Fintype V]
    {R : V → α → α → Bool} (h : ∀ i, IsAsymmetricPref (R i)) :
    strictPrefCount R = strictCount R := by
  funext x y
  unfold strictPrefCount strictCount
  exact Finset.sum_congr rfl fun i _ => by
    rw [strictPrefRel_eq_of_asymm (h i)]

/-- On linear-order profiles every voter compares every distinct pair:
`t_{x,y} = |V|`. -/
lemma comparedCount_eq_card_of_linearProfile [Fintype V]
    {R : V → α → α → Bool} (h : ∀ i, IsLinearPref (R i))
    {x y : α} (hxy : x ≠ y) :
    comparedCount R x y = (Fintype.card V : ℝ) := by
  unfold comparedCount strictComparedCount strictPrefCount indiffCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hone : ∀ i : V,
      prefIndicator (strictPrefRel (R i) x y) +
          prefIndicator (strictPrefRel (R i) y x) +
        prefIndicator (indiffRel (R i) x y) = 1 := by
    intro i
    have hasymm := isAsymmetricPref_of_isLinearPref (h i)
    rw [strictPrefRel_eq_of_asymm hasymm, strictPrefRel_eq_of_asymm hasymm,
      indiffRel_eq_false_of_asymm hasymm]
    rcases (h i).2.2.1 x y hxy with hxy' | hyx'
    · simp [prefIndicator, hxy', hasymm hxy']
    · simp [prefIndicator, hyx', hasymm hyx']
  rw [Finset.sum_congr rfl (fun i _ => hone i)]
  simp

/-- The paper's `t_{x,y}`-normalized margin `m̄_{x,y}(𝐑)`, with the
`t_{x,y} = 0` convention `m̄ = 0` (`paper/main.tex`, formal framework). -/
noncomputable def paperNormalizedMargin [Fintype V]
    (R : V → α → α → Bool) (x y : α) : ℝ :=
  if comparedCount R x y = 0 then 0
  else (strictPrefCount R x y - strictPrefCount R y x) / comparedCount R x y

/-- On linear-order profiles the paper's `t`-normalized margin agrees with
the `|V|`-normalized strict margin. -/
theorem paperNormalizedMargin_eq_normalizedStrictMargin_of_linearProfile
    [Fintype V] [Nonempty V]
    {R : V → α → α → Bool} (h : ∀ i, IsLinearPref (R i)) :
    paperNormalizedMargin R = normalizedStrictMargin R := by
  funext x y
  by_cases hxy : x = y
  · subst hxy
    have hcc : comparedCount R x x = 0 := by
      unfold comparedCount strictComparedCount strictPrefCount indiffCount
      have hz1 : ∀ i : V, prefIndicator (strictPrefRel (R i) x x) = 0 := by
        intro i
        unfold strictPrefRel prefIndicator
        cases hp : R i x x <;> simp [hp]
      have hz2 : ∀ i : V, prefIndicator (indiffRel (R i) x x) = 0 := by
        intro i
        unfold indiffRel prefIndicator
        simp [(h i).1 x]
      rw [Finset.sum_eq_zero (fun i _ => hz1 i),
        Finset.sum_eq_zero (fun i _ => hz2 i)]
      ring
    unfold paperNormalizedMargin normalizedStrictMargin
    rw [strictMargin_self_eq_zero]
    simp [hcc]
  · have hcard : comparedCount R x y = (Fintype.card V : ℝ) :=
      comparedCount_eq_card_of_linearProfile h hxy
    have hcount := strictPrefCount_eq_strictCount_of_asymmProfile
      (fun i => isAsymmetricPref_of_isLinearPref (h i))
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    unfold paperNormalizedMargin normalizedStrictMargin strictMargin
    rw [hcard, hcount, if_neg hpos.ne']

/-! ## Profile-level involvement predicates

These give formal content to "`M'` is obtained from `M` by adding a voter
who ranks `x` first/last": the margin matrices are realized by an actual
finite linear-order profile and the same profile with one added linear
voter. -/

/-- `M'` is obtained from `M` by adding one voter who ranks `x` uniquely
first, on an actual finite linear-order profile, both read by
`|V|`-normalized strict margins (which agree with the paper's
`t_{x,y}`-normalization on linear-order profiles). -/
def LinearOrderAddsTopMargins [Fintype α]
    (M M' : α → α → ℝ) (x : α) : Prop :=
  ∃ (n : ℕ) (R : Fin n → α → α → Bool) (p : α → α → Bool),
    (∀ i, IsLinearPref (R i)) ∧ IsLinearPref p ∧ RanksTop p x ∧
      M = normalizedStrictMargin R ∧
      M' = normalizedStrictMargin (addVoterProfile R p)

/-- `M'` is obtained from `M` by adding one voter who ranks `x` uniquely
last, on an actual finite linear-order profile. -/
def LinearOrderAddsBottomMargins [Fintype α]
    (M M' : α → α → ℝ) (x : α) : Prop :=
  ∃ (n : ℕ) (R : Fin n → α → α → Bool) (p : α → α → Bool),
    (∀ i, IsLinearPref (R i)) ∧ IsLinearPref p ∧ RanksBottom p x ∧
      M = normalizedStrictMargin R ∧
      M' = normalizedStrictMargin (addVoterProfile R p)

/-! ## Relation to the strict-domination score

On complete profiles without expressed indifference, `B^p` and `B^d`
coincide. Completeness is necessary: an unexpressed comparison earns half
a point under `B^p` but none under the strict-domination score. -/

/-- No voter expresses indifference between distinct candidates. -/
def NoIndifference (R : V → α → α → Bool) : Prop :=
  ∀ i x y, x ≠ y → ¬(R i x y = true ∧ R i y x = true)

lemma partialBordaScoreP_eq_strictDominationBordaScore_of_complete_noIndifference
    [Fintype α] [DecidableEq α] [Fintype V]
    {R : V → α → α → Bool} (h : NoIndifference R)
    (hcomplete : ∀ i x y, x ≠ y → R i x y = true ∨ R i y x = true) (x : α) :
    partialBordaScoreP R x = strictDominationBordaScore R x := by
  classical
  unfold partialBordaScoreP strictDominationBordaScore
  refine Finset.sum_congr rfl ?_
  intro i _hi
  refine Finset.sum_congr rfl ?_
  intro y hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hne : x ≠ y := fun hxy => hyx hxy.symm
  have hni := h i x y hne
  have hc := hcomplete i x y hne
  unfold relCredit prefIndicator
  cases hxy : R i x y <;> cases hyx' : R i y x <;> simp_all

end PaperFormalization
