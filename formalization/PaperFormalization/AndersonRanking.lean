import PaperFormalization.RTBTPairMonotonicity
import PaperFormalization.WeakOrderScoreRepresentation

open scoped BigOperators

namespace PaperFormalization

variable {α V : Type*}

/-!
# The Anderson--Dandurova--Falk--Yeganova ranking equivalence

This file formalizes exactly the specialization used by Proposition `Anderson`
in the paper: complete, tie-free ranked ballots, Ford/Zermelo Bradley--Terry
strengths, and strict-domination Borda scores.

Mathematical credit: the ranking argument is due to L. B. Anderson,
H. Dandurova, J. E. Falk, and L. Yeganova, *Relationships between Borda
voting and Zermelo ranking*, Social Choice and Welfare 32 (2009), 355--365,
doi:10.1007/s00355-008-0327-7, especially pp. 360--361.  We use their
expected-wins equation and order argument, with Ford's displayed equations
already proved elsewhere in this development.  Equation (4) in the printed
paper writes `M(i,j)` where the preceding derivation and the free index require
`M(i,k)`; the formal statement below uses the latter pair total.
-/

/-! ## The expected-score order argument -/

/-- The expected number of Bradley--Terry wins against every alternative,
including the harmless self-comparison term `1/2`.  Including that term puts
the sums for two alternatives over the same finite index set. -/
noncomputable def andersonExpectedScore
    [Fintype α] (u : α → ℝ) (x : α) : ℝ :=
  Finset.sum Finset.univ (fun z => u x / (u x + u z))

lemma andersonShare_le_iff
    {a b z : ℝ} (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) :
    a / (a + z) ≤ b / (b + z) ↔ a ≤ b := by
  rw [div_le_div_iff₀ (add_pos ha hz) (add_pos hb hz)]
  constructor <;> intro h <;> nlinarith

lemma andersonShare_lt_iff
    {a b z : ℝ} (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) :
    a / (a + z) < b / (b + z) ↔ a < b := by
  rw [div_lt_div_iff₀ (add_pos ha hz) (add_pos hb hz)]
  constructor <;> intro h <;> nlinarith

lemma andersonExpectedScore_order_iff
    [Fintype α] [Nonempty α]
    {u : α → ℝ} (hu : ∀ z : α, 0 < u z) (x y : α) :
    andersonExpectedScore u y ≤ andersonExpectedScore u x ↔ u y ≤ u x := by
  classical
  constructor
  · intro hscore
    by_contra hnot
    have hxy : u x < u y := lt_of_not_ge hnot
    have hstrict : andersonExpectedScore u x < andersonExpectedScore u y := by
      unfold andersonExpectedScore
      refine Finset.sum_lt_sum (fun z _hz => ?_) ?_
      · exact (andersonShare_le_iff (hu x) (hu y) (hu z)).2 hxy.le
      · let z0 : α := Classical.choice inferInstance
        exact ⟨z0, Finset.mem_univ z0,
          (andersonShare_lt_iff (hu x) (hu y) (hu z0)).2 hxy⟩
    exact (not_lt_of_ge hscore) hstrict
  · intro hxy
    unfold andersonExpectedScore
    exact Finset.sum_le_sum fun z _hz =>
      (andersonShare_le_iff (hu y) (hu x) (hu z)).2 hxy

lemma andersonExpectedScore_eq_displayed_add_half
    [Fintype α] [DecidableEq α]
    {B u : α → ℝ} (hu : ∀ z : α, 0 < u z)
    (hBT : SatisfiesBTDisplayedEquation (fun _ _ : α => (1 : ℝ)) B u)
    (x : α) :
    andersonExpectedScore u x = B x + 1 / 2 := by
  classical
  have hself : u x / (u x + u x) = (1 : ℝ) / 2 := by
    field_simp [(hu x).ne']
    ring
  have hdisplayed :
      Finset.sum (Finset.univ.erase x)
          (fun z : α => u x / (u x + u z)) = B x := by
    simpa using hBT x
  calc
    andersonExpectedScore u x =
        Finset.sum (Finset.univ.erase x)
            (fun z : α => u x / (u x + u z)) +
          u x / (u x + u x) := by
            exact
              (Finset.sum_erase_add Finset.univ
                (fun z : α => u x / (u x + u z))
                (Finset.mem_univ x)).symm
    _ = B x + 1 / 2 := by rw [hdisplayed, hself]

/-- Anderson et al.'s core order equivalence, stated only for the unit-pair
displayed equations needed after complete ranked-ballot normalization. -/
theorem anderson_order_iff_of_unit_pair_displayed_equations
    [Fintype α] [DecidableEq α] [Nonempty α]
    {B u : α → ℝ} (hu : ∀ z : α, 0 < u z)
    (hBT : SatisfiesBTDisplayedEquation (fun _ _ : α => (1 : ℝ)) B u)
    (x y : α) :
    u y ≤ u x ↔ B y ≤ B x := by
  have hx := andersonExpectedScore_eq_displayed_add_half hu hBT x
  have hy := andersonExpectedScore_eq_displayed_add_half hu hBT y
  rw [← andersonExpectedScore_order_iff hu x y]
  rw [hx, hy]
  constructor <;> intro h <;> linarith

/-! ## Complete linear-order profiles -/

/-- A profile of strict linear orders is irreflexive. -/
lemma isIrreflexiveProfile_of_linearProfile
    {R : V → α → α → Bool} (hR : ∀ i, IsLinearPref (R i)) :
    IsIrreflexiveProfile R :=
  fun i x => (hR i).1 x

/-- A profile of strict linear orders compares every distinct pair exactly
once per voter, which is the no-abstention hypothesis in Anderson et al. -/
lemma isPairwiseCompleteProfile_of_linearProfile
    {R : V → α → α → Bool} (hR : ∀ i, IsLinearPref (R i)) :
    IsPairwiseCompleteProfile R := by
  intro i x y hxy
  rcases (hR i).2.2.1 x y hxy with hxy' | hyx'
  · have hyx' : R i y x = false := (hR i).2.1 hxy'
    simp [prefIndicator, hxy', hyx']
  · have hxy' : R i x y = false := (hR i).2.1 hyx'
    simp [prefIndicator, hxy', hyx']

/-- Strict-domination Borda is the row sum of the profile's strict-count
matrix. -/
lemma strictDominationBordaScore_eq_fordWinCount
    [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (x : α) :
    strictDominationBordaScore R x = fordWinCount (strictCount R) x := by
  classical
  unfold strictDominationBordaScore fordWinCount strictCount
  rw [Finset.sum_comm]

/-- Anderson et al.'s BT-vs-Borda ranking theorem for exactly the profile
class used in this paper.  Ford/Zermelo strong connectivity selects the
positive normalized strength vector; no optimization theorem is assumed as a
premise here. -/
theorem selectedBTOfFordZermelo_linearProfile_order_iff_borda
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype V] [Nonempty V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hlinear : ∀ i, IsLinearPref (R i))
    (hconn : FordStronglyConnected (strictCount R))
    (x y : α) :
    selectedBTOfFordZermelo hFord (strictCount R)
          (strictCount_isFordCountMatrix
            (isIrreflexiveProfile_of_linearProfile hlinear)) hconn y ≤
        selectedBTOfFordZermelo hFord (strictCount R)
          (strictCount_isFordCountMatrix
            (isIrreflexiveProfile_of_linearProfile hlinear)) hconn x ↔
      strictDominationBordaScore R y ≤ strictDominationBordaScore R x := by
  let u : α → ℝ :=
    selectedBTOfFordZermelo hFord (strictCount R)
      (strictCount_isFordCountMatrix
        (isIrreflexiveProfile_of_linearProfile hlinear)) hconn
  have hu : ∀ z : α, 0 < u z :=
    selectedBTOfFordZermelo_pos hFord
      (strictCount_isFordCountMatrix
        (isIrreflexiveProfile_of_linearProfile hlinear)) hconn
  have hcomp : IsPairwiseCompleteProfile R :=
    isPairwiseCompleteProfile_of_linearProfile hlinear
  have hBT :
      SatisfiesCompleteMarginBTEquations (normalizedStrictMargin R) u :=
    selectedBTOfFordZermelo_strictCountProfile_satisfiesCompleteMarginEquations
      hFord (isIrreflexiveProfile_of_linearProfile hlinear) hcomp hconn
  have hAnderson :
      u y ≤ u x ↔
        completeMarginWinCount (normalizedStrictMargin R) y ≤
          completeMarginWinCount (normalizedStrictMargin R) x :=
    anderson_order_iff_of_unit_pair_displayed_equations hu hBT x y
  have hcardpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card V)
  change u y ≤ u x ↔ _
  refine hAnderson.trans ?_
  rw [completeMarginWinCount_normalizedStrictMargin_eq_scaled_fordWinCount
        (R := R) hcomp y,
    completeMarginWinCount_normalizedStrictMargin_eq_scaled_fordWinCount
        (R := R) hcomp x,
    strictDominationBordaScore_eq_fordWinCount R y,
    strictDominationBordaScore_eq_fordWinCount R x]
  exact div_le_div_iff_of_pos_right hcardpos

/-- Proposition `Anderson` as used in the paper: for a uniform reference and
every `β > 0`, RTBT and strict-domination Borda induce the same weak ranking
on a complete strict-linear-order profile. -/
theorem Anderson_RTBTRanking_linearProfile
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype V] [Nonempty V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool}
    (hlinear : ∀ i, IsLinearPref (R i))
    (hconn : FordStronglyConnected (strictCount R))
    (x y : α) :
    RTBTFromStrength β (finiteUniformLottery α)
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite (strictCount R)
          (strictCount_isFordCountMatrix
            (isIrreflexiveProfile_of_linearProfile hlinear)) hconn) x ≥
      RTBTFromStrength β (finiteUniformLottery α)
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite (strictCount R)
          (strictCount_isFordCountMatrix
            (isIrreflexiveProfile_of_linearProfile hlinear)) hconn) y ↔
      strictDominationBordaScore R x ≥ strictDominationBordaScore R y := by
  let u : α → ℝ :=
    selectedBTOfFordZermelo FordZermeloBTTheorem_finite (strictCount R)
      (strictCount_isFordCountMatrix
        (isIrreflexiveProfile_of_linearProfile hlinear)) hconn
  have hu : ∀ z : α, 0 < u z :=
    selectedBTOfFordZermelo_pos FordZermeloBTTheorem_finite
      (strictCount_isFordCountMatrix
        (isIrreflexiveProfile_of_linearProfile hlinear)) hconn
  have hrtbt :
      RTBTFromStrength β (finiteUniformLottery α) u x ≥
          RTBTFromStrength β (finiteUniformLottery α) u y ↔
        u x ≥ u y :=
    RTBTFromStrength_order_iff_of_equal_reference hβ
      finiteUniformLottery_fullSupport.1 hu rfl
  change RTBTFromStrength β (finiteUniformLottery α) u x ≥
      RTBTFromStrength β (finiteUniformLottery α) u y ↔ _
  exact hrtbt.trans
    (selectedBTOfFordZermelo_linearProfile_order_iff_borda
      FordZermeloBTTheorem_finite hlinear hconn x y)

/-! ## The paper's native reflexive linear-order profiles -/

/-- The strict part of a paper-style reflexive, complete, transitive, and
antisymmetric relation is a strict linear order. -/
lemma isLinearPref_strictPart_of_isLinearOrderProfile
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R) (i : V) :
    IsLinearPref (strictPart R i) := by
  refine ⟨isIrreflexiveProfile_strictPart R i, ?_, ?_, ?_⟩
  · intro x y hxy
    unfold strictPart strictPrefRel at hxy ⊢
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxy
    simp [hxy.1, hxy.2]
  · intro x y hxy
    rcases hR.1.2.1 i x y hxy with hxy' | hyx'
    · have hyxFalse : R i y x = false := by
        cases hyxVal : R i y x
        · rfl
        · exact (hxy (hR.2 i x y hxy' hyxVal)).elim
      left
      simp [strictPart, strictPrefRel, hxy', hyxFalse]
    · have hxyFalse : R i x y = false := by
        cases hxyVal : R i x y
        · rfl
        · exact (hxy (hR.2 i x y hxyVal hyx')).elim
      right
      simp [strictPart, strictPrefRel, hyx', hxyFalse]
  · intro x y z hxy hyz
    unfold strictPart strictPrefRel at hxy hyz ⊢
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hxy hyz
    have hxz : R i x z = true := hR.1.2.2 i x y z hxy.1 hyz.1
    have hzxFalse : R i z x = false := by
      cases hzxVal : R i z x
      · rfl
      · have hzy : R i z y = true :=
          hR.1.2.2 i z x y hzxVal hxy.1
        simp_all
    simp [hxz, hzxFalse]

/-- Proposition `Anderson` on the exact relation-valued profile class used by
the paper.  Bradley--Terry counts and the strict-domination Borda score are
both computed from `strictPart R`. -/
theorem Anderson_RTBTRanking_linearOrderProfile
    [Fintype α] [DecidableEq α] [Nonempty α]
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
  Anderson_RTBTRanking_linearProfile hβ
    (fun i => isLinearPref_strictPart_of_isLinearOrderProfile hlinear i)
    hconn x y

end PaperFormalization
