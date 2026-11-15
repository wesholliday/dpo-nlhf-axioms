import PaperFormalization.NLHFMonotonicityFinite
import PaperFormalization.ProfileRTBT

open scoped BigOperators

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Uniform full-support lottery on a nonempty finite type. -/
noncomputable def finiteUniformLottery (α : Type*) [Fintype α] : α → ℝ :=
  fun _ => ((Fintype.card α : ℝ)⁻¹)

omit [DecidableEq α] in
lemma finiteUniformLottery_fullSupport :
    IsFullSupportLottery (finiteUniformLottery α) := by
  classical
  have hcardpos_nat : 0 < Fintype.card α :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcardpos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast hcardpos_nat
  constructor
  · intro x
    exact inv_pos.mpr hcardpos
  · simp [finiteUniformLottery, Finset.sum_const, hcardpos.ne']

/-- The row win total encoded by a normalized margin matrix for complete
pairwise comparisons.  For a linear-order profile this is the average number
of voters preferring `x` to each opponent, summed over opponents. -/
noncomputable def completeMarginWinCount
    (M : α → α → ℝ) (x : α) : ℝ :=
  Finset.sum (Finset.univ.erase x) (fun y => (1 + M x y) / 2)

/-- The Ford/Zermelo count matrix encoded by a complete normalized margin
matrix.  Off the diagonal, `(1 + M x y) / 2` is the observed share preferring
`x` to `y`; on the diagonal Ford's count-matrix convention is zero. -/
noncomputable def completeMarginCount
    (M : α → α → ℝ) (x y : α) : ℝ :=
  if x = y then 0 else (1 + M x y) / 2

omit [Fintype α] [Nonempty α] in
lemma completeMarginCount_isFordCountMatrix
    {M : α → α → ℝ}
    (hM : IsNormalizedMarginMatrix M) :
    IsFordCountMatrix (completeMarginCount M) := by
  constructor
  · intro x
    simp [completeMarginCount]
  · intro x y
    by_cases hxy : x = y
    · simp [completeMarginCount, hxy]
    · have hbound := hM.2.2 x y
      have hlow : -1 ≤ M x y := (abs_le.mp hbound).1
      simp [completeMarginCount, hxy]
      linarith

omit [Fintype α] [Nonempty α] in
lemma fordPairTotal_completeMarginCount_of_ne
    {M : α → α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    {x y : α}
    (hxy : x ≠ y) :
    fordPairTotal (completeMarginCount M) x y = 1 := by
  have hyx : y ≠ x := Ne.symm hxy
  have hskew : M y x = -M x y := hM.2.1 x y
  simp [fordPairTotal, completeMarginCount, hxy, hyx, hskew]
  ring

omit [Nonempty α] in
lemma fordWinCount_completeMarginCount
    {M : α → α → ℝ} (x : α) :
    fordWinCount (completeMarginCount M) x = completeMarginWinCount M x := by
  classical
  unfold fordWinCount completeMarginWinCount
  refine Finset.sum_congr rfl ?_
  intro y hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  simp [completeMarginCount, Ne.symm hyx]

/-- Displayed Bradley--Terry equations for complete normalized-margin data:
each unordered pair has total weight one, and the observed win share of `x`
against `y` is `(1 + M x y) / 2`. -/
def SatisfiesCompleteMarginBTEquations
    (M : α → α → ℝ) (u : α → ℝ) : Prop :=
  SatisfiesBTDisplayedEquation
    (fun _ _ : α => (1 : ℝ)) (completeMarginWinCount M) u

omit [Nonempty α] in
theorem SatisfiesCompleteMarginBTEquations_of_satisfiesFord_completeMarginCount
    {M : α → α → ℝ} {u : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hBT : SatisfiesFordBTEquations (completeMarginCount M) u) :
    SatisfiesCompleteMarginBTEquations M u := by
  classical
  intro x
  have hsum :
      Finset.sum (Finset.univ.erase x)
          (fun y => (1 : ℝ) * (u x / (u x + u y))) =
        Finset.sum (Finset.univ.erase x)
          (fun y =>
            fordPairTotal (completeMarginCount M) x y *
              (u x / (u x + u y))) := by
    refine Finset.sum_congr rfl ?_
    intro y hy
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    rw [fordPairTotal_completeMarginCount_of_ne hM (Ne.symm hyx)]
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y => (1 : ℝ) * (u x / (u x + u y))) =
      Finset.sum (Finset.univ.erase x)
        (fun y =>
          fordPairTotal (completeMarginCount M) x y *
            (u x / (u x + u y))) := hsum
    _ = fordWinCount (completeMarginCount M) x := hBT x
    _ = completeMarginWinCount M x := fordWinCount_completeMarginCount x

omit [Nonempty α] in
theorem SatisfiesFord_completeMarginCount_of_satisfiesCompleteMarginBTEquations
    {M : α → α → ℝ} {u : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hBT : SatisfiesCompleteMarginBTEquations M u) :
    SatisfiesFordBTEquations (completeMarginCount M) u := by
  classical
  intro x
  have hsum :
      Finset.sum (Finset.univ.erase x)
          (fun y =>
            fordPairTotal (completeMarginCount M) x y *
              (u x / (u x + u y))) =
        Finset.sum (Finset.univ.erase x)
          (fun y => (1 : ℝ) * (u x / (u x + u y))) := by
    refine Finset.sum_congr rfl ?_
    intro y hy
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    rw [fordPairTotal_completeMarginCount_of_ne hM (Ne.symm hyx)]
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y =>
          fordPairTotal (completeMarginCount M) x y *
            (u x / (u x + u y))) =
      Finset.sum (Finset.univ.erase x)
        (fun y => (1 : ℝ) * (u x / (u x + u y))) := hsum
    _ = completeMarginWinCount M x := hBT x
    _ = fordWinCount (completeMarginCount M) x :=
      (fordWinCount_completeMarginCount x).symm

omit [Nonempty α] in
theorem SatisfiesCompleteMarginBTEquations_iff_satisfiesFord_completeMarginCount
    {M : α → α → ℝ} {u : α → ℝ}
    (hM : IsNormalizedMarginMatrix M) :
    SatisfiesCompleteMarginBTEquations M u ↔
      SatisfiesFordBTEquations (completeMarginCount M) u :=
  ⟨SatisfiesFord_completeMarginCount_of_satisfiesCompleteMarginBTEquations hM,
    SatisfiesCompleteMarginBTEquations_of_satisfiesFord_completeMarginCount hM⟩

theorem exists_positive_completeMarginBTEquations_of_ford_zermelo
    (hFord : FordZermeloBTTheorem α)
    {M : α → α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hconn : FordStronglyConnected (completeMarginCount M)) :
    ∃ u : α → ℝ,
      (∀ x : α, 0 < u x) ∧ SatisfiesCompleteMarginBTEquations M u := by
  rcases exists_positive_ford_equation_solution_of_ford_zermelo hFord
      (completeMarginCount_isFordCountMatrix hM) hconn with
    ⟨u, hu, hBT⟩
  exact
    ⟨u, hu,
      SatisfiesCompleteMarginBTEquations_of_satisfiesFord_completeMarginCount
        hM hBT⟩

/-- Complete-margin Bradley--Terry equation existence with Ford/Zermelo
discharged by the proved finite theorem. -/
theorem exists_positive_completeMarginBTEquations
    {M : α → α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hconn : FordStronglyConnected (completeMarginCount M)) :
    ∃ u : α → ℝ,
      (∀ x : α, 0 < u x) ∧ SatisfiesCompleteMarginBTEquations M u :=
  exists_positive_completeMarginBTEquations_of_ford_zermelo
    FordZermeloBTTheorem_finite hM hconn

noncomputable def selectedCompleteMarginBTOfFordZermelo
    (hFord : FordZermeloBTTheorem α)
    (M : α → α → ℝ)
    (hM : IsNormalizedMarginMatrix M)
    (hconn : FordStronglyConnected (completeMarginCount M)) : α → ℝ :=
  selectedBTOfFordZermelo hFord (completeMarginCount M)
    (completeMarginCount_isFordCountMatrix hM) hconn

theorem selectedCompleteMarginBTOfFordZermelo_pos
    (hFord : FordZermeloBTTheorem α)
    {M : α → α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hconn : FordStronglyConnected (completeMarginCount M))
    (x : α) :
    0 < selectedCompleteMarginBTOfFordZermelo hFord M hM hconn x :=
  selectedBTOfFordZermelo_pos hFord
    (completeMarginCount_isFordCountMatrix hM) hconn x

theorem selectedCompleteMarginBTOfFordZermelo_fullSupport
    (hFord : FordZermeloBTTheorem α)
    {M : α → α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hconn : FordStronglyConnected (completeMarginCount M)) :
    IsFullSupportLottery
      (selectedCompleteMarginBTOfFordZermelo hFord M hM hconn) :=
  selectedBTOfFordZermelo_fullSupport hFord
    (completeMarginCount_isFordCountMatrix hM) hconn

theorem selectedCompleteMarginBTOfFordZermelo_satisfiesCompleteEquations
    (hFord : FordZermeloBTTheorem α)
    {M : α → α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hconn : FordStronglyConnected (completeMarginCount M)) :
    SatisfiesCompleteMarginBTEquations M
      (selectedCompleteMarginBTOfFordZermelo hFord M hM hconn) :=
  SatisfiesCompleteMarginBTEquations_of_satisfiesFord_completeMarginCount hM
    (selectedBTOfFordZermelo_satisfiesFordEquations hFord
      (completeMarginCount_isFordCountMatrix hM) hconn)

def IsPairwiseCompleteProfile
    {α V : Type*} (R : V → α → α → Bool) : Prop :=
  ∀ i x y, x ≠ y →
    prefIndicator (R i x y) + prefIndicator (R i y x) = 1

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma strictCount_add_swap_of_pairwiseComplete
    {V : Type*} [Fintype V]
    {R : V → α → α → Bool}
    (hcomp : IsPairwiseCompleteProfile R)
    {x y : α} (hxy : x ≠ y) :
    strictCount R x y + strictCount R y x = (Fintype.card V : ℝ) := by
  classical
  unfold strictCount
  rw [← Finset.sum_add_distrib]
  calc
    Finset.sum Finset.univ
        (fun i : V => prefIndicator (R i x y) + prefIndicator (R i y x)) =
      Finset.sum Finset.univ (fun _i : V => (1 : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        exact hcomp i x y hxy
    _ = (Fintype.card V : ℝ) := by simp

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma fordPairTotal_strictCount_eq_card_of_pairwiseComplete
    {V : Type*} [Fintype V]
    {R : V → α → α → Bool}
    (hcomp : IsPairwiseCompleteProfile R)
    {x y : α} (hxy : x ≠ y) :
    fordPairTotal (strictCount R) x y = (Fintype.card V : ℝ) := by
  simpa [fordPairTotal] using
    strictCount_add_swap_of_pairwiseComplete
      (R := R) hcomp hxy

omit [Fintype α] [Nonempty α] in
lemma completeMarginCount_normalizedStrictMargin_eq_scaled_strictCount_of_ne
    {V : Type*} [Fintype V] [Nonempty V]
    {R : V → α → α → Bool}
    (hcomp : IsPairwiseCompleteProfile R)
    {x y : α} (hxy : x ≠ y) :
    completeMarginCount (normalizedStrictMargin R) x y =
      strictCount R x y / (Fintype.card V : ℝ) := by
  classical
  have hcardpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card V)
  have hsum :
      strictCount R x y + strictCount R y x = (Fintype.card V : ℝ) :=
    strictCount_add_swap_of_pairwiseComplete (R := R) hcomp hxy
  simp [completeMarginCount, hxy, normalizedStrictMargin, strictMargin]
  field_simp [hcardpos.ne']
  linarith

omit [Nonempty α] in
lemma completeMarginWinCount_normalizedStrictMargin_eq_scaled_fordWinCount
    {V : Type*} [Fintype V] [Nonempty V]
    {R : V → α → α → Bool}
    (hcomp : IsPairwiseCompleteProfile R)
    (x : α) :
    completeMarginWinCount (normalizedStrictMargin R) x =
      fordWinCount (strictCount R) x / (Fintype.card V : ℝ) := by
  classical
  unfold completeMarginWinCount fordWinCount
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y : α => (1 + normalizedStrictMargin R x y) / 2) =
      Finset.sum (Finset.univ.erase x)
        (fun y : α => strictCount R x y / (Fintype.card V : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        simpa [completeMarginCount, Ne.symm hyx] using
          completeMarginCount_normalizedStrictMargin_eq_scaled_strictCount_of_ne
            (R := R) hcomp (Ne.symm hyx)
    _ = Finset.sum (Finset.univ.erase x)
        (fun y : α => strictCount R x y) / (Fintype.card V : ℝ) := by
        rw [Finset.sum_div]

omit [Nonempty α] in
theorem SatisfiesCompleteMarginBTEquations_normalizedStrictMargin_of_satisfiesFord
    {V : Type*} [Fintype V] [Nonempty V]
    {R : V → α → α → Bool} {u : α → ℝ}
    (hcomp : IsPairwiseCompleteProfile R)
    (hBT : SatisfiesFordBTEquations (strictCount R) u) :
    SatisfiesCompleteMarginBTEquations (normalizedStrictMargin R) u := by
  classical
  intro x
  have hcardpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card V)
  have hleft :
      Finset.sum (Finset.univ.erase x)
          (fun y : α => (1 : ℝ) * (u x / (u x + u y))) =
        Finset.sum (Finset.univ.erase x)
          (fun y : α =>
            fordPairTotal (strictCount R) x y *
              (u x / (u x + u y))) /
          (Fintype.card V : ℝ) := by
    calc
      Finset.sum (Finset.univ.erase x)
          (fun y : α => (1 : ℝ) * (u x / (u x + u y))) =
        Finset.sum (Finset.univ.erase x)
          (fun y : α =>
            (fordPairTotal (strictCount R) x y *
              (u x / (u x + u y))) /
              (Fintype.card V : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
          have hpair :
              fordPairTotal (strictCount R) x y =
                (Fintype.card V : ℝ) :=
            fordPairTotal_strictCount_eq_card_of_pairwiseComplete
              (R := R) hcomp (Ne.symm hyx)
          rw [hpair]
          field_simp [hcardpos.ne']
      _ =
        Finset.sum (Finset.univ.erase x)
          (fun y : α =>
            fordPairTotal (strictCount R) x y *
              (u x / (u x + u y))) /
          (Fintype.card V : ℝ) := by
          rw [Finset.sum_div]
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y : α => (1 : ℝ) * (u x / (u x + u y))) =
      Finset.sum (Finset.univ.erase x)
        (fun y : α =>
          fordPairTotal (strictCount R) x y *
            (u x / (u x + u y))) /
        (Fintype.card V : ℝ) := hleft
    _ = fordWinCount (strictCount R) x / (Fintype.card V : ℝ) := by
      rw [hBT x]
    _ = completeMarginWinCount (normalizedStrictMargin R) x :=
    (completeMarginWinCount_normalizedStrictMargin_eq_scaled_fordWinCount
      (R := R) hcomp x).symm

omit [Nonempty α] in
theorem SatisfiesFord_of_satisfiesCompleteMarginBTEquations_normalizedStrictMargin
    {V : Type*} [Fintype V] [Nonempty V]
    {R : V → α → α → Bool} {u : α → ℝ}
    (hcomp : IsPairwiseCompleteProfile R)
    (hBT : SatisfiesCompleteMarginBTEquations (normalizedStrictMargin R) u) :
    SatisfiesFordBTEquations (strictCount R) u := by
  classical
  intro x
  have hcardpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card V)
  have hsum :
      Finset.sum (Finset.univ.erase x)
          (fun y : α =>
            fordPairTotal (strictCount R) x y *
              (u x / (u x + u y))) =
        (Fintype.card V : ℝ) *
          Finset.sum (Finset.univ.erase x)
            (fun y : α => (1 : ℝ) * (u x / (u x + u y))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y hy
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    have hpair :
        fordPairTotal (strictCount R) x y = (Fintype.card V : ℝ) :=
      fordPairTotal_strictCount_eq_card_of_pairwiseComplete
        (R := R) hcomp (Ne.symm hyx)
    rw [hpair]
    ring
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y : α =>
          fordPairTotal (strictCount R) x y *
            (u x / (u x + u y))) =
      (Fintype.card V : ℝ) *
        Finset.sum (Finset.univ.erase x)
          (fun y : α => (1 : ℝ) * (u x / (u x + u y))) := hsum
    _ = (Fintype.card V : ℝ) *
        completeMarginWinCount (normalizedStrictMargin R) x := by
        rw [hBT x]
    _ = fordWinCount (strictCount R) x := by
        rw [completeMarginWinCount_normalizedStrictMargin_eq_scaled_fordWinCount
          (R := R) hcomp x]
        field_simp [hcardpos.ne']

omit [Fintype α] [Nonempty α] in
theorem FordStronglyConnected_completeMarginCount_normalizedStrictMargin
    {V : Type*} [Fintype V] [Nonempty V]
    {R : V → α → α → Bool}
    (hirr : IsIrreflexiveProfile R)
    (hcomp : IsPairwiseCompleteProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    FordStronglyConnected (completeMarginCount (normalizedStrictMargin R)) := by
  refine FordStronglyConnected_mono ?_ hconn
  intro x y hpos
  have hxy : x ≠ y := by
    intro h
    subst y
    have hzero : strictCount R x x = 0 := strictCount_self_eq_zero hirr x
    linarith
  rw [completeMarginCount_normalizedStrictMargin_eq_scaled_strictCount_of_ne
    (R := R) hcomp hxy]
  have hcardpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card V)
  exact div_pos hpos hcardpos

theorem selectedBTOfFordZermelo_strictCountProfile_satisfiesCompleteMarginEquations
    {V : Type*} [Fintype V] [Nonempty V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hirr : IsIrreflexiveProfile R)
    (hcomp : IsPairwiseCompleteProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    SatisfiesCompleteMarginBTEquations (normalizedStrictMargin R)
      (selectedBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hirr) hconn) :=
  SatisfiesCompleteMarginBTEquations_normalizedStrictMargin_of_satisfiesFord
    hcomp
    (selectedBTOfFordZermelo_satisfiesFordEquations hFord
      (strictCount_isFordCountMatrix hirr) hconn)

theorem selectedCompleteMarginBTOfFordZermelo_normalizedStrictMargin_eq_selectedBTOfFordZermelo
    {V : Type*} [Fintype V] [Nonempty V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hirr : IsIrreflexiveProfile R)
    (hcomp : IsPairwiseCompleteProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    selectedCompleteMarginBTOfFordZermelo hFord
        (normalizedStrictMargin R)
        (normalizedStrictMargin_isNormalizedMarginMatrix R)
        (FordStronglyConnected_completeMarginCount_normalizedStrictMargin
          hirr hcomp hconn) =
      selectedBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hirr) hconn := by
  exact SatisfiesFordBTEquations_unique_of_stronglyConnected
    (strictCount_isFordCountMatrix hirr) hconn
    (selectedCompleteMarginBTOfFordZermelo_fullSupport hFord
      (normalizedStrictMargin_isNormalizedMarginMatrix R)
      (FordStronglyConnected_completeMarginCount_normalizedStrictMargin
        hirr hcomp hconn))
    (selectedBTOfFordZermelo_fullSupport hFord
      (strictCount_isFordCountMatrix hirr) hconn)
    (SatisfiesFord_of_satisfiesCompleteMarginBTEquations_normalizedStrictMargin
      hcomp
      (selectedCompleteMarginBTOfFordZermelo_satisfiesCompleteEquations hFord
        (normalizedStrictMargin_isNormalizedMarginMatrix R)
        (FordStronglyConnected_completeMarginCount_normalizedStrictMargin
          hirr hcomp hconn)))
    (selectedBTOfFordZermelo_satisfiesFordEquations hFord
      (strictCount_isFordCountMatrix hirr) hconn)

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma div_le_div_of_ratio_le
    {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    {x z : α}
    (h : v z / u z ≤ v x / u x) :
    v z / v x ≤ u z / u x := by
  have hcross : v z * u x ≤ v x * u z := by
    rwa [div_le_div_iff₀ (hu z) (hu x)] at h
  rw [div_le_div_iff₀ (hv x) (hu x)]
  nlinarith

omit [Nonempty α] in
lemma completeMarginWinCount_improvePairMargin_le_of_ne
    {M : α → α → ℝ} {x y k : α} {δ : ℝ}
    (hkx : k ≠ x)
    (hδ : 0 ≤ δ) :
    completeMarginWinCount (improvePairMargin M x y δ) k ≤
      completeMarginWinCount M k := by
  classical
  unfold completeMarginWinCount
  refine Finset.sum_le_sum ?_
  intro z hz
  by_cases hky : k = y
  · subst k
    by_cases hzx : z = x
    · subst z
      simp [improvePairMargin, hkx]
      linarith
    · have hnot₁ : ¬ (y = x ∧ z = y) := by
        intro h
        exact hkx h.1
      have hnot₂ : ¬ (y = y ∧ z = x) := by
        intro h
        exact hzx h.2
      simp [improvePairMargin, hnot₁, hzx]
  · have hnot₁ : ¬ (k = x ∧ z = y) := by
      intro h
      exact hkx h.1
    have hnot₂ : ¬ (k = y ∧ z = x) := by
      intro h
      exact hky h.1
    simp [improvePairMargin, hnot₁, hnot₂]

/-- One-pair Bradley--Terry comparative statics for complete normalized-margin
equations.  If `M'` improves `x` against one opponent and `u`, `v` are
positive BT solutions for `M`, `M'`, then every ratio `v z / v x` is at most
the old ratio `u z / u x`. -/
theorem completeMarginBT_pair_ratio_monotonicity_of_displayed_equations
    {M : α → α → ℝ} {x y : α} {δ : ℝ} {u v : α → ℝ}
    (hδpos : 0 < δ)
    (hu : ∀ z : α, 0 < u z)
    (hv : ∀ z : α, 0 < v z)
    (hBTu : SatisfiesCompleteMarginBTEquations M u)
    (hBTv :
      SatisfiesCompleteMarginBTEquations
        (improvePairMargin M x y δ) v) :
    ∀ z : α, z ≠ x → v z / v x ≤ u z / u x := by
  classical
  rcases Finset.exists_max_image (Finset.univ : Finset α)
      (fun z => v z / u z) Finset.univ_nonempty with
    ⟨k, _hk, hmax_univ⟩
  have hmax : ∀ z : α, v z / u z ≤ v k / u k := by
    intro z
    exact hmax_univ z (Finset.mem_univ z)
  have hx_max : ∀ z : α, v z / u z ≤ v x / u x := by
    by_cases hkx : k = x
    · subst k
      exact hmax
    · have hfrac_le :
        ∀ z : α, z ∈ Finset.univ.erase k →
          btFraction u k z ≤ btFraction v k z := by
        intro z _hz
        exact btFraction_le_of_ratio_ge hv hu (hmax z)
      have hBTu_k :
          Finset.sum (Finset.univ.erase k)
              (fun z => btFraction u k z) =
            completeMarginWinCount M k := by
        simpa [SatisfiesCompleteMarginBTEquations, btFraction] using hBTu k
      have hBTv_k :
          Finset.sum (Finset.univ.erase k)
              (fun z => btFraction v k z) =
            completeMarginWinCount (improvePairMargin M x y δ) k := by
        simpa [SatisfiesCompleteMarginBTEquations, btFraction] using hBTv k
      have hwin_le :
          completeMarginWinCount (improvePairMargin M x y δ) k ≤
            completeMarginWinCount M k :=
        completeMarginWinCount_improvePairMargin_le_of_ne
          (M := M) (y := y) hkx hδpos.le
      have hsum_le :
          Finset.sum (Finset.univ.erase k)
              (fun z => btFraction u k z) ≤
            Finset.sum (Finset.univ.erase k)
              (fun z => btFraction v k z) :=
        Finset.sum_le_sum hfrac_le
      have hwin_eq :
          completeMarginWinCount (improvePairMargin M x y δ) k =
            completeMarginWinCount M k := by
        linarith
      have hsumzero :
          Finset.sum (Finset.univ.erase k)
              (fun z => btFraction v k z - btFraction u k z) = 0 := by
        calc
          Finset.sum (Finset.univ.erase k)
              (fun z => btFraction v k z - btFraction u k z)
              =
            Finset.sum (Finset.univ.erase k)
                (fun z => btFraction v k z) -
              Finset.sum (Finset.univ.erase k)
                (fun z => btFraction u k z) := by
              rw [← Finset.sum_sub_distrib]
          _ = 0 := by
              rw [hBTv_k, hBTu_k, hwin_eq]
              ring
      have hterm_nonneg :
          ∀ z : α, z ∈ Finset.univ.erase k →
            0 ≤ btFraction v k z - btFraction u k z := by
        intro z hz
        exact sub_nonneg.mpr (hfrac_le z hz)
      have hx_mem : x ∈ Finset.univ.erase k :=
        Finset.mem_erase.mpr ⟨Ne.symm hkx, Finset.mem_univ x⟩
      have hfrac_eq :
          btFraction v k x - btFraction u k x = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp
          hsumzero x hx_mem
      have hratio_kx : v k / u k = v x / u x :=
        ratio_eq_of_btFraction_eq hv hu (by linarith)
      intro z
      calc
        v z / u z ≤ v k / u k := hmax z
        _ = v x / u x := hratio_kx
  intro z _hzx
  exact div_le_div_of_ratio_le hu hv (hx_max z)

/-- Concrete selected-Ford/Zermelo one-pair RTBT monotonicity wrapper.  This
is the paper proof's single-comparison step with the BT strengths instantiated
by the Ford/Zermelo selected complete-margin solutions, rather than by an
abstract selector. -/
theorem RTBTPM_onePair_selectedCompleteMarginBTOfFordZermelo
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {M : α → α → ℝ} {ρ : α → ℝ} {x y : α} {δ : ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hconn : FordStronglyConnected (completeMarginCount M))
    (hconn' :
      FordStronglyConnected
        (completeMarginCount (improvePairMargin M x y δ)))
    (hρ : IsFullSupportLottery ρ)
    (hyx : y ≠ x)
    (hδpos : 0 < δ)
    (hδle : δ ≤ 1 - M x y) :
    RTBTFromStrength β ρ
        (selectedCompleteMarginBTOfFordZermelo hFord M hM hconn) x ≤
      RTBTFromStrength β ρ
        (selectedCompleteMarginBTOfFordZermelo hFord
          (improvePairMargin M x y δ)
          (improvePairMargin_normalized hM (Ne.symm hyx) hδpos.le hδle)
          hconn') x := by
  let Mplus : α → α → ℝ := improvePairMargin M x y δ
  have hMplus : IsNormalizedMarginMatrix Mplus := by
    dsimp [Mplus]
    exact improvePairMargin_normalized hM (Ne.symm hyx) hδpos.le hδle
  have hratio : ∀ z : α, z ≠ x →
      selectedCompleteMarginBTOfFordZermelo hFord Mplus hMplus hconn' z /
          selectedCompleteMarginBTOfFordZermelo hFord Mplus hMplus hconn' x ≤
        selectedCompleteMarginBTOfFordZermelo hFord M hM hconn z /
          selectedCompleteMarginBTOfFordZermelo hFord M hM hconn x := by
    exact completeMarginBT_pair_ratio_monotonicity_of_displayed_equations
      hδpos
      (selectedCompleteMarginBTOfFordZermelo_pos hFord hM hconn)
      (selectedCompleteMarginBTOfFordZermelo_pos hFord hMplus hconn')
      (selectedCompleteMarginBTOfFordZermelo_satisfiesCompleteEquations
        hFord hM hconn)
      (selectedCompleteMarginBTOfFordZermelo_satisfiesCompleteEquations
        hFord hMplus hconn')
  simpa [Mplus] using
    RTBTPM_from_BT_ratio_monotonicity (α := α) (β := β) hβ
      (fun z => (hρ.1 z).le) (hρ.1 x)
      (selectedCompleteMarginBTOfFordZermelo_pos hFord hM hconn)
      (selectedCompleteMarginBTOfFordZermelo_pos hFord hMplus hconn')
      hratio

/-- Pair-change Bradley-Terry comparative-static interface.  This matches the
paper proof's single-comparison-change step: after improving `x` against one
`y`, every ratio `BT z / BT x`
weakly decreases. -/
def HasBTRatioMonotonicityForPairImprovements
    (BT : (α → α → ℝ) → α → ℝ) : Prop :=
  (∀ (M : α → α → ℝ) (x : α), 0 < BT M x) ∧
  ∀ (M : α → α → ℝ) (x y : α) (δ : ℝ),
    IsNormalizedMarginMatrix M →
      y ≠ x →
        0 < δ →
          δ ≤ 1 - M x y →
            ∀ z : α, z ≠ x →
              BT (improvePairMargin M x y δ) z /
                  BT (improvePairMargin M x y δ) x ≤
                BT M z / BT M x

/-- Forward-ratio version of the one-pair Bradley-Terry comparative static.
This matches the paper proof's wording: after improving `x` against one `y`,
every ratio `BT x / BT z` weakly increases. -/
def HasBTForwardRatioMonotonicityForPairImprovements
    (BT : (α → α → ℝ) → α → ℝ) : Prop :=
  (∀ (M : α → α → ℝ) (x : α), 0 < BT M x) ∧
  ∀ (M : α → α → ℝ) (x y : α) (δ : ℝ),
    IsNormalizedMarginMatrix M →
      y ≠ x →
        0 < δ →
          δ ≤ 1 - M x y →
            ∀ z : α, z ≠ x →
              BT M x / BT M z ≤
                BT (improvePairMargin M x y δ) x /
                  BT (improvePairMargin M x y δ) z

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma reciprocal_ratio_le_of_forward_ratio_le
    {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a / b ≤ c / d) :
    d / c ≤ b / a := by
  have hmul : a * d ≤ c * b := by
    rwa [div_le_div_iff₀ hb hd] at h
  rw [div_le_div_iff₀ hc ha]
  nlinarith [hmul]

/- The forward-ratio formulation of the one-pair Bradley-Terry comparative
static implies the reciprocal formulation used by the RTBT
denominator argument. -/
omit [Fintype α] [Nonempty α] in
lemma HasBTRatioMonotonicityForPairImprovements_of_forward_pair
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTForwardRatioMonotonicityForPairImprovements BT) :
    HasBTRatioMonotonicityForPairImprovements BT := by
  refine ⟨hBT.1, ?_⟩
  intro M x y δ hM hyx hδpos hδle z hzx
  exact reciprocal_ratio_le_of_forward_ratio_le
    (hBT.1 M x) (hBT.1 M z)
    (hBT.1 (improvePairMargin M x y δ) x)
    (hBT.1 (improvePairMargin M x y δ) z)
    (hBT.2 M x y δ hM hyx hδpos hδle z hzx)

/-- The one-pair Bradley-Terry ratio comparative static assembles into the
full matrix-improvement comparative static by the same pair-improvement
decomposition used for NLHF monotonicity. -/
theorem HasBTRatioMonotonicityForImprovements_of_pair
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTRatioMonotonicityForPairImprovements BT) :
    HasBTRatioMonotonicityForImprovements BT := by
  refine ⟨hBT.1, ?_⟩
  intro M M' x hM hM' himp z hzx
  let F : MatrixRule α :=
    fun N _ρ t => if z = t then (0 : ℝ) else -(BT N z / BT N t)
  have hmono : SatisfiesProbabilisticMonotonicity F := by
    refine monotonicity_from_pair_improvements ?_
    intro N ρ t y δ hN _hρ hyt hδpos hδle
    by_cases hzt : z = t
    · simp [F, hzt]
    · have hratio := hBT.2 N t y δ hN hyt hδpos hδle z hzt
      simp [F, hzt]
      linarith
  have hle :=
    hmono M M' (finiteUniformLottery α) x hM hM'
      finiteUniformLottery_fullSupport himp
  simp [F, hzx] at hle
  linarith

/-- The paper-worded forward-ratio one-pair comparative static assembles into
the full matrix-improvement comparative static. -/
theorem HasBTRatioMonotonicityForImprovements_of_forward_pair
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTForwardRatioMonotonicityForPairImprovements BT) :
    HasBTRatioMonotonicityForImprovements BT :=
  HasBTRatioMonotonicityForImprovements_of_pair
    (HasBTRatioMonotonicityForPairImprovements_of_forward_pair hBT)

/-- RTBT probabilistic monotonicity from the one-pair Bradley-Terry ratio
comparative static. -/
theorem RTBTPM_from_BT_pair_ratio_certificate
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTRatioMonotonicityForPairImprovements BT) :
    SatisfiesProbabilisticMonotonicity
      (fun M ρ => RTBTFromStrength β ρ (BT M)) :=
  RTBTPM_from_BT_ratio_certificate hβ
    (HasBTRatioMonotonicityForImprovements_of_pair hBT)

/-- Proposition `RTBTPM`, conditional on the paper-worded forward-ratio
one-pair Bradley-Terry comparative static. -/
theorem RTBTPM_from_BT_forward_pair_ratio_certificate
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTForwardRatioMonotonicityForPairImprovements BT) :
    SatisfiesProbabilisticMonotonicity
      (fun M ρ => RTBTFromStrength β ρ (BT M)) :=
  RTBTPM_from_BT_ratio_certificate hβ
    (HasBTRatioMonotonicityForImprovements_of_forward_pair hBT)

/-- Finite-profile version of `RTBTPM`, conditional only on the one-pair
Bradley-Terry ratio comparative static. -/
theorem RTBTPM_profile_from_BT_pair_ratio_certificate
    {V : Type*} [Fintype V] [Nonempty V]
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTRatioMonotonicityForPairImprovements BT) :
    SatisfiesProfileProbabilisticMonotonicity (V := V)
      (fun M ρ => RTBTFromStrength β ρ (BT M)) :=
  RTBTPM_profile_from_BT_ratio_certificate hβ
    (HasBTRatioMonotonicityForImprovements_of_pair hBT)

/-- Finite-profile `RTBTPM`, conditional on the paper-worded forward-ratio
one-pair Bradley-Terry comparative static. -/
theorem RTBTPM_profile_from_BT_forward_pair_ratio_certificate
    {V : Type*} [Fintype V] [Nonempty V]
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTForwardRatioMonotonicityForPairImprovements BT) :
    SatisfiesProfileProbabilisticMonotonicity (V := V)
      (fun M ρ => RTBTFromStrength β ρ (BT M)) :=
  RTBTPM_profile_from_BT_ratio_certificate hβ
    (HasBTRatioMonotonicityForImprovements_of_forward_pair hBT)

/-- Pointwise finite-profile `RTBTPM` from the one-pair Bradley-Terry ratio
comparative static. -/
theorem RTBTPM_profile_pointwise_from_BT_pair_ratio_certificate
    {V : Type*} [Fintype V] [Nonempty V]
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTRatioMonotonicityForPairImprovements BT)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (hprof : IsProfileImprovement R R' x) :
    RTBTFromStrength β ρ (BT (normalizedStrictMargin R)) x ≤
      RTBTFromStrength β ρ (BT (normalizedStrictMargin R')) x :=
  RTBTPM_profile_from_BT_pair_ratio_certificate (V := V) hβ hBT
    R R' ρ x hρ hprof

/-- Pointwise finite-profile `RTBTPM` from the paper-worded forward-ratio
one-pair Bradley-Terry comparative static. -/
theorem RTBTPM_profile_pointwise_from_BT_forward_pair_ratio_certificate
    {V : Type*} [Fintype V] [Nonempty V]
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTForwardRatioMonotonicityForPairImprovements BT)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (hprof : IsProfileImprovement R R' x) :
    RTBTFromStrength β ρ (BT (normalizedStrictMargin R)) x ≤
      RTBTFromStrength β ρ (BT (normalizedStrictMargin R')) x :=
  RTBTPM_profile_from_BT_forward_pair_ratio_certificate (V := V) hβ hBT
    R R' ρ x hρ hprof

end PaperFormalization
