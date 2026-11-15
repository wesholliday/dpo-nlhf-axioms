import PaperFormalization.WeakProfileBorda
import PaperFormalization.RTBTPairMonotonicity

open scoped BigOperators

namespace PaperFormalization

/-!
# Count-level Bradley--Terry comparative statics for `RTBTPM`

This module supplies the non-vacuous engine behind Proposition `RTBTPM`.
Everything happens at the level of Ford count matrices `c_{x,y}`, which is
exactly the level at which the paper defines `RTBT_β` (Ford's displayed
equations use the heterogeneous pair weights `w_{x,y} = c_{x,y} + c_{y,x}`).

Main results:

* `FordStronglyConnected_of_between` — connectivity for the intermediate
  stages of the improvement decomposition: a matrix whose
  `x`-out-edges dominate those of `c`, whose `x`-in-edges dominate those of
  `c'`, and which dominates both off `x`, is strongly connected as soon as `c`
  and `c'` are.
* `fordBT_max_ratio_at_improved_of_onePair` — the one-pair comparative static
  for heterogeneous pair weights (the count-level replacement for the citation
  of Noothigattu et al., Thm 4.2, in the English proof).
* `fordBT_ratio_monotonicity_of_countImprovement` — the multi-pair engine,
  assembled by induction over opponents.
* `RTBTPM_count_selectedBTOfFordZermelo` — count-level probabilistic
  monotonicity of the Ford/Zermelo-selected `RTBT_β`.
-/

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ## The count-level improvement relation -/

/-- Count-level reading of the paper's improvement conditions (i)–(iii):
`x`'s strict-win counts only grow, strict wins against `x` only shrink, and
comparisons not involving `x` are unchanged. -/
def IsCountImprovementOf (c c' : α → α → ℝ) (x : α) : Prop :=
  (∀ y : α, y ≠ x → c x y ≤ c' x y) ∧
    (∀ y : α, y ≠ x → c' y x ≤ c y x) ∧
      ∀ y z : α, y ≠ x → z ≠ x → c' y z = c y z

/-! ## The connectivity ("sandwich") argument -/

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Connectivity lemma used for Proposition `RTBTPM`.  An intermediate matrix
`d` keeps every out-edge of `x` in `G(c)`, every in-edge of `x` in `G(c')`,
and every edge not involving `x` from either graph; such a `d` is strongly
connected whenever `c` and `c'` are.  The proof uses Ford's partition
formulation, so no path induction is needed. -/
lemma FordStronglyConnected_of_between
    {c c' d : α → α → ℝ} {x : α}
    (hxout : ∀ y : α, 0 < c x y → 0 < d x y)
    (hxin : ∀ y : α, 0 < c' y x → 0 < d y x)
    (hoth : ∀ y z : α, y ≠ x → z ≠ x → 0 < c y z → 0 < d y z)
    (hoth' : ∀ y z : α, y ≠ x → z ≠ x → 0 < c' y z → 0 < d y z)
    (hconn : FordStronglyConnected c)
    (hconn' : FordStronglyConnected c') :
    FordStronglyConnected d := by
  rw [FordStronglyConnected_iff_partitionAssumption]
  intro S hS hSc
  by_cases hx : x ∈ S
  · rcases FordPartitionAssumption_of_stronglyConnected hconn' S hS hSc with
      ⟨a, haSc, b, hbS, hab⟩
    have hax : a ≠ x := by
      intro h
      subst h
      exact haSc hx
    refine ⟨a, haSc, b, hbS, ⟨hab.1, ?_⟩⟩
    by_cases hbx : b = x
    · subst hbx
      exact hxin a hab.2
    · exact hoth' a b hax hbx hab.2
  · rcases FordPartitionAssumption_of_stronglyConnected hconn S hS hSc with
      ⟨a, haSc, b, hbS, hab⟩
    have hbx : b ≠ x := by
      intro h
      subst h
      exact hx hbS
    refine ⟨a, haSc, b, hbS, ⟨hab.1, ?_⟩⟩
    by_cases hax : a = x
    · subst hax
      exact hxout b hab.2
    · exact hoth a b hax hbx hab.2

/-! ## Two-matrix single-row max-ratio equality -/

omit [Nonempty α] in
/-- Single-pivot-row version of `fordEquation_max_ratio_fraction_eq`: the two
strength vectors solve the displayed equations for *different* count matrices,
which are only required to agree on the pivot's row and column.  This is what
makes the max-ratio propagation usable across a one-pair change. -/
lemma fordEquation_max_ratio_fraction_eq_of_row_eq
    {c c' : α → α → ℝ} {u v : α → ℝ} {k z : α}
    (hc : IsFordCountMatrix c)
    (hrow : ∀ t : α, c' k t = c k t)
    (hcol : ∀ t : α, c' t k = c t k)
    (hu : ∀ t : α, 0 < u t) (hv : ∀ t : α, 0 < v t)
    (hmax : ∀ t : α, v t / u t ≤ v k / u k)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c' v)
    (hT : 0 < fordPairTotal c k z) :
    btFraction v k z = btFraction u k z := by
  classical
  have hpair : ∀ t : α, fordPairTotal c' k t = fordPairTotal c k t := by
    intro t
    unfold fordPairTotal
    rw [hrow t, hcol t]
  have hwin : fordWinCount c' k = fordWinCount c k := by
    unfold fordWinCount
    exact Finset.sum_congr rfl (fun t _ht => hrow t)
  have hBTu_k :
      Finset.sum (Finset.univ.erase k)
        (fun t => fordPairTotal c k t * btFraction u k t) =
          fordWinCount c k := by
    simpa [btFraction] using hBTu k
  have hBTv_k :
      Finset.sum (Finset.univ.erase k)
        (fun t => fordPairTotal c k t * btFraction v k t) =
          fordWinCount c k := by
    have hv_k :
        Finset.sum (Finset.univ.erase k)
          (fun t => fordPairTotal c' k t * btFraction v k t) =
            fordWinCount c' k := by
      simpa [btFraction] using hBTv k
    calc
      Finset.sum (Finset.univ.erase k)
          (fun t => fordPairTotal c k t * btFraction v k t) =
        Finset.sum (Finset.univ.erase k)
          (fun t => fordPairTotal c' k t * btFraction v k t) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          rw [hpair t]
      _ = fordWinCount c' k := hv_k
      _ = fordWinCount c k := hwin
  have hterm_nonneg :
      ∀ t : α, t ∈ Finset.univ.erase k →
        0 ≤ fordPairTotal c k t * (btFraction v k t - btFraction u k t) := by
    intro t _ht
    have hTnonneg : 0 ≤ fordPairTotal c k t := by
      unfold fordPairTotal
      exact add_nonneg (hc.2 k t) (hc.2 t k)
    have hfrac_le : btFraction u k t ≤ btFraction v k t :=
      btFraction_le_of_ratio_ge hv hu (hmax t)
    exact mul_nonneg hTnonneg (sub_nonneg.mpr hfrac_le)
  have hsumzero :
      Finset.sum (Finset.univ.erase k)
        (fun t => fordPairTotal c k t *
          (btFraction v k t - btFraction u k t)) = 0 := by
    calc
      Finset.sum (Finset.univ.erase k)
          (fun t => fordPairTotal c k t *
            (btFraction v k t - btFraction u k t))
          =
        Finset.sum (Finset.univ.erase k)
          (fun t => fordPairTotal c k t * btFraction v k t) -
          Finset.sum (Finset.univ.erase k)
            (fun t => fordPairTotal c k t * btFraction u k t) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro t _ht
          ring
      _ = 0 := by
          rw [hBTu_k, hBTv_k]
          ring
  have hzk : z ≠ k := by
    intro hzk
    subst hzk
    have hTzero : fordPairTotal c z z = 0 := by
      unfold fordPairTotal
      rw [hc.1 z]
      ring
    rw [hTzero] at hT
    linarith
  have hz_mem : z ∈ Finset.univ.erase k :=
    Finset.mem_erase.mpr ⟨hzk, Finset.mem_univ z⟩
  have hterm_zero :
      fordPairTotal c k z * (btFraction v k z - btFraction u k z) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsumzero z hz_mem
  have hdiff_zero : btFraction v k z - btFraction u k z = 0 := by
    nlinarith
  linarith

/-! ## Row bookkeeping for a one-pair change -/

omit [Nonempty α] in
/-- Row-`y` win count for a one-pair change: only the `x` entry of `y`'s row
moves, so `y`'s win count drops by exactly what is removed from `c y x`. -/
lemma fordWinCount_of_onePair
    {c c' : α → α → ℝ} {x y : α}
    (hyx : y ≠ x)
    (hoth : ∀ p q : α, ¬(p = x ∧ q = y) → ¬(p = y ∧ q = x) → c' p q = c p q) :
    fordWinCount c' y = fordWinCount c y - (c y x - c' y x) := by
  classical
  have hx_mem : x ∈ Finset.univ.erase y :=
    Finset.mem_erase.mpr ⟨Ne.symm hyx, Finset.mem_univ x⟩
  have hdiff :
      Finset.sum (Finset.univ.erase y) (fun t => c' y t - c y t) =
        c' y x - c y x := by
    refine Finset.sum_eq_single_of_mem x hx_mem ?_
    intro t _ht htx
    have h1 : ¬ (y = x ∧ t = y) := by
      intro h
      exact hyx h.1
    have h2 : ¬ (y = y ∧ t = x) := by
      intro h
      exact htx h.2
    rw [hoth y t h1 h2]
    ring
  have hsplit :
      fordWinCount c' y - fordWinCount c y =
        Finset.sum (Finset.univ.erase y) (fun t => c' y t - c y t) := by
    unfold fordWinCount
    rw [← Finset.sum_sub_distrib]
  have hfinal := hsplit.trans hdiff
  linarith

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Row-`y` pair totals for a one-pair change: only the `(y,x)` total moves. -/
lemma fordPairTotal_of_onePair
    {c c' : α → α → ℝ} {x y t : α}
    (hyx : y ≠ x)
    (hoth : ∀ p q : α, ¬(p = x ∧ q = y) → ¬(p = y ∧ q = x) → c' p q = c p q)
    (htx : t ≠ x) :
    fordPairTotal c' y t = fordPairTotal c y t := by
  have h1 : ¬ (y = x ∧ t = y) := by
    intro h
    exact hyx h.1
  have h2 : ¬ (y = y ∧ t = x) := by
    intro h
    exact htx h.2
  have h3 : ¬ (t = x ∧ y = y) := by
    intro h
    exact htx h.1
  have h4 : ¬ (t = y ∧ y = x) := by
    intro h
    exact hyx h.2
  unfold fordPairTotal
  rw [hoth y t h1 h2, hoth t y h3 h4]

omit [Nonempty α] in
/-- The losing endpoint of a one-pair improvement cannot carry the maximal
new/old strength ratio.  This rules out the "wrong" argmax in the count-level
comparative static. -/
lemma not_max_ratio_at_opponent_of_onePair
    {c c' : α → α → ℝ} {x y : α} {u v : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hyx : y ≠ x)
    (hxy_le : c x y ≤ c' x y)
    (hyx_ge : c' y x ≤ c y x)
    (hoth : ∀ p q : α, ¬(p = x ∧ q = y) → ¬(p = y ∧ q = x) → c' p q = c p q)
    (hchange : 0 < (c' x y - c x y) + (c y x - c' y x))
    (hu : ∀ t : α, 0 < u t) (hv : ∀ t : α, 0 < v t)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c' v)
    (hmaxy : ∀ t : α, v t / u t ≤ v y / u y) :
    False := by
  classical
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, c' x y = c x y + a :=
    ⟨c' x y - c x y, by ring⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, c' y x = c y x - b :=
    ⟨c y x - c' y x, by ring⟩
  have ha : 0 ≤ a := by
    rw [ha_def] at hxy_le
    linarith
  have hb : 0 ≤ b := by
    rw [hb_def] at hyx_ge
    linarith
  have hab : 0 < a + b := by
    rw [ha_def, hb_def] at hchange
    linarith
  have hx_mem : x ∈ Finset.univ.erase y :=
    Finset.mem_erase.mpr ⟨Ne.symm hyx, Finset.mem_univ x⟩
  have hBTu_y :
      Finset.sum (Finset.univ.erase y)
        (fun t => fordPairTotal c y t * btFraction u y t) =
          fordWinCount c y := by
    simpa [btFraction] using hBTu y
  have hBTv_y :
      Finset.sum (Finset.univ.erase y)
        (fun t => fordPairTotal c' y t * btFraction v y t) =
          fordWinCount c' y := by
    simpa [btFraction] using hBTv y
  have hfrac_le : ∀ t : α, btFraction u y t ≤ btFraction v y t := by
    intro t
    exact btFraction_le_of_ratio_ge hv hu (hmaxy t)
  have hsum_le :
      Finset.sum (Finset.univ.erase y)
          (fun t => fordPairTotal c y t * btFraction u y t) ≤
        Finset.sum (Finset.univ.erase y)
          (fun t => fordPairTotal c y t * btFraction v y t) := by
    refine Finset.sum_le_sum ?_
    intro t _ht
    have hTnonneg : 0 ≤ fordPairTotal c y t := by
      unfold fordPairTotal
      exact add_nonneg (hc.2 y t) (hc.2 t y)
    exact mul_le_mul_of_nonneg_left (hfrac_le t) hTnonneg
  have hxterm :
      fordPairTotal c' y x * btFraction v y x -
          fordPairTotal c y x * btFraction v y x =
        (a - b) * btFraction v y x := by
    unfold fordPairTotal
    rw [ha_def, hb_def]
    ring
  have hpairdiff :
      Finset.sum (Finset.univ.erase y)
        (fun t =>
          fordPairTotal c' y t * btFraction v y t -
            fordPairTotal c y t * btFraction v y t) =
        (a - b) * btFraction v y x := by
    rw [← hxterm]
    refine Finset.sum_eq_single_of_mem x hx_mem ?_
    intro t _ht htx
    rw [fordPairTotal_of_onePair (c := c) (c' := c') hyx hoth htx]
    ring
  have hdist :
      Finset.sum (Finset.univ.erase y)
          (fun t =>
            fordPairTotal c' y t * btFraction v y t -
              fordPairTotal c y t * btFraction v y t) =
        Finset.sum (Finset.univ.erase y)
            (fun t => fordPairTotal c' y t * btFraction v y t) -
          Finset.sum (Finset.univ.erase y)
            (fun t => fordPairTotal c y t * btFraction v y t) := by
    rw [← Finset.sum_sub_distrib]
  have hwin : fordWinCount c' y = fordWinCount c y - b := by
    rw [fordWinCount_of_onePair hyx hoth, hb_def]
    ring
  have hkey : (a - b) * btFraction v y x ≤ -b := by
    rw [hdist, hBTv_y, hwin] at hpairdiff
    linarith [hsum_le, hBTu_y, hpairdiff]
  have hf0 : 0 < btFraction v y x := btFraction_pos_of_pos hv y x
  have hf1 : btFraction v y x < 1 := btFraction_lt_one_of_pos hv y x
  have hane : 0 < a ∨ 0 < b := by
    by_contra hcon
    push_neg at hcon
    linarith [hcon.1, hcon.2]
  rcases hane with hapos | hbpos
  · nlinarith [mul_pos hapos hf0, mul_nonneg hb (sub_pos.mpr hf1).le]
  · nlinarith [mul_nonneg ha hf0.le, mul_pos hbpos (sub_pos.mpr hf1)]

/-! ## The one-pair count-level comparative static -/

/-- One-pair Bradley--Terry comparative static at the count level, with the
heterogeneous Ford pair weights `w_{x,y} = c_{x,y} + c_{y,x}`.  This is the
formal counterpart of the single-comparison step of the English proof (cited
there as Noothigattu et al., Thm 4.2).  The proof takes the argmax of the
new/old strength ratio, excludes the opponent `y` by
`not_max_ratio_at_opponent_of_onePair`, and propagates the max along a
`c`-edge produced by Ford's partition assumption. -/
theorem fordBT_max_ratio_at_improved_of_onePair
    {c c' : α → α → ℝ} {x y : α} {u v : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hyx : y ≠ x)
    (hxy_le : c x y ≤ c' x y)
    (hyx_ge : c' y x ≤ c y x)
    (hoth : ∀ p q : α, ¬(p = x ∧ q = y) → ¬(p = y ∧ q = x) → c' p q = c p q)
    (hchange : 0 < (c' x y - c x y) + (c y x - c' y x))
    (hu : ∀ t : α, 0 < u t) (hv : ∀ t : α, 0 < v t)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c' v) :
    ∀ z : α, v z / u z ≤ v x / u x := by
  classical
  rcases Finset.exists_max_image (Finset.univ : Finset α)
      (fun z => v z / u z) Finset.univ_nonempty with ⟨k, _hk, hmax_univ⟩
  have hmax : ∀ t : α, v t / u t ≤ v k / u k := by
    intro t
    exact hmax_univ t (Finset.mem_univ t)
  have hxmax : v x / u x = v k / u k := by
    by_contra hxne
    set S : Set α := {z : α | v z / u z ≠ v k / u k} with hS_def
    have hxS : x ∈ S := hxne
    have hkSc : k ∈ Sᶜ := by
      intro hkS
      exact hkS rfl
    rcases FordPartitionAssumption_of_stronglyConnected hconn S ⟨x, hxS⟩
        ⟨k, hkSc⟩ with ⟨p, hpSc, q, hqS, hpq⟩
    have hpmax : v p / u p = v k / u k := by
      by_contra hpne
      exact hpSc hpne
    have hqne : v q / u q ≠ v k / u k := hqS
    have hmaxp : ∀ t : α, v t / u t ≤ v p / u p := by
      intro t
      rw [hpmax]
      exact hmax t
    have hpy : p ≠ y := by
      intro hpy
      subst hpy
      exact not_max_ratio_at_opponent_of_onePair hc hyx hxy_le hyx_ge hoth
        hchange hu hv hBTu hBTv hmaxp
    have hpx : p ≠ x := by
      intro hpx
      subst hpx
      exact hxS hpmax
    have hrow : ∀ t : α, c' p t = c p t := by
      intro t
      refine hoth p t ?_ ?_
      · intro h
        exact hpx h.1
      · intro h
        exact hpy h.1
    have hcol : ∀ t : α, c' t p = c t p := by
      intro t
      refine hoth t p ?_ ?_
      · intro h
        exact hpy h.2
      · intro h
        exact hpx h.2
    have hT : 0 < fordPairTotal c p q :=
      fordPairTotal_pos_of_count_pos hc.2 hpq.2
    have hfrac : btFraction v p q = btFraction u p q :=
      fordEquation_max_ratio_fraction_eq_of_row_eq hc hrow hcol hu hv hmaxp
        hBTu hBTv hT
    have hratio : v p / u p = v q / u q :=
      ratio_eq_of_btFraction_eq hv hu hfrac
    exact hqne (by rw [← hratio, hpmax])
  intro z
  rw [hxmax]
  exact hmax z

/-- Ratio form of the one-pair count-level comparative static. -/
theorem fordBT_ratio_le_of_onePair
    {c c' : α → α → ℝ} {x y : α} {u v : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hyx : y ≠ x)
    (hxy_le : c x y ≤ c' x y)
    (hyx_ge : c' y x ≤ c y x)
    (hoth : ∀ p q : α, ¬(p = x ∧ q = y) → ¬(p = y ∧ q = x) → c' p q = c p q)
    (hchange : 0 < (c' x y - c x y) + (c y x - c' y x))
    (hu : ∀ t : α, 0 < u t) (hv : ∀ t : α, 0 < v t)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c' v) :
    ∀ z : α, z ≠ x → v z / v x ≤ u z / u x := by
  intro z _hzx
  exact div_le_div_of_ratio_le hu hv
    (fordBT_max_ratio_at_improved_of_onePair hc hconn hyx hxy_le hyx_ge hoth
      hchange hu hv hBTu hBTv z)

/-! ## Per-opponent decomposition of a count improvement -/

/-- Partially apply a count improvement of `x`, opponent by opponent: the
entries `c x y` and `c y x` are replaced by the improved ones exactly for the
opponents `y ∈ S`.  Aggregating a whole opponent at once makes the order of
the paper's additions and removals irrelevant. -/
def partialCountImprovement (c c' : α → α → ℝ) (x : α) (S : Finset α) :
    α → α → ℝ :=
  fun p q =>
    if p = x ∧ q ∈ S then c' p q
    else if p ∈ S ∧ q = x then c' p q
    else c p q

omit [Fintype α] [Nonempty α] in
lemma partialCountImprovement_empty (c c' : α → α → ℝ) (x : α) :
    partialCountImprovement c c' x ∅ = c := by
  funext p q
  simp [partialCountImprovement]

omit [Nonempty α] in
lemma partialCountImprovement_univ_erase
    {c c' : α → α → ℝ} {x : α}
    (hc : IsFordCountMatrix c) (hc' : IsFordCountMatrix c')
    (himp : IsCountImprovementOf c c' x) :
    partialCountImprovement c c' x (Finset.univ.erase x) = c' := by
  funext p q
  by_cases hpx : p = x
  · subst p
    by_cases hqx : q = x
    · subst q
      simp [partialCountImprovement, hc.1, hc'.1]
    · simp [partialCountImprovement, hqx]
  · by_cases hqx : q = x
    · subst q
      simp [partialCountImprovement, hpx]
    · have hfixed := himp.2.2 p q hpx hqx
      simp [partialCountImprovement, hpx, hqx, hfixed]

omit [Fintype α] [Nonempty α] in
lemma partialCountImprovement_isFordCountMatrix
    {c c' : α → α → ℝ} {x : α} {S : Finset α}
    (hc : IsFordCountMatrix c) (hc' : IsFordCountMatrix c')
    (hxS : x ∉ S) :
    IsFordCountMatrix (partialCountImprovement c c' x S) := by
  constructor
  · intro p
    unfold partialCountImprovement
    split_ifs with h1 h2
    · exact absurd (h1.1 ▸ h1.2) hxS
    · exact absurd (h2.2 ▸ h2.1) hxS
    · exact hc.1 p
  · intro p q
    unfold partialCountImprovement
    split_ifs
    · exact hc'.2 p q
    · exact hc'.2 p q
    · exact hc.2 p q

omit [Fintype α] [Nonempty α] in
/-- Every intermediate matrix of the per-opponent decomposition is strongly
connected: it keeps all of `x`'s out-edges in `G(c)`, all of `x`'s in-edges in
`G(c')`, and every edge not involving `x`.  This is the machine-checked
replacement for the flagged parenthetical in the English proof. -/
lemma FordStronglyConnected_partialCountImprovement
    {c c' : α → α → ℝ} {x : α} {S : Finset α}
    (hc' : IsFordCountMatrix c')
    (himp : IsCountImprovementOf c c' x)
    (hxS : x ∉ S)
    (hconn : FordStronglyConnected c)
    (hconn' : FordStronglyConnected c') :
    FordStronglyConnected (partialCountImprovement c c' x S) := by
  refine FordStronglyConnected_of_between (c := c) (c' := c') (x := x)
    ?_ ?_ ?_ ?_ hconn hconn'
  · intro y hpos
    unfold partialCountImprovement
    split_ifs with h1 h2
    · have hyx : y ≠ x := by
        intro h
        exact hxS (h ▸ h1.2)
      exact lt_of_lt_of_le hpos (himp.1 y hyx)
    · exact absurd (h2.1) hxS
    · exact hpos
  · intro y hpos
    unfold partialCountImprovement
    split_ifs with h1 h2
    · exact absurd (h1.2) hxS
    · exact hpos
    · have hyx : y ≠ x := by
        intro h
        subst h
        rw [hc'.1 y] at hpos
        exact lt_irrefl 0 hpos
      exact lt_of_lt_of_le hpos (himp.2.1 y hyx)
  · intro y z hyx hzx hpos
    unfold partialCountImprovement
    split_ifs with h1 h2
    · exact absurd h1.1 hyx
    · exact absurd h2.2 hzx
    · exact hpos
  · intro y z hyx hzx hpos
    unfold partialCountImprovement
    split_ifs with h1 h2
    · exact absurd h1.1 hyx
    · exact absurd h2.2 hzx
    · rw [himp.2.2 y z hyx hzx] at hpos
      exact hpos

omit [Fintype α] [Nonempty α] in
lemma partialCountImprovement_apply_xy
    {c c' : α → α → ℝ} {x y : α} {S : Finset α}
    (hxS : x ∉ S) (hyS : y ∉ S) :
    partialCountImprovement c c' x S x y = c x y := by
  simp [partialCountImprovement, hxS, hyS]

omit [Fintype α] [Nonempty α] in
lemma partialCountImprovement_apply_yx
    {c c' : α → α → ℝ} {x y : α} {S : Finset α}
    (hyx : y ≠ x) (hyS : y ∉ S) :
    partialCountImprovement c c' x S y x = c y x := by
  simp [partialCountImprovement, hyx, hyS]

omit [Fintype α] [Nonempty α] in
lemma partialCountImprovement_insert_apply_xy
    (c c' : α → α → ℝ) (x y : α) (S : Finset α) :
    partialCountImprovement c c' x (insert y S) x y = c' x y := by
  simp [partialCountImprovement]

omit [Fintype α] [Nonempty α] in
lemma partialCountImprovement_insert_apply_yx
    {c c' : α → α → ℝ} {x y : α} {S : Finset α}
    (hyx : y ≠ x) :
    partialCountImprovement c c' x (insert y S) y x = c' y x := by
  simp [partialCountImprovement, hyx]

omit [Fintype α] [Nonempty α] in
/-- Adding one opponent to the partial improvement changes exactly the two
entries of that opponent's pair with `x`. -/
lemma partialCountImprovement_insert_agrees
    {c c' : α → α → ℝ} {x y : α} {S : Finset α}
    (hyx : y ≠ x) (hxS : x ∉ S) :
    ∀ p q : α, ¬(p = x ∧ q = y) → ¬(p = y ∧ q = x) →
      partialCountImprovement c c' x (insert y S) p q =
        partialCountImprovement c c' x S p q := by
  intro p q h1 h2
  by_cases hpx : p = x
  · subst p
    have hqy : q ≠ y := by
      intro h
      exact h1 ⟨rfl, h⟩
    have hmem : q ∈ insert y S ↔ q ∈ S := by
      simp [Finset.mem_insert, hqy]
    simp [partialCountImprovement, hmem, hxS, Ne.symm hyx]
  · by_cases hqx : q = x
    · subst q
      have hpy : p ≠ y := by
        intro h
        exact h2 ⟨h, rfl⟩
      have hmem : p ∈ insert y S ↔ p ∈ S := by
        simp [Finset.mem_insert, hpy]
      simp [partialCountImprovement, hmem, hpx]
    · simp [partialCountImprovement, hpx, hqx]

/-! ## The multi-pair engine -/

/-- Count-level Bradley--Terry ratio monotonicity for a full improvement of
`x`: assembled from the one-pair static by induction over opponents, with the
intermediate Ford solutions supplied by `exists_positive_ford_equation_solution`
and intermediate connectivity by the sandwich lemma. -/
theorem fordBT_ratio_monotonicity_of_countImprovement
    {c c' : α → α → ℝ} {x : α} {u v : α → ℝ}
    (hc : IsFordCountMatrix c) (hc' : IsFordCountMatrix c')
    (hconn : FordStronglyConnected c) (hconn' : FordStronglyConnected c')
    (himp : IsCountImprovementOf c c' x)
    (hu : ∀ t : α, 0 < u t) (hv : ∀ t : α, 0 < v t)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c' v) :
    ∀ z : α, z ≠ x → v z / v x ≤ u z / u x := by
  classical
  have hind : ∀ S : Finset α, S ⊆ Finset.univ.erase x →
      ∀ w : α → ℝ, (∀ t : α, 0 < w t) →
        SatisfiesFordBTEquations (partialCountImprovement c c' x S) w →
          ∀ z : α, z ≠ x → w z / w x ≤ u z / u x := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hsub w hw hBTw z _hzx
      rw [partialCountImprovement_empty] at hBTw
      obtain ⟨a, hapos, heq⟩ :=
        SatisfiesFordBTEquations_positive_unique_ray hc hconn hu hw hBTu hBTw
      have hwz : w z = a * u z := by rw [heq]
      have hwx : w x = a * u x := by rw [heq]
      have hane : a ≠ 0 := ne_of_gt hapos
      have hux : u x ≠ 0 := ne_of_gt (hu x)
      rw [hwz, hwx]
      have hcalc : a * u z / (a * u x) = u z / u x := by
        field_simp
      rw [hcalc]
    · intro y S hyS ih hsub w' hw' hBTw'
      have hSsub : S ⊆ Finset.univ.erase x := by
        intro t ht
        exact hsub (Finset.mem_insert_of_mem ht)
      have hy_target : y ∈ Finset.univ.erase x :=
        hsub (Finset.mem_insert_self y S)
      have hyx : y ≠ x := (Finset.mem_erase.mp hy_target).1
      have hxS : x ∉ S := by
        intro hx
        exact (Finset.mem_erase.mp (hSsub hx)).1 rfl
      have hxinsert : x ∉ insert y S := by
        intro hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact hyx h.symm
        · exact hxS h
      have hdFord : IsFordCountMatrix (partialCountImprovement c c' x S) :=
        partialCountImprovement_isFordCountMatrix hc hc' hxS
      have hdconn :
          FordStronglyConnected (partialCountImprovement c c' x S) :=
        FordStronglyConnected_partialCountImprovement hc' himp hxS hconn hconn'
      obtain ⟨w, hw, hBTw⟩ :=
        exists_positive_ford_equation_solution hdFord hdconn
      have hIH := ih hSsub w hw hBTw
      have hagree :=
        partialCountImprovement_insert_agrees
          (c := c) (c' := c') (x := x) (y := y) (S := S) hyx hxS
      have hd_xy : partialCountImprovement c c' x S x y = c x y :=
        partialCountImprovement_apply_xy hxS hyS
      have hd_yx : partialCountImprovement c c' x S y x = c y x :=
        partialCountImprovement_apply_yx hyx hyS
      have hd'_xy :
          partialCountImprovement c c' x (insert y S) x y = c' x y :=
        partialCountImprovement_insert_apply_xy c c' x y S
      have hd'_yx :
          partialCountImprovement c c' x (insert y S) y x = c' y x :=
        partialCountImprovement_insert_apply_yx hyx
      by_cases hchange :
          0 < (partialCountImprovement c c' x (insert y S) x y -
                partialCountImprovement c c' x S x y) +
              (partialCountImprovement c c' x S y x -
                partialCountImprovement c c' x (insert y S) y x)
      · have hxy_le :
            partialCountImprovement c c' x S x y ≤
              partialCountImprovement c c' x (insert y S) x y := by
          rw [hd_xy, hd'_xy]
          exact himp.1 y hyx
        have hyx_ge :
            partialCountImprovement c c' x (insert y S) y x ≤
              partialCountImprovement c c' x S y x := by
          rw [hd_yx, hd'_yx]
          exact himp.2.1 y hyx
        have hstep :=
          fordBT_ratio_le_of_onePair hdFord hdconn hyx hxy_le hyx_ge
            (fun p q h1 h2 => hagree p q h1 h2) hchange hw hw' hBTw hBTw'
        intro z hzx
        exact le_trans (hstep z hzx) (hIH z hzx)
      · push_neg at hchange
        have hxy_le : c x y ≤ c' x y := himp.1 y hyx
        have hyx_ge : c' y x ≤ c y x := himp.2.1 y hyx
        rw [hd_xy, hd_yx, hd'_xy, hd'_yx] at hchange
        have hxy_eq : c' x y = c x y := by linarith
        have hyx_eq : c' y x = c y x := by linarith
        have hsame :
            partialCountImprovement c c' x (insert y S) =
              partialCountImprovement c c' x S := by
          funext p q
          by_cases h1 : p = x ∧ q = y
          · obtain ⟨hp, hq⟩ := h1
            subst p
            subst q
            rw [hd'_xy, hd_xy, hxy_eq]
          · by_cases h2 : p = y ∧ q = x
            · obtain ⟨hp, hq⟩ := h2
              subst p
              subst q
              rw [hd'_yx, hd_yx, hyx_eq]
            · exact hagree p q h1 h2
        rw [hsame] at hBTw'
        exact ih hSsub w' hw' hBTw'
  have hsub : (Finset.univ.erase x : Finset α) ⊆ Finset.univ.erase x :=
    subset_rfl
  refine hind (Finset.univ.erase x) hsub v hv ?_
  rw [partialCountImprovement_univ_erase hc hc' himp]
  exact hBTv

/-! ## A satisfiable Bradley--Terry selector interface -/

/-- A Bradley--Terry selector on the domain where Ford/Zermelo applies: it is
positive everywhere and solves Ford's displayed equations for every strongly
connected Ford count matrix.  `fordZermeloBTSelector` is an instance. -/
def IsStronglyConnectedFordBTSelector (BT : (α → α → ℝ) → α → ℝ) : Prop :=
  (∀ (c : α → α → ℝ) (x : α), 0 < BT c x) ∧
    ∀ c : α → α → ℝ, IsFordCountMatrix c → FordStronglyConnected c →
      SatisfiesFordBTEquations c (BT c)

/-- The total Ford/Zermelo Bradley--Terry selector: the selected normalized
solution on the Ford-connected domain, and an arbitrary positive constant
elsewhere. -/
noncomputable def fordZermeloBTSelector : (α → α → ℝ) → α → ℝ := by
  classical
  exact fun c =>
    if h : IsFordCountMatrix c ∧ FordStronglyConnected c then
      selectedBTOfFordZermelo FordZermeloBTTheorem_finite c h.1 h.2
    else fun _ => 1

theorem fordZermeloBTSelector_eq_selectedBTOfFordZermelo
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c) (hconn : FordStronglyConnected c) :
    fordZermeloBTSelector c =
      selectedBTOfFordZermelo FordZermeloBTTheorem_finite c hc hconn := by
  classical
  simp [fordZermeloBTSelector, hc, hconn]

theorem fordZermeloBTSelector_pos (c : α → α → ℝ) (x : α) :
    0 < fordZermeloBTSelector c x := by
  classical
  by_cases h : IsFordCountMatrix c ∧ FordStronglyConnected c
  · rw [fordZermeloBTSelector_eq_selectedBTOfFordZermelo h.1 h.2]
    exact selectedBTOfFordZermelo_pos FordZermeloBTTheorem_finite h.1 h.2 x
  · have hval : fordZermeloBTSelector c = fun _ : α => (1 : ℝ) := by
      simp [fordZermeloBTSelector, h]
    rw [hval]
    norm_num

theorem fordZermeloBTSelector_isStronglyConnectedFordBTSelector :
    IsStronglyConnectedFordBTSelector (fordZermeloBTSelector (α := α)) := by
  refine ⟨fordZermeloBTSelector_pos, ?_⟩
  intro c hc hconn
  rw [fordZermeloBTSelector_eq_selectedBTOfFordZermelo hc hconn]
  exact selectedBTOfFordZermelo_satisfiesFordEquations
    FordZermeloBTTheorem_finite hc hconn

/-! ## Count-level probabilistic monotonicity -/

/-- Probabilistic monotonicity on the paper's domain `𝒟`: Ford count matrices
whose positive-count graph is strongly connected, together with a full-support
reference lottery. -/
def SatisfiesCountProbabilisticMonotonicity (F : MatrixRule α) : Prop :=
  ∀ (c c' : α → α → ℝ) (ρ : α → ℝ) (x : α),
    IsFordCountMatrix c → IsFordCountMatrix c' →
      FordStronglyConnected c → FordStronglyConnected c' →
        IsFullSupportLottery ρ → IsCountImprovementOf c c' x →
          F c ρ x ≤ F c' ρ x

/-- Proposition `RTBTPM` at the count level, for any selector that solves
Ford's equations on the strongly connected domain. -/
theorem RTBTPM_count_from_selector
    {β : ℝ} (hβ : 0 < β) {BT : (α → α → ℝ) → α → ℝ}
    (hBT : IsStronglyConnectedFordBTSelector BT) :
    SatisfiesCountProbabilisticMonotonicity
      (fun c ρ => RTBTFromStrength β ρ (BT c)) := by
  intro c c' ρ x hc hc' hconn hconn' hρ himp
  exact RTBTPM_from_BT_ratio_monotonicity hβ
    (fun z => (hρ.1 z).le) (hρ.1 x) (hBT.1 c) (hBT.1 c')
    (fordBT_ratio_monotonicity_of_countImprovement hc hc' hconn hconn' himp
      (hBT.1 c) (hBT.1 c') (hBT.2 c hc hconn) (hBT.2 c' hc' hconn'))

/-- Proposition `RTBTPM` for the total Ford/Zermelo selector. -/
theorem RTBTPM_count_fordZermeloBTSelector
    {β : ℝ} (hβ : 0 < β) :
    SatisfiesCountProbabilisticMonotonicity (α := α)
      (fun c ρ => RTBTFromStrength β ρ (fordZermeloBTSelector c)) :=
  RTBTPM_count_from_selector hβ
    (fordZermeloBTSelector_isStronglyConnectedFordBTSelector (α := α))

/-- Pointwise count-level form of Proposition `RTBTPM` for the Ford/Zermelo
selected Bradley--Terry strengths. -/
theorem RTBTPM_count_selectedBTOfFordZermelo
    {β : ℝ} (hβ : 0 < β)
    {c c' : α → α → ℝ} {ρ : α → ℝ} {x : α}
    (hc : IsFordCountMatrix c) (hc' : IsFordCountMatrix c')
    (hconn : FordStronglyConnected c) (hconn' : FordStronglyConnected c')
    (hρ : IsFullSupportLottery ρ)
    (himp : IsCountImprovementOf c c' x) :
    RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite c hc hconn) x ≤
      RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite c' hc' hconn')
          x :=
  RTBTPM_from_BT_ratio_monotonicity hβ
    (fun z => (hρ.1 z).le) (hρ.1 x)
    (selectedBTOfFordZermelo_pos FordZermeloBTTheorem_finite hc hconn)
    (selectedBTOfFordZermelo_pos FordZermeloBTTheorem_finite hc' hconn')
    (fordBT_ratio_monotonicity_of_countImprovement hc hc' hconn hconn' himp
      (selectedBTOfFordZermelo_pos FordZermeloBTTheorem_finite hc hconn)
      (selectedBTOfFordZermelo_pos FordZermeloBTTheorem_finite hc' hconn')
      (selectedBTOfFordZermelo_satisfiesFordEquations
        FordZermeloBTTheorem_finite hc hconn)
      (selectedBTOfFordZermelo_satisfiesFordEquations
        FordZermeloBTTheorem_finite hc' hconn'))

/-! ## Profile bridges -/

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The paper's improvement conditions (i)–(iii) on weak relations induce a
strict-part improvement of the same candidate. -/
lemma isProfileImprovement_strictPart_of_weakProfileImprovement
    {V : Type*} {R R' : V → α → α → Bool} {x : α}
    (h : IsWeakProfileImprovement R R' x) :
    IsProfileImprovement (strictPart R) (strictPart R') x := by
  refine ⟨?_, ?_, ?_⟩
  · intro i y hyx hxy
    have h1 := h.1 i y hyx
    have h2 := h.2.1 i y hyx
    unfold strictPart strictPrefRel at hxy ⊢
    cases hA : R i x y <;> cases hB : R i y x <;>
      cases hC : R' i x y <;> cases hD : R' i y x <;> simp_all
  · intro i y hyx hyxTrue
    have h1 := h.1 i y hyx
    have h2 := h.2.1 i y hyx
    unfold strictPart strictPrefRel at hyxTrue ⊢
    cases hA : R i x y <;> cases hB : R i y x <;>
      cases hC : R' i x y <;> cases hD : R' i y x <;> simp_all
  · intro i y z hyx hzx
    unfold strictPart strictPrefRel
    rw [h.2.2 i y z hyx hzx, h.2.2 i z y hzx hyx]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Profile improvements act on the strict-count matrices exactly as
count-level improvements. -/
lemma isCountImprovementOf_strictCount_of_profileImprovement
    {V : Type*} [Fintype V] {R R' : V → α → α → Bool} {x : α}
    (h : IsProfileImprovement R R' x) :
    IsCountImprovementOf (strictCount R) (strictCount R') x :=
  ⟨fun y hyx => strictCount_improved_candidate_le_of_profile_improvement h hyx,
    fun y hyx =>
      strictCount_against_improved_candidate_le_of_profile_improvement h hyx,
    fun y z hyx hzx => strictCount_other_eq_of_profile_improvement h hyx hzx⟩

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The paper's (i)–(iii) improvement of a weak-relation profile is a
count-level improvement of the strict-preference counts `c_{x,y}`. -/
lemma isCountImprovementOf_strictCount_strictPart_of_weakProfileImprovement
    {V : Type*} [Fintype V] {R R' : V → α → α → Bool} {x : α}
    (h : IsWeakProfileImprovement R R' x) :
    IsCountImprovementOf (strictCount (strictPart R))
      (strictCount (strictPart R')) x :=
  isCountImprovementOf_strictCount_of_profileImprovement
    (isProfileImprovement_strictPart_of_weakProfileImprovement h)

/-- Proposition `RTBTPM` on weak-relation profiles.  Both `(R,ρ)` and
`(R⁺,ρ)` lie in the paper's domain `𝒟` — exactly the quantification of the
probabilistic-monotonicity axiom — the improvement hypothesis is the paper's
(i)–(iii), and the Bradley--Terry strengths are the Ford/Zermelo selected
solutions for the strict-preference counts, as in `RTBTorder`. -/
theorem RTBTPM_profile_weak_selectedBTOfFordZermelo
    {V : Type*} [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hconn : FordStronglyConnected (strictCount (strictPart R)))
    (hconn' : FordStronglyConnected (strictCount (strictPart R')))
    (hρ : IsFullSupportLottery ρ)
    (himp : IsWeakProfileImprovement R R' x) :
    RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount (strictPart R))
          (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R))
          hconn) x ≤
      RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite
          (strictCount (strictPart R'))
          (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R'))
          hconn') x :=
  RTBTPM_count_selectedBTOfFordZermelo hβ
    (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R))
    (strictCount_isFordCountMatrix (isIrreflexiveProfile_strictPart R'))
    hconn hconn' hρ
    (isCountImprovementOf_strictCount_strictPart_of_weakProfileImprovement himp)

end PaperFormalization
