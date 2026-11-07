import PaperFormalization.NLHFMonotonicityThreshold
import PaperFormalization.NLHFExistence

open scoped BigOperators Topology
open Filter

namespace PaperFormalization

/-!
This file formalizes the finite-comparison core of the appendix proof of
Theorem `NLHFmono`.

The proof is deliberately stated at the level of the endpoint secant system:
the logarithmic-mean identities and the endpoint optimality/KL argument are
kept as explicit hypotheses.  The checked theorem below is the algebraic heart
of the endpoint proof: from those endpoint identities, the
Cauchy/energy estimate and the block comparison imply `q(x) >= p(x)`.
-/

/-- The pointwise margin change for improving `x` against every member of the
block `B` by the same amount `delta`. -/
def blockImprovementChange {α : Type*} [DecidableEq α]
    (x : α) (B : Finset α) (delta : ℝ) (a y : α) : ℝ :=
  (if a = x ∧ y ∈ B then delta else 0) -
    (if a ∈ B ∧ y = x then delta else 0)

/-- A one-pair improvement is the singleton-block instance of
`blockImprovementChange`. -/
lemma improvePairMargin_change_eq_blockImprovementChange_singleton
    {α : Type*} [DecidableEq α]
    (M : α → α → ℝ) {x y : α} (delta : ℝ)
    (hyx : y ≠ x) (a b : α) :
    improvePairMargin M x y delta a b - M a b =
      blockImprovementChange x ({y} : Finset α) delta a b := by
  have hxy : x ≠ y := hyx ∘ Eq.symm
  unfold improvePairMargin blockImprovementChange
  by_cases hax : a = x
  · subst a
    by_cases hby : b = y
    · subst b
      simp [hyx]
    · have hbnot : b ∉ ({y} : Finset α) := by simpa using hby
      simp [hby, hbnot, hxy]
  · by_cases hay : a = y
    · subst a
      by_cases hbx : b = x
      · subst b
        simp [hyx]
      · simp [hax, hbx]
    · have hanot : a ∉ ({y} : Finset α) := by simpa using hay
      simp [hax, hay, hanot]

/-- The logarithmic mean from the paper. -/
noncomputable def logMean (a b : ℝ) : ℝ :=
  if a = b then a else (b - a) / (Real.log b - Real.log a)

lemma logMean_log_sub_mul
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Real.log b - Real.log a) * logMean a b = b - a := by
  unfold logMean
  by_cases h : a = b
  · subst b
    simp
  · rw [if_neg h]
    have hlogne : Real.log b - Real.log a ≠ 0 := by
      intro hzero
      have hlogeq : Real.log b = Real.log a := by linarith
      have hba : b = a := Real.log_injOn_pos hb ha hlogeq
      exact h hba.symm
    field_simp [hlogne]

lemma logMean_ne_zero
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logMean a b ≠ 0 := by
  unfold logMean
  by_cases h : a = b
  · rw [if_pos h]
    exact ne_of_gt ha
  · rw [if_neg h]
    have hba : b - a ≠ 0 := by
      intro hzero
      have hbaeq : b = a := by linarith
      exact h hbaeq.symm
    have hlogne : Real.log b - Real.log a ≠ 0 := by
      intro hzero
      have hlogeq : Real.log b = Real.log a := by linarith
      have hbaeq : b = a := Real.log_injOn_pos hb ha hlogeq
      exact h hbaeq.symm
    exact div_ne_zero hba hlogne

lemma logMean_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < logMean a b := by
  unfold logMean
  by_cases h : a = b
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hab | hba
    · have hnum : 0 < b - a := by linarith
      have hlog : 0 < Real.log b - Real.log a := by
        have := Real.log_lt_log ha hab
        linarith
      exact div_pos hnum hlog
    · have hnum : b - a < 0 := by linarith
      have hlog : Real.log b - Real.log a < 0 := by
        have := Real.log_lt_log hb hba
        linarith
      exact div_pos_of_neg_of_neg hnum hlog

lemma logMean_log_identity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (b / a) = (b - a) / logMean a b := by
  have hmul := logMean_log_sub_mul (a := a) (b := b) ha hb
  have hLne := logMean_ne_zero (a := a) (b := b) ha hb
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)]
  field_simp [hLne]
  linarith

lemma logMean_comm_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logMean a b = logMean b a := by
  unfold logMean
  by_cases h : a = b
  · subst b
    simp
  · have h' : b ≠ a := by exact h ∘ Eq.symm
    rw [if_neg h, if_neg h']
    have hlogne : Real.log b - Real.log a ≠ 0 := by
      intro hzero
      have hlogeq : Real.log b = Real.log a := by linarith
      have hba : b = a := Real.log_injOn_pos hb ha hlogeq
      exact h hba.symm
    have hlogne' : Real.log a - Real.log b ≠ 0 := by
      intro hzero
      have hzero' : Real.log b - Real.log a = 0 := by linarith
      exact hlogne hzero'
    field_simp [hlogne, hlogne']
    ring

lemma logMean_log_reverse_identity
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a / b) = (a - b) / logMean a b := by
  have h := logMean_log_identity (a := b) (b := a) hb ha
  rw [logMean_comm_of_pos hb ha] at h
  exact h

lemma logMean_mul_left {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    logMean (c * a) (c * b) = c * logMean a b := by
  unfold logMean
  by_cases h : a = b
  · subst b
    rw [if_pos rfl, if_pos rfl]
  · have hcne : c ≠ 0 := hc.ne'
    have hcab : c * a ≠ c * b := by
      intro hmul
      exact h (mul_left_cancel₀ hcne hmul)
    rw [if_neg hcab, if_neg h]
    have hlogc :
        Real.log (c * b) - Real.log (c * a) =
          Real.log b - Real.log a := by
      rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hb),
        Real.log_mul (ne_of_gt hc) (ne_of_gt ha)]
      ring
    rw [hlogc]
    ring

lemma one_le_logMean_one_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    1 ≤ logMean 1 t := by
  rcases eq_or_lt_of_le ht with h | hlt
  · subst t
    unfold logMean
    simp
  · have htpos : 0 < t := by linarith
    unfold logMean
    have hone : (1 : ℝ) ≠ t := by linarith
    rw [if_neg hone, Real.log_one]
    simp only [sub_zero]
    have hlogpos : 0 < Real.log t := Real.log_pos hlt
    rw [le_div_iff₀ hlogpos]
    have hle := Real.log_le_sub_one_of_pos htpos
    linarith

/-- The normalized weighted AM-GM estimate used pointwise in the proof of the
logarithmic-mean block-sum inequality. -/
lemma weighted_geom_sum_ratio_le_one
    {α : Type*} [Fintype α]
    {B : Finset α} {p q : α → ℝ} {P Q t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : ∀ i ∈ B, 0 ≤ p i) (hq : ∀ i ∈ B, 0 ≤ q i)
    (hPpos : 0 < P) (hQpos : 0 < Q)
    (hP : P = B.sum (fun i => p i))
    (hQ : Q = B.sum (fun i => q i)) :
    B.sum (fun i => (p i / P) ^ (1 - t) * (q i / Q) ^ t) ≤ 1 := by
  have hpoint : ∀ i ∈ B,
      (p i / P) ^ (1 - t) * (q i / Q) ^ t ≤
        (1 - t) * (p i / P) + t * (q i / Q) := by
    intro i hi
    exact Real.geom_mean_le_arith_mean2_weighted
      (sub_nonneg.mpr ht1) ht0
      (div_nonneg (hp i hi) hPpos.le)
      (div_nonneg (hq i hi) hQpos.le)
      (by ring)
  have hsum_le :
      B.sum (fun i => (p i / P) ^ (1 - t) * (q i / Q) ^ t) ≤
        B.sum (fun i => (1 - t) * (p i / P) + t * (q i / Q)) :=
    Finset.sum_le_sum hpoint
  have hsum_eq :
      B.sum (fun i => (1 - t) * (p i / P) + t * (q i / Q)) = 1 := by
    calc
      B.sum (fun i => (1 - t) * (p i / P) + t * (q i / Q)) =
        (1 - t) * B.sum (fun i => p i / P) +
          t * B.sum (fun i => q i / Q) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = (1 - t) * (B.sum (fun i => p i) / P) +
          t * (B.sum (fun i => q i) / Q) := by
          rw [Finset.sum_div, Finset.sum_div]
      _ = 1 := by
          rw [← hP, ← hQ]
          field_simp [hPpos.ne', hQpos.ne']
          ring
  linarith

lemma rpow_ratio_mul_eq
    {p q P Q t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hP : 0 < P) (hQ : 0 < Q) :
    P ^ (1 - t) * Q ^ t *
        ((p / P) ^ (1 - t) * (q / Q) ^ t) =
      p ^ (1 - t) * q ^ t := by
  rw [Real.div_rpow hp.le hP.le, Real.div_rpow hq.le hQ.le]
  have hPpow : P ^ (1 - t) ≠ 0 := (Real.rpow_pos_of_pos hP _).ne'
  have hQpow : Q ^ t ≠ 0 := (Real.rpow_pos_of_pos hQ _).ne'
  field_simp [hPpow, hQpow]

/-- The unnormalized weighted AM-GM estimate used under the integral in the
block-sum proof. -/
lemma weighted_geometric_sum_le
    {α : Type*} [Fintype α]
    {B : Finset α} {p q : α → ℝ} {P Q t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : ∀ i ∈ B, 0 < p i) (hq : ∀ i ∈ B, 0 < q i)
    (hPpos : 0 < P) (hQpos : 0 < Q)
    (hP : P = B.sum (fun i => p i))
    (hQ : Q = B.sum (fun i => q i)) :
    B.sum (fun i => p i ^ (1 - t) * q i ^ t) ≤
      P ^ (1 - t) * Q ^ t := by
  let C : ℝ := P ^ (1 - t) * Q ^ t
  have hnorm := weighted_geom_sum_ratio_le_one
    (B := B) (p := p) (q := q) (P := P) (Q := Q) (t := t)
    ht0 ht1 (fun i hi => (hp i hi).le) (fun i hi => (hq i hi).le)
    hPpos hQpos hP hQ
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmul := mul_le_mul_of_nonneg_left hnorm hCnonneg
  have hCsum :
      C * B.sum (fun i => (p i / P) ^ (1 - t) * (q i / Q) ^ t) =
        B.sum (fun i => p i ^ (1 - t) * q i ^ t) := by
    dsimp [C]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact rpow_ratio_mul_eq (hp i hi) (hq i hi) hPpos hQpos
  rw [hCsum] at hmul
  dsimp [C] at hmul
  simpa using hmul

/-- Antiderivative for `exp (c * x) / c`, used to prove the integral formula
for the logarithmic mean without relying on a specialized library lemma. -/
lemma hasDerivAt_exp_mul_div {c x : ℝ} (hc : c ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.exp (c * y) / c) (Real.exp (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hcomp : HasDerivAt (fun y : ℝ => Real.exp (c * y))
      (Real.exp (c * x) * c) x := by
    simpa using (Real.hasDerivAt_exp (c * x)).comp x hinner
  have hdiv := hcomp.div_const c
  convert hdiv using 1
  field_simp [hc]

lemma integral_exp_mul {c a b : ℝ} (hc : c ≠ 0) :
    ∫ x in a..b, Real.exp (c * x) =
      (Real.exp (c * b) - Real.exp (c * a)) / c := by
  have hderiv : deriv (fun y : ℝ => Real.exp (c * y) / c) =
      fun y => Real.exp (c * y) := by
    funext y
    exact (hasDerivAt_exp_mul_div (c := c) (x := y) hc).deriv
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun y : ℝ => Real.exp (c * y) / c) hderiv
    (fun x hx => (hasDerivAt_exp_mul_div (c := c) (x := x) hc).differentiableAt)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)]
  ring

lemma rpow_product_eq_exp {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a ^ (1 - t) * b ^ t =
      a * Real.exp ((Real.log b - Real.log a) * t) := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb]
  rw [← Real.exp_add]
  rw [← Real.exp_log ha]
  rw [← Real.exp_add]
  congr 1
  simp [Real.exp_log ha]
  ring

/-- Integral representation of the logarithmic mean. -/
lemma logMean_integral_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..1, a ^ (1 - t) * b ^ t) = logMean a b := by
  unfold logMean
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    have hconst :
        Set.EqOn (fun t : ℝ => a ^ (1 - t) * a ^ t) (fun _ : ℝ => a)
          (Set.uIcc (0 : ℝ) 1) := by
      intro t ht
      change a ^ (1 - t) * a ^ t = a
      rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos ha, ← Real.exp_add]
      rw [← Real.exp_log ha]
      congr 1
      simp [Real.exp_log ha]
      ring
    rw [intervalIntegral.integral_congr hconst]
    rw [intervalIntegral.integral_const]
    norm_num
  · rw [if_neg hab]
    let c : ℝ := Real.log b - Real.log a
    have hc : c ≠ 0 := by
      intro hzero
      have hlogeq : Real.log b = Real.log a := by
        dsimp [c] at hzero
        linarith
      have hba : b = a := Real.log_injOn_pos hb ha hlogeq
      exact hab hba.symm
    have hcongr :
        (∫ t in (0 : ℝ)..1, a ^ (1 - t) * b ^ t) =
          ∫ t in (0 : ℝ)..1, a * Real.exp (c * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [c]
      exact rpow_product_eq_exp ha hb
    rw [hcongr]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_exp_mul (c := c) (a := (0 : ℝ)) (b := 1) hc]
    dsimp [c]
    rw [mul_zero, Real.exp_zero]
    simp only [mul_one]
    have hexp : Real.exp (Real.log b - Real.log a) = b / a := by
      rw [Real.exp_sub]
      rw [Real.exp_log hb, Real.exp_log ha]
    rw [hexp]
    field_simp [ha.ne']

lemma continuous_rpow_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous fun t : ℝ => a ^ (1 - t) * b ^ t := by
  have hcont :
      Continuous fun t : ℝ =>
        a * Real.exp ((Real.log b - Real.log a) * t) := by
    exact continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  exact hcont.congr (fun t => (rpow_product_eq_exp ha hb).symm)

lemma intervalIntegrable_rpow_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => a ^ (1 - t) * b ^ t)
      MeasureTheory.volume (0 : ℝ) 1 :=
  (continuous_rpow_product ha hb).intervalIntegrable 0 1

/-- The logarithmic mean is superadditive in the block direction needed in
the proof.  This is obtained from its integral representation and the
pointwise weighted AM-GM estimate. -/
lemma logMean_block_sum_le
    {α : Type*} [Fintype α]
    {B : Finset α} {p q : α → ℝ}
    (hB : B.Nonempty)
    (hp : ∀ i ∈ B, 0 < p i)
    (hq : ∀ i ∈ B, 0 < q i) :
    B.sum (fun i => logMean (p i) (q i)) ≤
      logMean (B.sum (fun i => p i)) (B.sum (fun i => q i)) := by
  classical
  let P : ℝ := B.sum (fun i => p i)
  let Q : ℝ := B.sum (fun i => q i)
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.sum_pos hp hB
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.sum_pos hq hB
  have hint_i :
      ∀ i ∈ B,
        IntervalIntegrable (fun t : ℝ => p i ^ (1 - t) * q i ^ t)
          MeasureTheory.volume (0 : ℝ) 1 := by
    intro i hi
    exact intervalIntegrable_rpow_product (hp i hi) (hq i hi)
  have hsum_integral :
      B.sum (fun i => logMean (p i) (q i)) =
        ∫ t in (0 : ℝ)..1, B.sum (fun i => p i ^ (1 - t) * q i ^ t) := by
    calc
      B.sum (fun i => logMean (p i) (q i)) =
          B.sum (fun i =>
            ∫ t in (0 : ℝ)..1, p i ^ (1 - t) * q i ^ t) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact (logMean_integral_eq (hp i hi) (hq i hi)).symm
      _ = ∫ t in (0 : ℝ)..1, B.sum (fun i => p i ^ (1 - t) * q i ^ t) := by
          rw [intervalIntegral.integral_finset_sum hint_i]
  have htarget_integral :
      logMean P Q =
        ∫ t in (0 : ℝ)..1, P ^ (1 - t) * Q ^ t :=
    (logMean_integral_eq hPpos hQpos).symm
  have hint_sum :
      IntervalIntegrable
        (fun t : ℝ => B.sum (fun i => p i ^ (1 - t) * q i ^ t))
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcont :
        Continuous fun t : ℝ =>
          B.sum (fun i => p i ^ (1 - t) * q i ^ t) :=
      continuous_finset_sum B
        (fun i hi => continuous_rpow_product (hp i hi) (hq i hi))
    exact hcont.intervalIntegrable 0 1
  have hint_target :
      IntervalIntegrable (fun t : ℝ => P ^ (1 - t) * Q ^ t)
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_rpow_product hPpos hQpos
  have hmono :
      (∫ t in (0 : ℝ)..1, B.sum (fun i => p i ^ (1 - t) * q i ^ t)) ≤
        ∫ t in (0 : ℝ)..1, P ^ (1 - t) * Q ^ t := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint_sum hint_target ?_
    intro t ht
    exact weighted_geometric_sum_le
      (B := B) (p := p) (q := q) (P := P) (Q := Q) (t := t)
      ht.1 ht.2 hp hq hPpos hQpos rfl rfl
  rw [hsum_integral, htarget_integral]
  exact hmono

/-- Display `TwoIntegrals` in the paper's proof of Lemma `log-mean-sums`: the
integral representation of the logarithmic mean (Fact `log-mean`(2)) with the
first argument factored out, `L(P,Q) = P ∫₀¹ (Q/P)^t dt`. -/
lemma logMean_eq_mul_integral_ratio_rpow {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) :
    logMean P Q = P * ∫ t in (0 : ℝ)..1, (Q / P) ^ t := by
  have hQP : 0 < Q / P := div_pos hQ hP
  have hone : (0 : ℝ) < 1 := by norm_num
  have hscale : logMean P Q = P * logMean 1 (Q / P) := by
    have h := logMean_mul_left (c := P) (a := 1) (b := Q / P) hP hone hQP
    have hPQ : P * (Q / P) = Q := by field_simp [hP.ne']
    simpa [hPQ] using h
  have hint :
      (∫ t in (0 : ℝ)..1, (1 : ℝ) ^ (1 - t) * (Q / P) ^ t) =
        ∫ t in (0 : ℝ)..1, (Q / P) ^ t := by
    apply intervalIntegral.integral_congr
    intro t _
    simp [Real.one_rpow]
  rw [hscale, ← logMean_integral_eq hone hQP, hint]

/-- Ratio monotonicity of the logarithmic mean, Lemma `log-mean-sums`(2), by
the paper's argument: by display `TwoIntegrals`, `L(P,Q) = P ∫₀¹ (Q/P)^t dt`
and `L(r,s) = r ∫₀¹ (s/r)^t dt`; since `Q/P ≤ s/r`, the integrands satisfy
`(Q/P)^t ≤ (s/r)^t` for `t ∈ [0,1]`, so the first integral is at most the
second; the second integral is positive; hence `L(P,Q)/L(r,s) ≤ P/r`. -/
lemma logMean_ratio_le_of_ratio
    {P Q r s : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hr : 0 < r) (hs : 0 < s)
    (hratio : Q / P ≤ s / r) :
    logMean P Q / logMean r s ≤ P / r := by
  have hQP : 0 < Q / P := div_pos hQ hP
  have hsr : 0 < s / r := div_pos hs hr
  have hone : (0 : ℝ) < 1 := by norm_num
  -- Display `TwoIntegrals`.
  have hPQ : logMean P Q = P * ∫ t in (0 : ℝ)..1, (Q / P) ^ t :=
    logMean_eq_mul_integral_ratio_rpow hP hQ
  have hrs : logMean r s = r * ∫ t in (0 : ℝ)..1, (s / r) ^ t :=
    logMean_eq_mul_integral_ratio_rpow hr hs
  -- Both integrands are continuous, hence integrable on `[0,1]`.
  have hintQP :
      IntervalIntegrable (fun t : ℝ => (Q / P) ^ t)
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcont : Continuous fun t : ℝ => (Q / P) ^ t :=
      (continuous_rpow_product hone hQP).congr
        (fun t => by simp [Real.one_rpow])
    exact hcont.intervalIntegrable 0 1
  have hintsr :
      IntervalIntegrable (fun t : ℝ => (s / r) ^ t)
        MeasureTheory.volume (0 : ℝ) 1 := by
    have hcont : Continuous fun t : ℝ => (s / r) ^ t :=
      (continuous_rpow_product hone hsr).congr
        (fun t => by simp [Real.one_rpow])
    exact hcont.intervalIntegrable 0 1
  -- `(Q/P)^t ≤ (s/r)^t` for each `t ∈ [0,1]`, hence for the integrals.
  have hmono :
      (∫ t in (0 : ℝ)..1, (Q / P) ^ t) ≤ ∫ t in (0 : ℝ)..1, (s / r) ^ t := by
    refine intervalIntegral.integral_mono_on (by norm_num) hintQP hintsr ?_
    intro t ht
    exact Real.rpow_le_rpow hQP.le hratio ht.1
  -- The second integral in `TwoIntegrals` is positive.
  have hpos : 0 < ∫ t in (0 : ℝ)..1, (s / r) ^ t := by
    have h : 0 < r * ∫ t in (0 : ℝ)..1, (s / r) ^ t := by
      rw [← hrs]
      exact logMean_pos hr hs
    exact pos_of_mul_pos_right h hr.le
  rw [hPQ, hrs, div_le_div_iff₀ (mul_pos hr hpos) hr]
  have hmul := mul_le_mul_of_nonneg_left hmono (mul_nonneg hP.le hr.le)
  nlinarith

/-- The standard elementary lower bound
`2 * (t - 1) / (t + 1) ≤ log t`, written in the form needed for the
logarithmic-mean arithmetic bound. -/
lemma log_lower_two_mul_sub_div_add {t : ℝ} (ht : 1 ≤ t) :
    2 * (t - 1) / (t + 1) ≤ Real.log t := by
  have hx : 0 ≤ t - 1 := sub_nonneg.mpr ht
  have h := Real.le_log_one_add_of_nonneg hx
  convert h using 1 <;> ring_nf

/-- The logarithmic mean is bounded above by the arithmetic mean, in the
ordered case. -/
lemma logMean_arithmetic_le_ordered
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    logMean a b ≤ (a + b) / 2 := by
  unfold logMean
  by_cases heq : a = b
  · rw [if_pos heq]
    linarith
  · rw [if_neg heq]
    have hlt : a < b := lt_of_le_of_ne hab heq
    have hdenpos : 0 < Real.log b - Real.log a := by
      have hlog := Real.log_lt_log ha hlt
      linarith
    have hsumpos : 0 < (a + b) / 2 := by positivity
    have hratio : 2 * (b - a) / (a + b) ≤ Real.log b - Real.log a := by
      have ht : 1 ≤ b / a := by
        rw [le_div_iff₀ ha]
        nlinarith
      have h := log_lower_two_mul_sub_div_add ht
      have hlogdiv : Real.log (b / a) = Real.log b - Real.log a := by
        rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)]
      have hleft :
          2 * (b / a - 1) / (b / a + 1) =
            2 * (b - a) / (a + b) := by
        field_simp [ha.ne']
        ring_nf
      rwa [hlogdiv, hleft] at h
    rw [div_le_iff₀ hdenpos]
    have hmul := mul_le_mul_of_nonneg_left hratio hsumpos.le
    have hleft_eq :
        (a + b) / 2 * (2 * (b - a) / (a + b)) = b - a := by
      have hsumne : a + b ≠ 0 := by positivity
      field_simp [hsumne]
    nlinarith

/-- The logarithmic mean is bounded above by the arithmetic mean. -/
lemma logMean_arithmetic_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logMean a b ≤ (a + b) / 2 := by
  rcases le_total a b with hab | hba
  · exact logMean_arithmetic_le_ordered ha hb hab
  · have h := logMean_arithmetic_le_ordered hb ha hba
    rw [logMean_comm_of_pos ha hb]
    linarith

/-- The logarithmic mean lies between its two positive inputs. -/
lemma logMean_between_ordered {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) :
    a ≤ logMean a b ∧ logMean a b ≤ b := by
  have hscale : logMean a b = a * logMean 1 (b / a) := by
    have hba : 0 < b / a := div_pos hb ha
    have h := logMean_mul_left
      (c := a) (a := 1) (b := b / a) ha (by norm_num) hba
    have hab' : a * (b / a) = b := by field_simp [ha.ne']
    simpa [hab'] using h
  have hratio_ge : 1 ≤ b / a := by
    rw [le_div_iff₀ ha]
    simpa using hab
  have hLge : 1 ≤ logMean 1 (b / a) :=
    one_le_logMean_one_of_one_le hratio_ge
  constructor
  · rw [hscale]
    nlinarith
  · have hle := logMean_arithmetic_le ha hb
    nlinarith

/-- Moving one endpoint by `b - a` moves the logarithmic mean by no more than
that endpoint move. -/
lemma logMean_abs_sub_left_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |logMean a b - a| ≤ |b - a| := by
  rcases le_total a b with hab | hba
  · rcases logMean_between_ordered ha hb hab with ⟨hlo, hhi⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hlo),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith
  · have hcomm := logMean_comm_of_pos ha hb
    rcases logMean_between_ordered hb ha hba with ⟨hlo, hhi⟩
    rw [hcomm]
    rw [abs_of_nonpos (sub_nonpos.mpr hhi),
      abs_of_nonpos (sub_nonpos.mpr hba)]
    linarith

/-- Endpoint continuity of the logarithmic mean in the second argument.  This
is the elementary topological substep used when the finite-secant quantities
are specialized to a path of nearby NLHF fixed points. -/
lemma tendsto_logMean_right
    {ι : Type*} {l : Filter ι} {a : ℝ} {f : ι → ℝ}
    (ha : 0 < a) (hf : Filter.Tendsto f l (𝓝 a)) :
    Filter.Tendsto (fun s => logMean a (f s)) l (𝓝 a) := by
  let g : ι → ℝ := fun s => if 0 < f s then logMean a (f s) else a
  have hg_abs : Filter.Tendsto (fun s => |g s - a|) l (𝓝 0) := by
    have hnonneg : ∀ s : ι, 0 ≤ |g s - a| := fun s => abs_nonneg _
    have hle : ∀ s : ι, |g s - a| ≤ |f s - a| := by
      intro s
      by_cases hfs : 0 < f s
      · simp [g, hfs]
        exact logMean_abs_sub_left_le ha hfs
      · simp [g, hfs]
    have hf_abs : Filter.Tendsto (fun s => |f s - a|) l (𝓝 0) := by
      have hsub : Filter.Tendsto (fun s => f s - a) l (𝓝 (a - a)) :=
        hf.sub tendsto_const_nhds
      have hsub0 : Filter.Tendsto (fun s => f s - a) l (𝓝 0) := by
        simpa using hsub
      have habs := (continuous_abs.tendsto 0).comp hsub0
      simpa using habs
    exact squeeze_zero hnonneg hle hf_abs
  have hg : Filter.Tendsto g l (𝓝 a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using hg_abs
  have hpos_event : ∀ᶠ s in l, 0 < f s :=
    hf.eventually (Ioi_mem_nhds ha)
  have heq : g =ᶠ[l] fun s => logMean a (f s) := by
    filter_upwards [hpos_event] with s hs
    simp [g, hs]
  exact Filter.Tendsto.congr' heq hg

/-- Two-variable endpoint continuity of the logarithmic mean at a positive
limit.  In the converse proof, this is the elementary step turning convergence
of the old and improved fixed-point probabilities into convergence of the
secant logarithmic means. -/
lemma tendsto_logMean
    {ι : Type*} {l : Filter ι} {a : ℝ} {f g : ι → ℝ}
    (ha : 0 < a)
    (hf : Filter.Tendsto f l (𝓝 a))
    (hg : Filter.Tendsto g l (𝓝 a)) :
    Filter.Tendsto (fun s => logMean (f s) (g s)) l (𝓝 a) := by
  let L : ι → ℝ :=
    fun s => if 0 < f s ∧ 0 < g s then logMean (f s) (g s) else a
  have hL_abs : Filter.Tendsto (fun s => |L s - a|) l (𝓝 0) := by
    have hnonneg : ∀ s : ι, 0 ≤ |L s - a| := fun s => abs_nonneg _
    have hle : ∀ s : ι, |L s - a| ≤ |g s - f s| + |f s - a| := by
      intro s
      by_cases hpos : 0 < f s ∧ 0 < g s
      · have htri :
            |logMean (f s) (g s) - a| ≤
              |logMean (f s) (g s) - f s| + |f s - a| := by
          calc
            |logMean (f s) (g s) - a|
                = |(logMean (f s) (g s) - f s) + (f s - a)| := by ring_nf
            _ ≤ |logMean (f s) (g s) - f s| + |f s - a| :=
                abs_add_le _ _
        have hmove :
            |logMean (f s) (g s) - f s| ≤ |g s - f s| :=
          logMean_abs_sub_left_le hpos.1 hpos.2
        dsimp [L]
        rw [if_pos hpos]
        exact le_trans htri (add_le_add hmove le_rfl)
      · dsimp [L]
        rw [if_neg hpos]
        simpa using add_nonneg (abs_nonneg (g s - f s)) (abs_nonneg (f s - a))
    have hgf_abs : Filter.Tendsto (fun s => |g s - f s|) l (𝓝 0) := by
      have hsub : Filter.Tendsto (fun s => g s - f s) l (𝓝 (a - a)) :=
        hg.sub hf
      have hsub0 : Filter.Tendsto (fun s => g s - f s) l (𝓝 0) := by
        simpa using hsub
      have habs := (continuous_abs.tendsto 0).comp hsub0
      simpa using habs
    have hf_abs : Filter.Tendsto (fun s => |f s - a|) l (𝓝 0) := by
      have hsub : Filter.Tendsto (fun s => f s - a) l (𝓝 (a - a)) :=
        hf.sub tendsto_const_nhds
      have hsub0 : Filter.Tendsto (fun s => f s - a) l (𝓝 0) := by
        simpa using hsub
      have habs := (continuous_abs.tendsto 0).comp hsub0
      simpa using habs
    have hsum :
        Filter.Tendsto (fun s => |g s - f s| + |f s - a|) l (𝓝 0) := by
      simpa using hgf_abs.add hf_abs
    exact squeeze_zero hnonneg hle hsum
  have hL : Filter.Tendsto L l (𝓝 a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using hL_abs
  have hfpos : ∀ᶠ s in l, 0 < f s :=
    hf.eventually (Ioi_mem_nhds ha)
  have hgpos : ∀ᶠ s in l, 0 < g s :=
    hg.eventually (Ioi_mem_nhds ha)
  have heq : L =ᶠ[l] fun s => logMean (f s) (g s) := by
    filter_upwards [hfpos, hgpos] with s hfs hgs
    simp [L, hfs, hgs]
  exact Filter.Tendsto.congr' heq hL

/-- Conditional low-temperature bridge for the three-candidate converse.  Once
the two endpoint probabilities for `y` converge to `muy`, the two endpoint
probabilities for `z` converge to `mux`, and the coefficient `D` converges to
`d`, the checked finite-secant formula produces an actual strict drop for some
small positive improvement whenever the limiting numerator is negative. -/
theorem exists_threeCandidateSecant_drop_of_probability_tendsto
    {oldY newY oldZ newZ D den Δx : ℝ → ℝ}
    {lam mux muy d ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε)
    (hmux : 0 < mux) (hmuy : 0 < muy)
    (holdY : Filter.Tendsto oldY (𝓝[>] (0 : ℝ)) (𝓝 muy))
    (hnewY : Filter.Tendsto newY (𝓝[>] (0 : ℝ)) (𝓝 muy))
    (holdZ : Filter.Tendsto oldZ (𝓝[>] (0 : ℝ)) (𝓝 mux))
    (hnewZ : Filter.Tendsto newZ (𝓝[>] (0 : ℝ)) (𝓝 mux))
    (hD : Filter.Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hlimitneg : 2 + muy / mux - lam * d * mux < 0)
    (hden : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < den s)
    (hformula : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Δx s =
        lam * s *
          (mux / logMean (oldZ s) (newZ s) +
            muy / logMean (oldY s) (newY s) +
            muy / logMean (oldZ s) (newZ s) -
            lam * D s * mux) / den s) :
    ∃ s : ℝ, 0 < s ∧ s < ε ∧ Δx s < 0 := by
  let N : ℝ → ℝ := fun s =>
    mux / logMean (oldZ s) (newZ s) +
      muy / logMean (oldY s) (newY s) +
      muy / logMean (oldZ s) (newZ s) -
      lam * D s * mux
  have hLy :
      Filter.Tendsto (fun s => logMean (oldY s) (newY s))
        (𝓝[>] (0 : ℝ)) (𝓝 muy) :=
    tendsto_logMean hmuy holdY hnewY
  have hLz :
      Filter.Tendsto (fun s => logMean (oldZ s) (newZ s))
        (𝓝[>] (0 : ℝ)) (𝓝 mux) :=
    tendsto_logMean hmux holdZ hnewZ
  have hN :
      Filter.Tendsto N (𝓝[>] (0 : ℝ))
        (𝓝 (2 + muy / mux - lam * d * mux)) := by
    dsimp [N]
    exact threeCandidateSecant_numerator_tendsto
      (lam := lam) (mux := mux) (muy := muy) (d := d)
      hmux hmuy hLy hLz hD
  exact exists_threeCandidateSecant_drop_of_tendsto_negative_numerator
    (N := N) (den := den) (Δx := Δx) (lam := lam)
    hlam hε hlimitneg hN hden hformula

/-- Sequence form of `exists_threeCandidateSecant_drop_of_probability_tendsto`.
This is the form used with the sequential continuity proof for the selected
NLHF fixed point. -/
theorem exists_threeCandidateSecant_drop_of_probability_tendsto_seq
    {sseq oldY newY oldZ newZ D den Δx : ℕ → ℝ}
    {lam mux muy d ε : ℝ}
    (hlam : 0 < lam)
    (hspos : ∀ᶠ n in Filter.atTop, 0 < sseq n)
    (hslt : ∀ᶠ n in Filter.atTop, sseq n < ε)
    (hmux : 0 < mux) (hmuy : 0 < muy)
    (holdY : Filter.Tendsto oldY Filter.atTop (𝓝 muy))
    (hnewY : Filter.Tendsto newY Filter.atTop (𝓝 muy))
    (holdZ : Filter.Tendsto oldZ Filter.atTop (𝓝 mux))
    (hnewZ : Filter.Tendsto newZ Filter.atTop (𝓝 mux))
    (hD : Filter.Tendsto D Filter.atTop (𝓝 d))
    (hlimitneg : 2 + muy / mux - lam * d * mux < 0)
    (hden : ∀ᶠ n in Filter.atTop, 0 < den n)
    (hformula : ∀ᶠ n in Filter.atTop,
      Δx n =
        lam * sseq n *
          (mux / logMean (oldZ n) (newZ n) +
            muy / logMean (oldY n) (newY n) +
            muy / logMean (oldZ n) (newZ n) -
            lam * D n * mux) / den n) :
    ∃ n : ℕ, 0 < sseq n ∧ sseq n < ε ∧ Δx n < 0 := by
  let N : ℕ → ℝ := fun n =>
    mux / logMean (oldZ n) (newZ n) +
      muy / logMean (oldY n) (newY n) +
      muy / logMean (oldZ n) (newZ n) -
      lam * D n * mux
  have hLy :
      Filter.Tendsto (fun n => logMean (oldY n) (newY n))
        Filter.atTop (𝓝 muy) :=
    tendsto_logMean hmuy holdY hnewY
  have hLz :
      Filter.Tendsto (fun n => logMean (oldZ n) (newZ n))
        Filter.atTop (𝓝 mux) :=
    tendsto_logMean hmux holdZ hnewZ
  have hN :
      Filter.Tendsto N Filter.atTop
        (𝓝 (2 + muy / mux - lam * d * mux)) := by
    dsimp [N]
    exact threeCandidateSecant_numerator_tendsto
      (lam := lam) (mux := mux) (muy := muy) (d := d)
      hmux hmuy hLy hLz hD
  have hneg : ∀ᶠ n in Filter.atTop, N n < 0 :=
    hN.eventually_lt_const hlimitneg
  have hgood : ∀ᶠ n in Filter.atTop,
      N n < 0 ∧ 0 < den n ∧
        Δx n = lam * sseq n * N n / den n ∧
        0 < sseq n ∧ sseq n < ε := by
    filter_upwards [hneg, hden, hformula, hspos, hslt] with n hn hd hf hp hlt
    exact ⟨hn, hd, hf, hp, hlt⟩
  rcases hgood.exists with ⟨n, hn, hd, hf, hp, hlt⟩
  exact ⟨n, hp, hlt,
    threeCandidateSecant_drop_of_negative_numerator hlam hp hn hd hf⟩

/-- The total logarithmic-mean weight bound, assuming the elementary
arithmetic-mean upper bound for each coordinate. -/
lemma logMean_total_weight_le_one_of_arithmetic
    {α : Type*} [Fintype α]
    {p q : α → ℝ} {pX qX : ℝ}
    (hp_total : pX + Finset.univ.sum (fun i => p i) = 1)
    (hq_total : qX + Finset.univ.sum (fun i => q i) = 1)
    (hX : logMean pX qX ≤ (pX + qX) / 2)
    (hcoord : ∀ i : α, logMean (p i) (q i) ≤ (p i + q i) / 2) :
    logMean pX qX +
        Finset.univ.sum (fun i => logMean (p i) (q i)) ≤ 1 := by
  have hsum :
      Finset.univ.sum (fun i => logMean (p i) (q i)) ≤
        Finset.univ.sum (fun i => (p i + q i) / 2) :=
    Finset.sum_le_sum (fun i _hi => hcoord i)
  have hsum_avg :
      Finset.univ.sum (fun i => (p i + q i) / 2) =
        (Finset.univ.sum (fun i => p i) +
          Finset.univ.sum (fun i => q i)) / 2 := by
    calc
      Finset.univ.sum (fun i => (p i + q i) / 2) =
        Finset.univ.sum (fun i => p i / 2 + q i / 2) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
      _ = Finset.univ.sum (fun i => p i / 2) +
          Finset.univ.sum (fun i => q i / 2) := by
          rw [Finset.sum_add_distrib]
      _ = (Finset.univ.sum (fun i => p i) +
          Finset.univ.sum (fun i => q i)) / 2 := by
          rw [← Finset.sum_div Finset.univ (fun i => p i) 2,
            ← Finset.sum_div Finset.univ (fun i => q i) 2]
          ring
  have havg :
      (pX + qX) / 2 +
        Finset.univ.sum (fun i => (p i + q i) / 2) = 1 := by
    rw [hsum_avg]
    nlinarith
  linarith

/-- The paper's total logarithmic-mean weight bound, with the arithmetic
logarithmic-mean bound supplied by `logMean_arithmetic_le`. -/
lemma logMean_total_weight_le_one
    {α : Type*} [Fintype α]
    {p q : α → ℝ} {pX qX : ℝ}
    (hpX : 0 < pX) (hqX : 0 < qX)
    (hp : ∀ i : α, 0 < p i) (hq : ∀ i : α, 0 < q i)
    (hp_total : pX + Finset.univ.sum (fun i => p i) = 1)
    (hq_total : qX + Finset.univ.sum (fun i => q i) = 1) :
    logMean pX qX +
        Finset.univ.sum (fun i => logMean (p i) (q i)) ≤ 1 :=
  logMean_total_weight_le_one_of_arithmetic hp_total hq_total
    (logMean_arithmetic_le hpX hqX)
    (fun i => logMean_arithmetic_le (hp i) (hq i))

lemma block_probability_ratio_le_of_odds
    {pX qX PB QB : ℝ}
    (hpX : 0 < pX) (hPB : 0 < PB)
    (hodds : pX * QB ≤ qX * PB) :
    QB / PB ≤ qX / pX := by
  rw [div_le_div_iff₀ hPB hpX]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hodds

lemma logMean_block_ratio_from_sum_and_ratio
    {α : Type*} [Fintype α]
    {p q : α → ℝ} {pX qX PB QB : ℝ} {B : Finset α}
    (hpX : 0 < pX) (hqX : 0 < qX)
    (hblockSum :
      B.sum (fun i => logMean (p i) (q i)) ≤ logMean PB QB)
    (hratio :
      logMean PB QB / logMean pX qX ≤ PB / pX) :
    B.sum (fun i => logMean (p i) (q i)) / logMean pX qX ≤
      PB / pX := by
  have hden : 0 < logMean pX qX := logMean_pos hpX hqX
  have hdiv :
      B.sum (fun i => logMean (p i) (q i)) / logMean pX qX ≤
        logMean PB QB / logMean pX qX :=
    div_le_div_of_nonneg_right hblockSum hden.le
  exact le_trans hdiv hratio

/-- Summing over the subtype of candidates different from `x` is the same as
summing over `univ.erase x`. -/
lemma sum_univ_subtype_ne_eq_erase
    {β : Type*} [Fintype β] [DecidableEq β] (x : β) (f : β → ℝ) :
    Finset.univ.sum (fun i : {y : β // y ≠ x} => f i.1) =
      (Finset.univ.erase x).sum f := by
  have hmap :
      (Finset.univ : Finset {y : β // y ≠ x}).map
          (Function.Embedding.subtype (fun y : β => y ≠ x)) =
        Finset.univ.erase x := by
    ext y
    simp
  rw [← hmap]
  exact (Finset.sum_map
    (s := (Finset.univ : Finset {y : β // y ≠ x}))
    (e := Function.Embedding.subtype (fun y : β => y ≠ x)) f).symm

lemma mem_map_subtype_ne
    {β : Type*} [DecidableEq β] {x : β}
    {B : Finset {y : β // y ≠ x}} (i : {y : β // y ≠ x}) :
    (i.1 ∈ B.map (Function.Embedding.subtype (fun y : β => y ≠ x))) ↔
      i ∈ B := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨j, hj, hji⟩
    have : j = i := Subtype.ext hji
    simpa [this] using hj
  · intro hi
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

/-- Summing the pointwise block-improvement change gives the odds-comparison
quantity from the finite-odds lemma. -/
lemma blockImprovementChange_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → ℝ) (x : α) (B : Finset α) (delta : ℝ) :
    Finset.univ.sum (fun a =>
        Finset.univ.sum (fun y =>
          q a * p y * blockImprovementChange x B delta a y)) =
      delta * (q x * B.sum (fun b => p b) -
        p x * B.sum (fun b => q b)) := by
  classical
  have hleft :
      Finset.univ.sum (fun a => Finset.univ.sum (fun y =>
        q a * p y * (if a = x ∧ y ∈ B then delta else 0))) =
        delta * q x * B.sum (fun b => p b) := by
    calc
      Finset.univ.sum (fun a => Finset.univ.sum (fun y =>
        q a * p y * (if a = x ∧ y ∈ B then delta else 0))) =
        Finset.univ.sum (fun y =>
          q x * p y * (if y ∈ B then delta else 0)) := by
          rw [Finset.sum_eq_single x]
          · simp
          · intro a _ha hax
            simp [hax]
          · intro hxnot
            simp at hxnot
      _ = B.sum (fun y => q x * p y * delta) := by
        calc
          Finset.univ.sum (fun y =>
              q x * p y * (if y ∈ B then delta else 0)) =
            Finset.univ.sum (fun y =>
              if y ∈ B then q x * p y * delta else 0) := by
              refine Finset.sum_congr rfl ?_
              intro y _hy
              by_cases hyB : y ∈ B <;> simp [hyB]
          _ = B.sum (fun y => q x * p y * delta) := by
            rw [← Finset.sum_filter]
            congr
            ext y
            simp
      _ = delta * q x * B.sum (fun b => p b) := by
        simp [Finset.mul_sum, mul_comm, mul_left_comm]
  have hright :
      Finset.univ.sum (fun a => Finset.univ.sum (fun y =>
        q a * p y * (if a ∈ B ∧ y = x then delta else 0))) =
        delta * p x * B.sum (fun b => q b) := by
    calc
      Finset.univ.sum (fun a => Finset.univ.sum (fun y =>
        q a * p y * (if a ∈ B ∧ y = x then delta else 0))) =
        Finset.univ.sum (fun a =>
          if a ∈ B then q a * p x * delta else 0) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          by_cases haB : a ∈ B
          · rw [Finset.sum_eq_single x]
            · simp [haB]
            · intro y _hy hyx
              simp [haB, hyx]
            · intro hxnot
              simp at hxnot
          · simp [haB]
      _ = B.sum (fun a => q a * p x * delta) := by
        rw [← Finset.sum_filter]
        congr
        ext a
        simp
      _ = delta * p x * B.sum (fun b => q b) := by
        simp [Finset.mul_sum, mul_comm, mul_left_comm]
  unfold blockImprovementChange
  calc
    Finset.univ.sum (fun a =>
        Finset.univ.sum (fun y =>
          q a * p y * ((if a = x ∧ y ∈ B then delta else 0) -
            (if a ∈ B ∧ y = x then delta else 0)))) =
      Finset.univ.sum (fun a =>
        (Finset.univ.sum (fun y =>
          q a * p y * (if a = x ∧ y ∈ B then delta else 0))) -
        (Finset.univ.sum (fun y =>
          q a * p y * (if a ∈ B ∧ y = x then delta else 0)))) := by
        refine Finset.sum_congr rfl ?_
        intro a _ha
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro y _hy
        ring
    _ = (Finset.univ.sum (fun a => Finset.univ.sum (fun y =>
          q a * p y * (if a = x ∧ y ∈ B then delta else 0)))) -
        (Finset.univ.sum (fun a => Finset.univ.sum (fun y =>
          q a * p y * (if a ∈ B ∧ y = x then delta else 0)))) := by
        rw [Finset.sum_sub_distrib]
    _ = delta * (q x * B.sum (fun b => p b) -
          p x * B.sum (fun b => q b)) := by
        rw [hleft, hright]
        ring

/-- Algebraic finite-odds conclusion from the two endpoint inequalities.  This
lemma checks the summation and cancellation step used after the selected NLHF
endpoint inequalities have been obtained. -/
lemma finiteOdds_from_variational_inequalities
    {α : Type*} [Fintype α] [DecidableEq α]
    {M Mplus : α → α → ℝ} {p q ρ : α → ℝ}
    {lam delta : ℝ} {x : α} {B : Finset α}
    (hMplus_skew : ∀ a y : α, Mplus y a = -Mplus a y)
    (hdelta : 0 < delta)
    (hchange : ∀ a y : α,
      Mplus a y - M a y =
        blockImprovementChange x B delta a y)
    (hvarOld :
      -(1 / lam) * KL p ρ ≥
        marginValue M q p - (1 / lam) * KL q ρ)
    (hvarNew :
      -(1 / lam) * KL q ρ ≥
        marginValue Mplus p q - (1 / lam) * KL p ρ) :
    q x * B.sum (fun b => p b) ≥
      p x * B.sum (fun b => q b) := by
  classical
  have hsum_nonneg :
      0 ≤ marginValue Mplus q p - marginValue M q p := by
    have hle : marginValue M q p + marginValue Mplus p q ≤ 0 := by
      linarith
    have hswap := marginValue_swap_eq_neg_of_skew p q hMplus_skew
    rw [hswap] at hle
    linarith
  have hchangeSum :
      marginValue Mplus q p - marginValue M q p =
        delta * (q x * B.sum (fun b => p b) -
          p x * B.sum (fun b => q b)) := by
    unfold marginValue
    calc
      (Finset.univ.sum fun a =>
          Finset.univ.sum fun y => q a * p y * Mplus a y) -
          (Finset.univ.sum fun a =>
            Finset.univ.sum fun y => q a * p y * M a y) =
        Finset.univ.sum (fun a =>
          Finset.univ.sum (fun y => q a * p y * (Mplus a y - M a y))) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro y _hy
          ring
      _ = Finset.univ.sum (fun a =>
          Finset.univ.sum (fun y =>
            q a * p y * blockImprovementChange x B delta a y)) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          refine Finset.sum_congr rfl ?_
          intro y _hy
          rw [hchange]
      _ = delta * (q x * B.sum (fun b => p b) -
            p x * B.sum (fun b => q b)) :=
          blockImprovementChange_sum p q x B delta
  have hprod_nonneg :
      0 ≤ delta * (q x * B.sum (fun b => p b) -
        p x * B.sum (fun b => q b)) := by
    rwa [← hchangeSum]
  have hbracket :
      0 ≤ q x * B.sum (fun b => p b) -
        p x * B.sum (fun b => q b) := by
    nlinarith
  linarith

/-- The part of the endpoint fixed-point comparison coming only from changing
the lottery, rewritten with the paper's `gamma` coefficient. -/
lemma lottery_change_sum_to_gamma
    {α : Type*} [Fintype α] [DecidableEq α]
    {Mplus : α → α → ℝ} {p q : α → ℝ} {x i : α}
    (hp : Finset.univ.sum (fun y => p y) = 1)
    (hq : Finset.univ.sum (fun y => q y) = 1)
    (hskew : ∀ a b : α, Mplus b a = -Mplus a b) :
    Finset.univ.sum (fun y =>
        (q y - p y) * (Mplus i y - Mplus x y)) =
      (Finset.univ.erase x).sum (fun j =>
        (q j - p j) * nlhfCoordinateC Mplus x i j) := by
  classical
  let s : α → ℝ := fun y => q y - p y
  have hsum_s : Finset.univ.sum (fun y => s y) = 0 := by
    dsimp [s]
    rw [Finset.sum_sub_distrib, hq, hp]
    ring
  have hMxx : Mplus x x = 0 := by
    have h := hskew x x
    linarith
  have hsx : s x = -(Finset.univ.erase x).sum (fun j => s j) := by
    have hadd : s x + (Finset.univ.erase x).sum (fun j => s j) = 0 := by
      rw [Finset.add_sum_erase (s := Finset.univ) (f := fun y => s y)
        (by simp : x ∈ (Finset.univ : Finset α))]
      exact hsum_s
    linarith
  calc
    Finset.univ.sum (fun y =>
        (q y - p y) * (Mplus i y - Mplus x y)) =
      Finset.univ.sum (fun y =>
        s y * (Mplus i y - Mplus x y)) := by
        rfl
    _ = (Finset.univ.erase x).sum (fun j =>
          s j * (Mplus i j - Mplus x j)) +
        s x * (Mplus i x - Mplus x x) := by
        rw [← Finset.add_sum_erase (s := Finset.univ)
          (f := fun y => s y * (Mplus i y - Mplus x y))
          (by simp : x ∈ (Finset.univ : Finset α))]
        ring
    _ = (Finset.univ.erase x).sum (fun j =>
          s j * (Mplus i j - Mplus x j)) +
        (Finset.univ.erase x).sum (fun j => s j * Mplus x i) := by
        rw [hMxx, hskew]
        rw [hsx]
        rw [← Finset.sum_mul]
        ring
    _ = (Finset.univ.erase x).sum (fun j =>
        s j * nlhfCoordinateC Mplus x i j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        unfold nlhfCoordinateC
        ring
    _ = (Finset.univ.erase x).sum (fun j =>
        (q j - p j) * nlhfCoordinateC Mplus x i j) := by
        rfl

/-- The direct margin-change contribution in the endpoint fixed-point
comparison for a block improvement. -/
lemma blockImprovementChange_row_difference_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) {x i : α} {B : Finset α} {delta : ℝ}
    (hix : i ≠ x) (hxB : x ∉ B) :
    Finset.univ.sum (fun y =>
        p y * (blockImprovementChange x B delta i y -
          blockImprovementChange x B delta x y)) =
      -delta * (B.sum (fun b => p b) +
        p x * if i ∈ B then (1 : ℝ) else 0) := by
  classical
  have hblock :
      Finset.univ.sum (fun y =>
          p y * (if y ∈ B then delta else 0)) =
        delta * B.sum (fun b => p b) := by
    calc
      Finset.univ.sum (fun y =>
          p y * (if y ∈ B then delta else 0)) =
        Finset.univ.sum (fun y =>
          if y ∈ B then p y * delta else 0) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          by_cases hyB : y ∈ B <;> simp [hyB]
      _ = B.sum (fun y => p y * delta) := by
        rw [← Finset.sum_filter]
        congr
        ext y
        simp
      _ = delta * B.sum (fun b => p b) := by
        simp [Finset.mul_sum, mul_comm]
  have hxterm :
      Finset.univ.sum (fun y =>
          p y * (if i ∈ B ∧ y = x then delta else 0)) =
        p x * (if i ∈ B then delta else 0) := by
    by_cases hiB : i ∈ B
    · rw [Finset.sum_eq_single x]
      · simp [hiB]
      · intro y _hy hyx
        simp [hiB, hyx]
      · intro hxnot
        simp at hxnot
    · simp [hiB]
  unfold blockImprovementChange
  calc
    Finset.univ.sum (fun y =>
        p y * (((if i = x ∧ y ∈ B then delta else 0) -
          (if i ∈ B ∧ y = x then delta else 0)) -
          ((if x = x ∧ y ∈ B then delta else 0) -
            (if x ∈ B ∧ y = x then delta else 0)))) =
      Finset.univ.sum (fun y =>
        p y * (-(if i ∈ B ∧ y = x then delta else 0) -
          (if y ∈ B then delta else 0))) := by
        refine Finset.sum_congr rfl ?_
        intro y _hy
        simp [hix, hxB]
    _ = -Finset.univ.sum (fun y =>
          p y * (if i ∈ B ∧ y = x then delta else 0)) -
        Finset.univ.sum (fun y =>
          p y * (if y ∈ B then delta else 0)) := by
        rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro y _hy
        ring
    _ = -delta * (B.sum (fun b => p b) +
        p x * if i ∈ B then (1 : ℝ) else 0) := by
        rw [hblock, hxterm]
        by_cases hiB : i ∈ B
        · simp [hiB]
          ring
        · simp [hiB]

/-- The full right-hand side decomposition of the endpoint fixed-point
comparison used to obtain the secant system in the finite proof. -/
lemma endpoint_margin_difference_decomposition
    {α : Type*} [Fintype α] [DecidableEq α]
    {M Mplus : α → α → ℝ} {p q : α → ℝ}
    {x i : α} {B : Finset α} {delta : ℝ}
    (hp : Finset.univ.sum (fun y => p y) = 1)
    (hq : Finset.univ.sum (fun y => q y) = 1)
    (hMplus_skew : ∀ a b : α, Mplus b a = -Mplus a b)
    (hchange : ∀ a y : α,
      Mplus a y - M a y =
        blockImprovementChange x B delta a y)
    (hix : i ≠ x) (hxB : x ∉ B) :
    (expectedMargin Mplus q i - expectedMargin Mplus q x) -
      (expectedMargin M p i - expectedMargin M p x) =
      (Finset.univ.erase x).sum (fun j =>
        (q j - p j) * nlhfCoordinateC Mplus x i j) -
      delta * (B.sum (fun b => p b) +
        p x * if i ∈ B then (1 : ℝ) else 0) := by
  classical
  have hlottery :=
    lottery_change_sum_to_gamma
      (Mplus := Mplus) (p := p) (q := q) (x := x) (i := i)
      hp hq hMplus_skew
  have hmargin :
      Finset.univ.sum (fun y =>
        p y * ((Mplus i y - Mplus x y) - (M i y - M x y))) =
        -delta * (B.sum (fun b => p b) +
          p x * if i ∈ B then (1 : ℝ) else 0) := by
    calc
      Finset.univ.sum (fun y =>
          p y * ((Mplus i y - Mplus x y) - (M i y - M x y))) =
        Finset.univ.sum (fun y =>
          p y * (blockImprovementChange x B delta i y -
            blockImprovementChange x B delta x y)) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          rw [← hchange i y, ← hchange x y]
          ring
      _ = -delta * (B.sum (fun b => p b) +
          p x * if i ∈ B then (1 : ℝ) else 0) :=
          blockImprovementChange_row_difference_sum p hix hxB
  unfold expectedMargin
  have hqpart :
      Finset.univ.sum (fun y => q y * Mplus i y) -
        Finset.univ.sum (fun y => q y * Mplus x y) =
      Finset.univ.sum (fun y => q y * (Mplus i y - Mplus x y)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro y _hy
    ring
  have hppart :
      Finset.univ.sum (fun y => p y * M i y) -
        Finset.univ.sum (fun y => p y * M x y) =
      Finset.univ.sum (fun y => p y * (M i y - M x y)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro y _hy
    ring
  calc
    (Finset.univ.sum (fun y => q y * Mplus i y) -
        Finset.univ.sum (fun y => q y * Mplus x y)) -
      (Finset.univ.sum (fun y => p y * M i y) -
        Finset.univ.sum (fun y => p y * M x y)) =
      Finset.univ.sum (fun y =>
        (q y - p y) * (Mplus i y - Mplus x y)) +
      Finset.univ.sum (fun y =>
        p y * ((Mplus i y - Mplus x y) - (M i y - M x y))) := by
        rw [hqpart, hppart]
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro y _hy
        ring
    _ = (Finset.univ.erase x).sum (fun j =>
          (q j - p j) * nlhfCoordinateC Mplus x i j) -
        delta * (B.sum (fun b => p b) +
          p x * if i ∈ B then (1 : ℝ) else 0) := by
        rw [hlottery, hmargin]
        ring

/-- From the two NLHF fixed-point equations and the endpoint logarithmic-mean
identities, obtain the secant-system equation used in the finite comparison. -/
lemma secant_system_from_fixed_points
    {α : Type*} [Fintype α] [DecidableEq α]
    {τ lam : ℝ} {M Mplus : α → α → ℝ} {ρ p q : α → ℝ}
    {x i : α} {B : Finset α} {delta alphaI alphaX : ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ p)
    (hfp' : IsNLHFFixedPoint τ Mplus ρ q)
    (hlam : lam = nlhfLambda τ)
    (hMplus_skew : ∀ a b : α, Mplus b a = -Mplus a b)
    (hchange : ∀ a y : α,
      Mplus a y - M a y =
        blockImprovementChange x B delta a y)
    (hix : i ≠ x) (hxB : x ∉ B)
    (hlogI : Real.log (q i / p i) = (q i - p i) / alphaI)
    (hlogX : Real.log (p x / q x) = (p x - q x) / alphaX) :
    (q i - p i) / alphaI + (p x - q x) / alphaX =
      lam * (Finset.univ.erase x).sum (fun j =>
        (q j - p j) * nlhfCoordinateC Mplus x i j) -
      lam * delta * (B.sum (fun b => p b) +
        p x * if i ∈ B then (1 : ℝ) else 0) := by
  classical
  have hendpoint :=
    nlhfFixedPoint_endpoint_log_difference hfp hfp' i x
  rw [hlogI, hlogX] at hendpoint
  have hdecomp :
      (expectedMargin Mplus q i - expectedMargin Mplus q x) -
        (expectedMargin M p i - expectedMargin M p x) =
        (Finset.univ.erase x).sum (fun j =>
          (q j - p j) * nlhfCoordinateC Mplus x i j) -
        delta * (B.sum (fun b => p b) +
          p x * if i ∈ B then (1 : ℝ) else 0) :=
    endpoint_margin_difference_decomposition
      (M := M) (Mplus := Mplus) (p := p) (q := q)
      (x := x) (i := i) (B := B) (delta := delta)
      hfp.2.2.1.2 hfp'.2.2.1.2 hMplus_skew hchange hix hxB
  rw [hdecomp] at hendpoint
  rw [hlam, nlhfLambda]
  rw [hendpoint]
  ring

/-- The secant-system equation with the logarithmic means filled in directly
from the endpoint lotteries. -/
lemma secant_system_from_fixed_points_logMean
    {α : Type*} [Fintype α] [DecidableEq α]
    {τ lam : ℝ} {M Mplus : α → α → ℝ} {ρ p q : α → ℝ}
    {x i : α} {B : Finset α} {delta : ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ p)
    (hfp' : IsNLHFFixedPoint τ Mplus ρ q)
    (hlam : lam = nlhfLambda τ)
    (hMplus_skew : ∀ a b : α, Mplus b a = -Mplus a b)
    (hchange : ∀ a y : α,
      Mplus a y - M a y =
        blockImprovementChange x B delta a y)
    (hix : i ≠ x) (hxB : x ∉ B) :
    (q i - p i) / logMean (p i) (q i) +
        (p x - q x) / logMean (p x) (q x) =
      lam * (Finset.univ.erase x).sum (fun j =>
        (q j - p j) * nlhfCoordinateC Mplus x i j) -
      lam * delta * (B.sum (fun b => p b) +
        p x * if i ∈ B then (1 : ℝ) else 0) := by
  exact
    secant_system_from_fixed_points
      (M := M) (Mplus := Mplus) (ρ := ρ) (p := p) (q := q)
      (τ := τ) (lam := lam) (x := x) (i := i) (B := B)
      (delta := delta)
      hfp hfp' hlam hMplus_skew hchange hix hxB
      (logMean_log_identity (hfp.2.2.1.1 i) (hfp'.2.2.1.1 i))
      (logMean_log_reverse_identity (hfp.2.2.1.1 x) (hfp'.2.2.1.1 x))

/-- Three-candidate finite-secant response derived from the old and new NLHF
fixed-point equations.  Candidates `0`, `1`, and `2` are the paper's
`x`, `y`, and `z`, respectively. -/
lemma threeCandidateSecant_formula_from_fixed_points_fin3
    {τ lam δ D den : ℝ}
    {M Mplus : Fin 3 → Fin 3 → ℝ}
    {ρ μ π : Fin 3 → ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ μ)
    (hfp' : IsNLHFFixedPoint τ Mplus ρ π)
    (hlam : lam = nlhfLambda τ)
    (hMplus : IsNormalizedMarginMatrix Mplus)
    (hchange : ∀ a y : Fin 3,
      Mplus a y - M a y =
        blockImprovementChange 0 ({1} : Finset (Fin 3)) δ a y)
    (hD : D = nlhfCoordinateC Mplus 0 1 2)
    (hden :
      den = lam ^ 2 * D ^ 2 +
        1 / (logMean (μ 1) (π 1) * logMean (μ 2) (π 2)) +
        1 / (logMean (μ 1) (π 1) * logMean (μ 0) (π 0)) +
        1 / (logMean (μ 2) (π 2) * logMean (μ 0) (π 0))) :
    π 0 - μ 0 =
      lam * δ *
        (μ 0 / logMean (μ 2) (π 2) +
          μ 1 / logMean (μ 1) (π 1) +
          μ 1 / logMean (μ 2) (π 2) -
          lam * D * μ 0) / den := by
  classical
  let Lx : ℝ := logMean (μ 0) (π 0)
  let Ly : ℝ := logMean (μ 1) (π 1)
  let Lz : ℝ := logMean (μ 2) (π 2)
  let Δx : ℝ := π 0 - μ 0
  let Δy : ℝ := π 1 - μ 1
  let Δz : ℝ := π 2 - μ 2
  have hLx_ne : Lx ≠ 0 := by
    dsimp [Lx]
    exact logMean_ne_zero (hfp.2.2.1.1 0) (hfp'.2.2.1.1 0)
  have hLy_ne : Ly ≠ 0 := by
    dsimp [Ly]
    exact logMean_ne_zero (hfp.2.2.1.1 1) (hfp'.2.2.1.1 1)
  have hLz_ne : Lz ≠ 0 := by
    dsimp [Lz]
    exact logMean_ne_zero (hfp.2.2.1.1 2) (hfp'.2.2.1.1 2)
  have hden' :
      den = lam ^ 2 * D ^ 2 +
        1 / (Ly * Lz) + 1 / (Ly * Lx) + 1 / (Lz * Lx) := by
    simpa [Lx, Ly, Lz] using hden
  have hden_pos : 0 < den := by
    rw [hden']
    exact threeCandidateSecant_den_pos
      (logMean_pos (hfp.2.2.1.1 0) (hfp'.2.2.1.1 0))
      (logMean_pos (hfp.2.2.1.1 1) (hfp'.2.2.1.1 1))
      (logMean_pos (hfp.2.2.1.1 2) (hfp'.2.2.1.1 2))
  have hsum : Δx + Δy + Δz = 0 := by
    dsimp [Δx, Δy, Δz]
    have hπsum := hfp'.2.2.1.2
    have hμsum := hfp.2.2.1.2
    simp [Fin.sum_univ_three] at hπsum hμsum ⊢
    linarith
  have hc11 : nlhfCoordinateC Mplus 0 1 1 = 0 := by
    unfold nlhfCoordinateC
    rw [hMplus.1 1]
    ring
  have hc22 : nlhfCoordinateC Mplus 0 2 2 = 0 := by
    unfold nlhfCoordinateC
    rw [hMplus.1 2]
    ring
  have hc12 : nlhfCoordinateC Mplus 0 1 2 = D := hD.symm
  have hc21 : nlhfCoordinateC Mplus 0 2 1 = -D := by
    rw [nlhfCoordinateC_skew hMplus 0 1 2, hc12]
  have hsum_y :
      (Finset.univ.erase 0).sum
          (fun j : Fin 3 =>
            (π j - μ j) * nlhfCoordinateC Mplus 0 1 j) =
        D * Δz := by
    dsimp [Δz]
    simp [Fin.sum_univ_three, hc11, hc12]
    ring
  have hsum_z :
      (Finset.univ.erase 0).sum
          (fun j : Fin 3 =>
            (π j - μ j) * nlhfCoordinateC Mplus 0 2 j) =
        -D * Δy := by
    dsimp [Δy]
    simp [Fin.sum_univ_three, hc21, hc22]
    ring
  have hy_raw :=
    secant_system_from_fixed_points_logMean
      (τ := τ) (lam := lam) (M := M) (Mplus := Mplus)
      (ρ := ρ) (p := μ) (q := π)
      (x := 0) (i := 1) (B := ({1} : Finset (Fin 3)))
      (delta := δ)
      hfp hfp' hlam hMplus.2.1 hchange
      (by decide : (1 : Fin 3) ≠ 0)
      (by simp : (0 : Fin 3) ∉ ({1} : Finset (Fin 3)))
  have hz_raw :=
    secant_system_from_fixed_points_logMean
      (τ := τ) (lam := lam) (M := M) (Mplus := Mplus)
      (ρ := ρ) (p := μ) (q := π)
      (x := 0) (i := 2) (B := ({1} : Finset (Fin 3)))
      (delta := δ)
      hfp hfp' hlam hMplus.2.1 hchange
      (by decide : (2 : Fin 3) ≠ 0)
      (by simp : (0 : Fin 3) ∉ ({1} : Finset (Fin 3)))
  have hy :
      Δy / Ly - Δx / Lx =
        lam * D * Δz - lam * δ * (μ 0 + μ 1) := by
    dsimp [Lx, Ly, Δx, Δy] at hy_raw ⊢
    rw [hsum_y] at hy_raw
    simp at hy_raw
    ring_nf at hy_raw ⊢
    linarith
  have hz :
      Δz / Lz - Δx / Lx =
        -lam * D * Δy - lam * δ * μ 1 := by
    dsimp [Lx, Lz, Δx, Δz] at hz_raw ⊢
    rw [hsum_z] at hz_raw
    simp at hz_raw
    ring_nf at hz_raw ⊢
    linarith
  have hformula :
      Δx =
        lam * δ *
          (μ 0 / Lz + μ 1 / Ly + μ 1 / Lz - lam * D * μ 0) / den :=
    threeCandidateSecant_formula_from_log_equations
      (lam := lam) (s := δ) (mux := μ 0) (muy := μ 1)
      (D := D) (Lx := Lx) (Ly := Ly) (Lz := Lz)
      (Δx := Δx) (Δy := Δy) (Δz := Δz) (den := den)
      hLx_ne hLy_ne hLz_ne hden' hden_pos.ne' hsum hy hz
  simpa [Lx, Ly, Lz, Δx] using hformula

/-- If the total logarithmic-mean weight is at most `1`, then deleting one
opponent leaves total weight at most `1 - alphaX`. -/
lemma erase_weight_sum_le_one_sub_of_total_le
    {α : Type*} [Fintype α] [DecidableEq α]
    {alpha : α → ℝ} {alphaX : ℝ} {i : α}
    (halpha_nonneg : ∀ j : α, 0 ≤ alpha j)
    (hsum : alphaX + Finset.univ.sum (fun j => alpha j) ≤ 1) :
    (Finset.univ.erase i).sum (fun j => alpha j) ≤ 1 - alphaX := by
  classical
  have hsubset :
      (Finset.univ.erase i : Finset α) ⊆ Finset.univ := by
    intro j hj
    simp
  have hle_univ :
      (Finset.univ.erase i).sum (fun j => alpha j) ≤
        Finset.univ.sum (fun j => alpha j) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro j _hj _hnot; exact halpha_nonneg j)
  linarith

/-- The Cauchy/logarithmic-mean estimate used in the finite comparison proof.
It is the endpoint `1/4` estimate used in the proof. -/
lemma finiteComparison_abs_erase_le_quarter
    {α : Type*} [Fintype α] [DecidableEq α]
    {alpha z : α → ℝ} {alphaX T : ℝ} {i : α}
    (halpha : ∀ j : α, 0 < alpha j)
    (halphaX : 0 < alphaX)
    (hsum : alphaX + Finset.univ.sum (fun j => alpha j) ≤ 1)
    (henergy :
      Finset.univ.sum (fun j => |z j| ^ 2 / alpha j) +
          T ^ 2 / alphaX = T) :
    (Finset.univ.erase i).sum (fun j => |z j|) ≤ (1 : ℝ) / 4 := by
  classical
  by_cases hex : ∃ j : α, j ≠ i
  · have hPpos :
        0 < (Finset.univ.erase i).sum (fun j => alpha j) :=
      erase_probability_sum_pos_of_exists halpha hex
    have hP_le :
        (Finset.univ.erase i).sum (fun j => alpha j) ≤ 1 - alphaX :=
      erase_weight_sum_le_one_sub_of_total_le
        (fun j => (halpha j).le) hsum
    have hZ_le :
        (Finset.univ.erase i).sum (fun j => |z j| ^ 2 / alpha j) ≤
          T - T ^ 2 / alphaX :=
      erase_energy_sum_le_remainder halpha henergy
    have hsq :
        ((Finset.univ.erase i).sum (fun j => |z j|)) ^ 2 ≤
          (1 - alphaX) * (T - T ^ 2 / alphaX) :=
      sqAbsSum_le_energyProduct_of_cauchy halpha hPpos hP_le hZ_le
    have hS0 :
        0 ≤ (Finset.univ.erase i).sum (fun j => |z j|) :=
      Finset.sum_nonneg (fun j _hj => abs_nonneg (z j))
    have halphaX_le_one : alphaX ≤ 1 := by
      have hsum_nonneg :
          0 ≤ Finset.univ.sum (fun j => alpha j) :=
        Finset.sum_nonneg (fun j _hj => (halpha j).le)
      linarith
    exact absSumBound_of_sq_le_energyBound
      hS0 halphaX halphaX_le_one hsq
  · have hempty : Finset.univ.erase i = (∅ : Finset α) := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hji : j ≠ i := by simpa using hj
      exact hex ⟨j, hji⟩
    simp [hempty]

/-- Energy identity for the auxiliary finite system in the endpoint proof. -/
lemma finiteComparison_energy_identity
    {α : Type*} [Fintype α]
    {alpha z : α → ℝ} {gamma : α → α → ℝ}
    {alphaX T lam : ℝ}
    (hT : Finset.univ.sum (fun i => z i) = T)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hz :
      ∀ i : α,
        z i / alpha i + T / alphaX +
          lam * Finset.univ.sum (fun j => gamma i j * z j) = 1) :
    Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) +
        T ^ 2 / alphaX = T := by
  classical
  have hweighted :
      Finset.univ.sum
        (fun i =>
          z i *
            (z i / alpha i + T / alphaX +
              lam * Finset.univ.sum (fun j => gamma i j * z j))) = T := by
    calc
      Finset.univ.sum
          (fun i =>
            z i *
              (z i / alpha i + T / alphaX +
                lam * Finset.univ.sum (fun j => gamma i j * z j)))
          =
        Finset.univ.sum (fun i => z i * 1) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hz i]
      _ = T := by
          simp [hT]
  exact auxiliary_energy_identity_from_weighted_sum hT hskew hweighted

/-- Energy identity for the homogeneous auxiliary system.  This formalizes the
calculation used in the paper to show that the homogeneous system has only the
zero solution. -/
lemma finiteComparison_homogeneous_energy_zero
    {α : Type*} [Fintype α]
    {alpha z : α → ℝ} {gamma : α → α → ℝ}
    {alphaX T lam : ℝ}
    (hT : Finset.univ.sum (fun i => z i) = T)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hz0 :
      ∀ i : α,
        z i / alpha i + T / alphaX +
          lam * Finset.univ.sum (fun j => gamma i j * z j) = 0) :
    Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) +
        T ^ 2 / alphaX = 0 := by
  classical
  have hweighted :
      Finset.univ.sum
        (fun i =>
          z i *
            (z i / alpha i + T / alphaX +
              lam * Finset.univ.sum (fun j => gamma i j * z j))) = 0 := by
    calc
      Finset.univ.sum
          (fun i =>
            z i *
              (z i / alpha i + T / alphaX +
                lam * Finset.univ.sum (fun j => gamma i j * z j)))
          =
        Finset.univ.sum (fun i => z i * 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hz0 i]
      _ = 0 := by simp
  have hdouble :
      Finset.univ.sum
          (fun i => z i * Finset.univ.sum (fun j => gamma i j * z j)) = 0 :=
    skew_weighted_double_sum_eq_zero hskew
  have hsq_abs :
      Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) =
        Finset.univ.sum (fun i => z i ^ 2 / alpha i) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [sq_abs]
  have hexpand :
      Finset.univ.sum
        (fun i =>
          z i *
            (z i / alpha i + T / alphaX +
              lam * Finset.univ.sum (fun j => gamma i j * z j))) =
        Finset.univ.sum (fun i => z i ^ 2 / alpha i) +
          T ^ 2 / alphaX +
            lam *
              Finset.univ.sum
                (fun i => z i * Finset.univ.sum (fun j => gamma i j * z j)) := by
    calc
      Finset.univ.sum
        (fun i =>
          z i *
            (z i / alpha i + T / alphaX +
              lam * Finset.univ.sum (fun j => gamma i j * z j)))
          =
        Finset.univ.sum
          (fun i =>
            z i ^ 2 / alpha i + (T / alphaX) * z i +
              lam * (z i * Finset.univ.sum (fun j => gamma i j * z j))) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ =
        Finset.univ.sum (fun i => z i ^ 2 / alpha i) +
          Finset.univ.sum (fun i => (T / alphaX) * z i) +
            Finset.univ.sum
              (fun i => lam * (z i * Finset.univ.sum (fun j => gamma i j * z j))) := by
            simp [Finset.sum_add_distrib]
      _ =
        Finset.univ.sum (fun i => z i ^ 2 / alpha i) +
          (T / alphaX) * Finset.univ.sum (fun i => z i) +
            lam *
              Finset.univ.sum
                (fun i => z i * Finset.univ.sum (fun j => gamma i j * z j)) := by
            simp [Finset.mul_sum]
      _ =
        Finset.univ.sum (fun i => z i ^ 2 / alpha i) +
          T ^ 2 / alphaX +
            lam *
              Finset.univ.sum
                (fun i => z i * Finset.univ.sum (fun j => gamma i j * z j)) := by
            rw [hT]
            ring
  rw [hexpand] at hweighted
  rw [hdouble] at hweighted
  rw [hsq_abs]
  linarith

lemma finiteComparison_homogeneous_solution_eq_zero
    {α : Type*} [Fintype α]
    {alpha z : α → ℝ} {gamma : α → α → ℝ}
    {alphaX T lam : ℝ}
    (halpha : ∀ i : α, 0 < alpha i)
    (halphaX : 0 < alphaX)
    (hT : Finset.univ.sum (fun i => z i) = T)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hz0 :
      ∀ i : α,
        z i / alpha i + T / alphaX +
          lam * Finset.univ.sum (fun j => gamma i j * z j) = 0) :
    ∀ i : α, z i = 0 := by
  classical
  have henergy0 :
      Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) +
          T ^ 2 / alphaX = 0 :=
    finiteComparison_homogeneous_energy_zero hT hskew hz0
  have hsum_nonneg :
      0 ≤ Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) := by
    exact Finset.sum_nonneg
      (fun i _hi => div_nonneg (sq_nonneg _) (halpha i).le)
  have hquad_nonneg : 0 ≤ T ^ 2 / alphaX :=
    div_nonneg (sq_nonneg T) halphaX.le
  have hsum_zero :
      Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) = 0 := by
    nlinarith
  intro i
  have hterm_nonneg :
      ∀ j ∈ (Finset.univ : Finset α),
        0 ≤ |z j| ^ 2 / alpha j := by
    intro j _hj
    exact div_nonneg (sq_nonneg _) (halpha j).le
  have hterm_le :
      |z i| ^ 2 / alpha i ≤
        Finset.univ.sum (fun j => |z j| ^ 2 / alpha j) :=
    Finset.single_le_sum hterm_nonneg (by simp)
  have hterm_zero : |z i| ^ 2 / alpha i = 0 := by
    have hterm0 : 0 ≤ |z i| ^ 2 / alpha i :=
      div_nonneg (sq_nonneg _) (halpha i).le
    linarith
  have hsq_zero : |z i| ^ 2 = 0 := by
    rcases (div_eq_zero_iff.mp hterm_zero) with hnum | hden
    · exact hnum
    · exact False.elim ((halpha i).ne' hden)
  exact abs_eq_zero.mp (sq_eq_zero_iff.mp hsq_zero)

/-- The auxiliary linear operator in the finite comparison proof. -/
noncomputable def finiteComparisonAuxLinearMap
    {α : Type*} [Fintype α]
    (alpha : α → ℝ) (gamma : α → α → ℝ)
    (alphaX lam : ℝ) :
    (α → ℝ) →ₗ[ℝ] (α → ℝ) where
  toFun z := fun i =>
    z i / alpha i + Finset.univ.sum (fun j => z j) / alphaX +
      lam * Finset.univ.sum (fun j => gamma i j * z j)
  map_add' z w := by
    ext i
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    have hgamma :
        Finset.univ.sum (fun j => gamma i j * (z j + w j)) =
          Finset.univ.sum (fun j => gamma i j * z j) +
            Finset.univ.sum (fun j => gamma i j * w j) := by
      calc
        Finset.univ.sum (fun j => gamma i j * (z j + w j)) =
          Finset.univ.sum
            (fun j => gamma i j * z j + gamma i j * w j) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
        _ = _ := by rw [Finset.sum_add_distrib]
    rw [hgamma]
    ring
  map_smul' c z := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hsum :
        Finset.univ.sum (fun j => c * z j) =
          c * Finset.univ.sum (fun j => z j) := by
      rw [Finset.mul_sum]
    have hgamma :
        Finset.univ.sum (fun j => gamma i j * (c * z j)) =
          c * Finset.univ.sum (fun j => gamma i j * z j) := by
      calc
        Finset.univ.sum (fun j => gamma i j * (c * z j)) =
          Finset.univ.sum (fun j => c * (gamma i j * z j)) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
        _ = c * Finset.univ.sum (fun j => gamma i j * z j) := by
          rw [Finset.mul_sum]
    rw [hsum, hgamma]
    ring

/-- The auxiliary finite system has a solution.  This is the formal
finite-dimensional linear algebra step following the homogeneous-kernel
argument in the TeX proof. -/
lemma finiteComparison_auxiliary_solution_exists
    {α : Type*} [Fintype α]
    {alpha : α → ℝ} {gamma : α → α → ℝ} {alphaX lam : ℝ}
    (halpha : ∀ i : α, 0 < alpha i)
    (halphaX : 0 < alphaX)
    (hskew : ∀ i j : α, gamma i j = -gamma j i) :
    ∃ z : α → ℝ,
      ∀ i : α,
        z i / alpha i + Finset.univ.sum (fun j => z j) / alphaX +
          lam * Finset.univ.sum (fun j => gamma i j * z j) = 1 := by
  classical
  let L := finiteComparisonAuxLinearMap alpha gamma alphaX lam
  have hinj : Function.Injective L := by
    intro z w hzw
    have hdiff : L (z - w) = 0 := by
      rw [map_sub, hzw]
      simp
    have hzero : ∀ i : α, (z - w) i = 0 := by
      refine finiteComparison_homogeneous_solution_eq_zero
        (alpha := alpha) (gamma := gamma) (alphaX := alphaX)
        (lam := lam) halpha halphaX
        (T := Finset.univ.sum (fun i => (z - w) i)) rfl hskew ?_
      intro i
      exact congrFun hdiff i
    ext i
    exact sub_eq_zero.mp (hzero i)
  have hsurj : Function.Surjective L :=
    LinearMap.surjective_of_injective hinj
  rcases hsurj (fun _ : α => (1 : ℝ)) with ⟨z, hz⟩
  exact ⟨z, fun i => congrFun hz i⟩

/-- The block version of the duality identity in the finite comparison proof.
This is equation `(U-formula)` in the TeX note. -/
lemma finiteComparison_block_duality
    {α : Type*} [Fintype α] [DecidableEq α]
    {alpha z s : α → ℝ} {gamma : α → α → ℝ}
    {alphaX pX PB T U lam delta : ℝ} {B : Finset α}
    (hT : Finset.univ.sum (fun i => z i) = T)
    (hU : Finset.univ.sum (fun i => s i) = U)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hz :
      ∀ i : α,
        z i / alpha i + T / alphaX +
          lam * Finset.univ.sum (fun j => gamma i j * z j) = 1)
    (hs :
      ∀ i : α,
        s i / alpha i + U / alphaX =
          lam * Finset.univ.sum (fun j => gamma i j * s j) -
            lam * delta * (PB + pX * if i ∈ B then (1 : ℝ) else 0)) :
    U = -lam * delta *
      (PB * T + pX * B.sum (fun i => z i)) := by
  classical
  let A : ℝ :=
    Finset.univ.sum (fun i => z i * (s i / alpha i + U / alphaX))
  let C : ℝ :=
    Finset.univ.sum
      (fun i => s i * (z i / alpha i + T / alphaX))
  have hAC : A = C := by
    unfold A C
    calc
      Finset.univ.sum (fun i => z i * (s i / alpha i + U / alphaX))
          =
        Finset.univ.sum (fun i => z i * (s i / alpha i) + (U / alphaX) * z i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
      _ =
        Finset.univ.sum (fun i => z i * (s i / alpha i)) +
          (U / alphaX) * Finset.univ.sum (fun i => z i) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ =
        Finset.univ.sum (fun i => s i * (z i / alpha i)) +
          (T / alphaX) * Finset.univ.sum (fun i => s i) := by
          have hsum :
              Finset.univ.sum (fun i => z i * (s i / alpha i)) =
                Finset.univ.sum (fun i => s i * (z i / alpha i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
          rw [hT, hU, hsum]
          ring
      _ =
        Finset.univ.sum (fun i => s i * (z i / alpha i) + (T / alphaX) * s i) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ =
        Finset.univ.sum (fun i => s i * (z i / alpha i + T / alphaX)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
  have hA :
      A =
        lam * Finset.univ.sum
          (fun i => z i * Finset.univ.sum (fun j => gamma i j * s j)) -
          lam * delta *
            (PB * T + pX * B.sum (fun i => z i)) := by
    unfold A
    calc
      Finset.univ.sum (fun i => z i * (s i / alpha i + U / alphaX))
          =
        Finset.univ.sum
          (fun i =>
            z i *
              (lam * Finset.univ.sum (fun j => gamma i j * s j) -
                lam * delta * (PB + pX * (if i ∈ B then (1 : ℝ) else 0)))) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hs i]
      _ =
        lam * Finset.univ.sum
          (fun i => z i * Finset.univ.sum (fun j => gamma i j * s j)) -
          lam * delta *
            Finset.univ.sum
              (fun i => z i * (PB + pX * (if i ∈ B then (1 : ℝ) else 0))) := by
          calc
            Finset.univ.sum
                (fun i =>
                  z i *
                    (lam * Finset.univ.sum (fun j => gamma i j * s j) -
                      lam * delta * (PB + pX * (if i ∈ B then (1 : ℝ) else 0))))
                =
              Finset.univ.sum
                (fun i =>
                  lam * (z i * Finset.univ.sum (fun j => gamma i j * s j)) -
                    lam * delta *
                      (z i * (PB + pX * (if i ∈ B then (1 : ℝ) else 0)))) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                ring
            _ =
              Finset.univ.sum
                (fun i => lam * (z i * Finset.univ.sum (fun j => gamma i j * s j))) -
                Finset.univ.sum
                  (fun i =>
                    lam * delta *
                      (z i * (PB + pX * (if i ∈ B then (1 : ℝ) else 0)))) := by
                rw [Finset.sum_sub_distrib]
            _ =
              lam * Finset.univ.sum
                (fun i => z i * Finset.univ.sum (fun j => gamma i j * s j)) -
              lam * delta *
                Finset.univ.sum
                  (fun i => z i * (PB + pX * (if i ∈ B then (1 : ℝ) else 0))) := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ =
        lam * Finset.univ.sum
          (fun i => z i * Finset.univ.sum (fun j => gamma i j * s j)) -
          lam * delta *
            (PB * T + pX * B.sum (fun i => z i)) := by
          have hindicator :
              Finset.univ.sum
                (fun i => z i * (PB + pX * (if i ∈ B then (1 : ℝ) else 0))) =
              PB * T + pX * B.sum (fun i => z i) := by
            calc
              Finset.univ.sum
                  (fun i => z i * (PB + pX * (if i ∈ B then (1 : ℝ) else 0)))
                  =
                Finset.univ.sum
                  (fun i => PB * z i + pX * (if i ∈ B then z i else 0)) := by
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  by_cases hi : i ∈ B <;> simp [hi] <;> ring
              _ =
                PB * Finset.univ.sum (fun i => z i) +
                  pX * Finset.univ.sum (fun i => if i ∈ B then z i else 0) := by
                simp [Finset.sum_add_distrib, Finset.mul_sum]
              _ = PB * T + pX * B.sum (fun i => z i) := by
                rw [hT]
                have hfilter :
                    Finset.univ.sum (fun i => if i ∈ B then z i else 0) =
                      B.sum (fun i => z i) := by
                  rw [← Finset.sum_filter]
                  congr
                  ext i
                  simp
                rw [hfilter]
          rw [hindicator]
  have hC :
      C =
        Finset.univ.sum (fun i => s i) -
          lam * Finset.univ.sum
            (fun i => s i * Finset.univ.sum (fun j => gamma i j * z j)) := by
    unfold C
    calc
      Finset.univ.sum (fun i => s i * (z i / alpha i + T / alphaX))
          =
        Finset.univ.sum
          (fun i =>
            s i * (1 - lam * Finset.univ.sum (fun j => gamma i j * z j))) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hzi :
              z i / alpha i + T / alphaX =
                1 - lam * Finset.univ.sum (fun j => gamma i j * z j) := by
            linarith [hz i]
          rw [hzi]
      _ =
        Finset.univ.sum (fun i => s i) -
          lam * Finset.univ.sum
            (fun i => s i * Finset.univ.sum (fun j => gamma i j * z j)) := by
          calc
            Finset.univ.sum
                (fun i =>
                  s i * (1 - lam * Finset.univ.sum (fun j => gamma i j * z j)))
                =
              Finset.univ.sum
                (fun i =>
                  s i - lam * (s i * Finset.univ.sum (fun j => gamma i j * z j))) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                ring
            _ =
              Finset.univ.sum (fun i => s i) -
                Finset.univ.sum
                  (fun i => lam * (s i * Finset.univ.sum (fun j => gamma i j * z j))) := by
                rw [Finset.sum_sub_distrib]
            _ =
              Finset.univ.sum (fun i => s i) -
                lam * Finset.univ.sum
                  (fun i => s i * Finset.univ.sum (fun j => gamma i j * z j)) := by
                rw [← Finset.mul_sum]
  have hswap :
      Finset.univ.sum
          (fun i => z i * Finset.univ.sum (fun j => gamma i j * s j)) =
        -Finset.univ.sum
          (fun i => s i * Finset.univ.sum (fun j => gamma i j * z j)) :=
    skew_weighted_double_sum_swap hskew
  rw [hA, hC, hU, hswap] at hAC
  ring_nf at hAC ⊢
  linarith

lemma finiteComparison_T_nonneg
    {α : Type*} [Fintype α]
    {alpha z : α → ℝ} {alphaX T : ℝ}
    (halpha : ∀ i : α, 0 < alpha i)
    (halphaX : 0 < alphaX)
    (henergy :
      Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) +
          T ^ 2 / alphaX = T) :
    0 ≤ T := by
  have hsum_nonneg :
      0 ≤ Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) := by
    exact Finset.sum_nonneg
      (fun i _hi => div_nonneg (sq_nonneg _) (halpha i).le)
  have hquad_nonneg : 0 ≤ T ^ 2 / alphaX :=
    div_nonneg (sq_nonneg T) halphaX.le
  nlinarith

/-- Direct finite comparison, stated over the opponent set `A = X \ {x}`.
The hypotheses are exactly the endpoint secant system, auxiliary system,
logarithmic-mean block ratio, and finite-odds consequences from the TeX proof. -/
theorem finiteComparison_from_secant_auxiliary
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q alpha z : α → ℝ} {gamma : α → α → ℝ}
    {pX qX alphaX lam delta K U T PB AB : ℝ} {B : Finset α}
    (hpX : 0 < pX)
    (halpha : ∀ i : α, 0 < alpha i)
    (halphaX : 0 < alphaX)
    (halpha_sum : alphaX + Finset.univ.sum (fun i => alpha i) ≤ 1)
    (hT : Finset.univ.sum (fun i => z i) = T)
    (hU : Finset.univ.sum (fun i => q i - p i) = U)
    (hUeq : U = pX - qX)
    (_hPB : PB = B.sum (fun i => p i))
    (hAB : AB = B.sum (fun i => alpha i))
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hbound : ∀ i j : α, |gamma i j| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hABratio : AB / alphaX ≤ PB / pX)
    (hz :
      ∀ i : α,
        z i / alpha i + T / alphaX +
          lam * Finset.univ.sum (fun j => gamma i j * z j) = 1)
    (hs :
      ∀ i : α,
        (q i - p i) / alpha i + U / alphaX =
          lam * Finset.univ.sum (fun j => gamma i j * (q j - p j)) -
            lam * delta * (PB + pX * if i ∈ B then (1 : ℝ) else 0)) :
    pX ≤ qX := by
  classical
  let s : α → ℝ := fun i => q i - p i
  have hs' :
      ∀ i : α,
        s i / alpha i + U / alphaX =
          lam * Finset.univ.sum (fun j => gamma i j * s j) -
            lam * delta * (PB + pX * if i ∈ B then (1 : ℝ) else 0) := by
    intro i
    simpa [s] using hs i
  have hU' : Finset.univ.sum (fun i => s i) = U := by
    simpa [s] using hU
  have henergy :
      Finset.univ.sum (fun i => |z i| ^ 2 / alpha i) +
          T ^ 2 / alphaX = T :=
    finiteComparison_energy_identity hT hskew hz
  have hTnonneg : 0 ≤ T :=
    finiteComparison_T_nonneg halpha halphaX henergy
  have hdiag : ∀ i : α, gamma i i = 0 := by
    intro i
    have h := hskew i i
    linarith
  have hg_nonneg :
      ∀ i : α, 0 ≤ z i / alpha i + T / alphaX := by
    intro i
    have habs :
        (Finset.univ.erase i).sum (fun j => |z j|) ≤ (1 : ℝ) / 4 :=
      finiteComparison_abs_erase_le_quarter
        halpha halphaX halpha_sum henergy
    have hcz :
        Finset.univ.sum (fun j => gamma i j * z j) ≤ K / 4 :=
      coordinateCz_le_of_abs_sum_bound
        (by
          have h := hbound i i
          exact le_trans (abs_nonneg _) h)
        (hdiag i) (hbound i) habs
    have hresp :
        0 ≤ 1 - lam * Finset.univ.sum (fun j => gamma i j * z j) :=
      coordinateResponse_nonneg_of_cz_bound
        hlam.le hlamK hcz rfl
    have hzi :
        z i / alpha i + T / alphaX =
          1 - lam * Finset.univ.sum (fun j => gamma i j * z j) := by
      linarith [hz i]
    rwa [hzi]
  have hz_lower :
      ∀ i ∈ B, z i ≥ -(alpha i / alphaX) * T := by
    intro i hi
    have hg := hg_nonneg i
    have hmul := mul_nonneg (halpha i).le hg
    have hrewrite :
        alpha i * (z i / alpha i + T / alphaX) =
          z i + (alpha i / alphaX) * T := by
      field_simp [(halpha i).ne', halphaX.ne']
    rw [hrewrite] at hmul
    linarith
  have hsum_z_lower :
      B.sum (fun i => z i) ≥ -(AB / alphaX) * T := by
    have hsum_lower :
        B.sum (fun i => z i) ≥
          B.sum (fun i => -(alpha i / alphaX) * T) := by
      exact Finset.sum_le_sum (fun i hi => hz_lower i hi)
    have hsum_eq :
        B.sum (fun i => -(alpha i / alphaX) * T) =
          -(AB / alphaX) * T := by
      rw [hAB]
      calc
        B.sum (fun i => -(alpha i / alphaX) * T)
            = B.sum (fun i => -((T / alphaX) * alpha i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              field_simp [halphaX.ne']
        _ = -B.sum (fun i => (T / alphaX) * alpha i) := by
              rw [Finset.sum_neg_distrib]
        _ = -(T / alphaX * B.sum (fun i => alpha i)) := by
              rw [Finset.mul_sum]
        _ = -(T / alphaX) * B.sum (fun i => alpha i) := by
              ring
        _ = -(B.sum (fun i => alpha i) / alphaX) * T := by
              field_simp [halphaX.ne']
    linarith
  have hbracket_nonneg :
      0 ≤ PB * T + pX * B.sum (fun i => z i) := by
    have hmul_lower :
        pX * B.sum (fun i => z i) ≥ pX * (-(AB / alphaX) * T) :=
      mul_le_mul_of_nonneg_left hsum_z_lower hpX.le
    have hratio_mul : pX * (AB / alphaX) ≤ PB := by
      have hmul := mul_le_mul_of_nonneg_left hABratio hpX.le
      calc
        pX * (AB / alphaX) ≤ pX * (PB / pX) := hmul
        _ = PB := by
          field_simp [hpX.ne']
    have hbracket : 0 ≤ PB - pX * (AB / alphaX) := by
      linarith
    have hTmul : 0 ≤ T * (PB - pX * (AB / alphaX)) :=
      mul_nonneg hTnonneg hbracket
    nlinarith
  have hUformula :
      U = -lam * delta *
        (PB * T + pX * B.sum (fun i => z i)) :=
    finiteComparison_block_duality hT hU' hskew hz hs'
  have hUle : U ≤ 0 := by
    rw [hUformula]
    have hcoeff : 0 ≤ lam * delta := by positivity
    nlinarith
  linarith

/-- Direct finite comparison with the auxiliary solution supplied by finite
linear algebra, rather than assumed.  The remaining hypotheses are the endpoint
secant system and the logarithmic-mean block comparison. -/
theorem finiteComparison_from_secant
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q alpha : α → ℝ} {gamma : α → α → ℝ}
    {pX qX alphaX lam delta K PB AB : ℝ} {B : Finset α}
    (hpX : 0 < pX)
    (halpha : ∀ i : α, 0 < alpha i)
    (halphaX : 0 < alphaX)
    (halpha_sum : alphaX + Finset.univ.sum (fun i => alpha i) ≤ 1)
    (hU : Finset.univ.sum (fun i => q i - p i) = pX - qX)
    (hPB : PB = B.sum (fun i => p i))
    (hAB : AB = B.sum (fun i => alpha i))
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hbound : ∀ i j : α, |gamma i j| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hABratio : AB / alphaX ≤ PB / pX)
    (hs :
      ∀ i : α,
        (q i - p i) / alpha i + (pX - qX) / alphaX =
          lam * Finset.univ.sum (fun j => gamma i j * (q j - p j)) -
            lam * delta * (PB + pX * if i ∈ B then (1 : ℝ) else 0)) :
    pX ≤ qX := by
  classical
  rcases finiteComparison_auxiliary_solution_exists
      (alpha := alpha) (gamma := gamma) (alphaX := alphaX)
      (lam := lam) halpha halphaX hskew with
    ⟨z, hz⟩
  exact finiteComparison_from_secant_auxiliary
    (p := p) (q := q) (alpha := alpha) (z := z)
    (gamma := gamma) (pX := pX) (qX := qX)
    (alphaX := alphaX) (lam := lam) (delta := delta)
    (K := K) (U := pX - qX)
    (T := Finset.univ.sum (fun i => z i)) (PB := PB) (AB := AB)
    (B := B) hpX halpha halphaX halpha_sum rfl hU rfl hPB hAB
    hskew hbound hlam hdelta hlamK hABratio hz hs

/-- Direct finite comparison stated with the actual logarithmic means from the
endpoint proof.  The hypotheses `hXarith` and `hcoordarith` are the
coordinatewise arithmetic-mean upper bound for the logarithmic mean; the
remaining logarithmic-mean input is the block-ratio estimate. -/
theorem finiteComparison_from_logMean_secant
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} {gamma : α → α → ℝ}
    {pX qX lam delta K : ℝ} {B : Finset α}
    (hpX : 0 < pX)
    (hqX : 0 < qX)
    (hp : ∀ i : α, 0 < p i)
    (hq : ∀ i : α, 0 < q i)
    (hp_total : pX + Finset.univ.sum (fun i => p i) = 1)
    (hq_total : qX + Finset.univ.sum (fun i => q i) = 1)
    (hXarith : logMean pX qX ≤ (pX + qX) / 2)
    (hcoordarith :
      ∀ i : α, logMean (p i) (q i) ≤ (p i + q i) / 2)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hbound : ∀ i j : α, |gamma i j| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hBlockRatio :
      B.sum (fun i => logMean (p i) (q i)) / logMean pX qX ≤
        B.sum (fun i => p i) / pX)
    (hs :
      ∀ i : α,
        (q i - p i) / logMean (p i) (q i) +
            (pX - qX) / logMean pX qX =
          lam * Finset.univ.sum
            (fun j => gamma i j * (q j - p j)) -
            lam * delta *
              (B.sum (fun i => p i) +
                pX * if i ∈ B then (1 : ℝ) else 0)) :
    pX ≤ qX := by
  classical
  have hU : Finset.univ.sum (fun i => q i - p i) = pX - qX := by
    rw [Finset.sum_sub_distrib]
    nlinarith
  exact finiteComparison_from_secant
    (p := p) (q := q)
    (alpha := fun i => logMean (p i) (q i))
    (gamma := gamma) (pX := pX) (qX := qX)
    (alphaX := logMean pX qX) (lam := lam) (delta := delta)
    (K := K) (PB := B.sum (fun i => p i))
    (AB := B.sum (fun i => logMean (p i) (q i))) (B := B)
    hpX
    (fun i => logMean_pos (hp i) (hq i))
    (logMean_pos hpX hqX)
    (logMean_total_weight_le_one_of_arithmetic
      hp_total hq_total hXarith hcoordarith)
    hU rfl rfl hskew hbound hlam hdelta hlamK hBlockRatio hs

/-- Direct finite comparison with the arithmetic logarithmic-mean bound proved
rather than assumed. -/
theorem finiteComparison_from_logMean_secant_arithmetic
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} {gamma : α → α → ℝ}
    {pX qX lam delta K : ℝ} {B : Finset α}
    (hpX : 0 < pX)
    (hqX : 0 < qX)
    (hp : ∀ i : α, 0 < p i)
    (hq : ∀ i : α, 0 < q i)
    (hp_total : pX + Finset.univ.sum (fun i => p i) = 1)
    (hq_total : qX + Finset.univ.sum (fun i => q i) = 1)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hbound : ∀ i j : α, |gamma i j| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hBlockRatio :
      B.sum (fun i => logMean (p i) (q i)) / logMean pX qX ≤
        B.sum (fun i => p i) / pX)
    (hs :
      ∀ i : α,
        (q i - p i) / logMean (p i) (q i) +
            (pX - qX) / logMean pX qX =
          lam * Finset.univ.sum
            (fun j => gamma i j * (q j - p j)) -
            lam * delta *
              (B.sum (fun i => p i) +
                pX * if i ∈ B then (1 : ℝ) else 0)) :
    pX ≤ qX := by
  exact finiteComparison_from_logMean_secant
    (p := p) (q := q) (gamma := gamma) (pX := pX) (qX := qX)
    (lam := lam) (delta := delta) (K := K) (B := B)
    hpX hqX hp hq hp_total hq_total
    (logMean_arithmetic_le hpX hqX)
    (fun i => logMean_arithmetic_le (hp i) (hq i))
    hskew hbound hlam hdelta hlamK hBlockRatio hs

/-- Same finite comparison, with the block-ratio hypothesis derived from the
finite-odds comparison and the two logarithmic-mean block facts. -/
theorem finiteComparison_from_logMean_secant_and_block_facts
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} {gamma : α → α → ℝ}
    {pX qX lam delta K : ℝ} {B : Finset α}
    (hpX : 0 < pX)
    (hqX : 0 < qX)
    (hp : ∀ i : α, 0 < p i)
    (hq : ∀ i : α, 0 < q i)
    (hp_total : pX + Finset.univ.sum (fun i => p i) = 1)
    (hq_total : qX + Finset.univ.sum (fun i => q i) = 1)
    (hXarith : logMean pX qX ≤ (pX + qX) / 2)
    (hcoordarith :
      ∀ i : α, logMean (p i) (q i) ≤ (p i + q i) / 2)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hbound : ∀ i j : α, |gamma i j| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hPBpos : 0 < B.sum (fun i => p i))
    (hodds :
      pX * B.sum (fun i => q i) ≤ qX * B.sum (fun i => p i))
    (hblockSum :
      B.sum (fun i => logMean (p i) (q i)) ≤
        logMean (B.sum (fun i => p i)) (B.sum (fun i => q i)))
    (hratioFact :
      B.sum (fun i => q i) / B.sum (fun i => p i) ≤ qX / pX →
        logMean (B.sum (fun i => p i)) (B.sum (fun i => q i)) /
            logMean pX qX ≤
          B.sum (fun i => p i) / pX)
    (hs :
      ∀ i : α,
        (q i - p i) / logMean (p i) (q i) +
            (pX - qX) / logMean pX qX =
          lam * Finset.univ.sum
            (fun j => gamma i j * (q j - p j)) -
            lam * delta *
              (B.sum (fun i => p i) +
                pX * if i ∈ B then (1 : ℝ) else 0)) :
    pX ≤ qX := by
  classical
  have hprobRatio :
      B.sum (fun i => q i) / B.sum (fun i => p i) ≤ qX / pX :=
    block_probability_ratio_le_of_odds hpX hPBpos hodds
  have hBlockRatio :
      B.sum (fun i => logMean (p i) (q i)) / logMean pX qX ≤
        B.sum (fun i => p i) / pX :=
    logMean_block_ratio_from_sum_and_ratio hpX hqX hblockSum
      (hratioFact hprobRatio)
  exact finiteComparison_from_logMean_secant
    (p := p) (q := q) (gamma := gamma) (pX := pX) (qX := qX)
    (lam := lam) (delta := delta) (K := K) (B := B)
    hpX hqX hp hq hp_total hq_total hXarith hcoordarith
    hskew hbound hlam hdelta hlamK hBlockRatio hs

/-- Same finite comparison, with the arithmetic logarithmic-mean bound proved
in Lean and only the two block logarithmic-mean facts left as explicit
standard inputs. -/
theorem finiteComparison_from_logMean_secant_and_block_facts_arithmetic
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} {gamma : α → α → ℝ}
    {pX qX lam delta K : ℝ} {B : Finset α}
    (hpX : 0 < pX)
    (hqX : 0 < qX)
    (hp : ∀ i : α, 0 < p i)
    (hq : ∀ i : α, 0 < q i)
    (hp_total : pX + Finset.univ.sum (fun i => p i) = 1)
    (hq_total : qX + Finset.univ.sum (fun i => q i) = 1)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hbound : ∀ i j : α, |gamma i j| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hPBpos : 0 < B.sum (fun i => p i))
    (hodds :
      pX * B.sum (fun i => q i) ≤ qX * B.sum (fun i => p i))
    (hblockSum :
      B.sum (fun i => logMean (p i) (q i)) ≤
        logMean (B.sum (fun i => p i)) (B.sum (fun i => q i)))
    (hratioFact :
      B.sum (fun i => q i) / B.sum (fun i => p i) ≤ qX / pX →
        logMean (B.sum (fun i => p i)) (B.sum (fun i => q i)) /
            logMean pX qX ≤
          B.sum (fun i => p i) / pX)
    (hs :
      ∀ i : α,
        (q i - p i) / logMean (p i) (q i) +
            (pX - qX) / logMean pX qX =
          lam * Finset.univ.sum
            (fun j => gamma i j * (q j - p j)) -
            lam * delta *
              (B.sum (fun i => p i) +
                pX * if i ∈ B then (1 : ℝ) else 0)) :
    pX ≤ qX := by
  exact finiteComparison_from_logMean_secant_and_block_facts
    (p := p) (q := q) (gamma := gamma) (pX := pX) (qX := qX)
    (lam := lam) (delta := delta) (K := K) (B := B)
    hpX hqX hp hq hp_total hq_total
    (logMean_arithmetic_le hpX hqX)
    (fun i => logMean_arithmetic_le (hp i) (hq i))
    hskew hbound hlam hdelta hlamK hPBpos hodds hblockSum
    hratioFact hs

/-- Same finite comparison, with the logarithmic-mean ratio estimate proved
in Lean.  The remaining standard logarithmic-mean input is the block-sum
estimate. -/
theorem finiteComparison_from_logMean_secant_and_block_sum_arithmetic
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} {gamma : α → α → ℝ}
    {pX qX lam delta K : ℝ} {B : Finset α}
    (hpX : 0 < pX)
    (hqX : 0 < qX)
    (hp : ∀ i : α, 0 < p i)
    (hq : ∀ i : α, 0 < q i)
    (hp_total : pX + Finset.univ.sum (fun i => p i) = 1)
    (hq_total : qX + Finset.univ.sum (fun i => q i) = 1)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hbound : ∀ i j : α, |gamma i j| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hPBpos : 0 < B.sum (fun i => p i))
    (hQBpos : 0 < B.sum (fun i => q i))
    (hodds :
      pX * B.sum (fun i => q i) ≤ qX * B.sum (fun i => p i))
    (hblockSum :
      B.sum (fun i => logMean (p i) (q i)) ≤
        logMean (B.sum (fun i => p i)) (B.sum (fun i => q i)))
    (hs :
      ∀ i : α,
        (q i - p i) / logMean (p i) (q i) +
            (pX - qX) / logMean pX qX =
          lam * Finset.univ.sum
            (fun j => gamma i j * (q j - p j)) -
            lam * delta *
              (B.sum (fun i => p i) +
                pX * if i ∈ B then (1 : ℝ) else 0)) :
    pX ≤ qX := by
  exact finiteComparison_from_logMean_secant_and_block_facts_arithmetic
    (p := p) (q := q) (gamma := gamma) (pX := pX) (qX := qX)
    (lam := lam) (delta := delta) (K := K) (B := B)
    hpX hqX hp hq hp_total hq_total hskew hbound hlam hdelta hlamK
    hPBpos hodds hblockSum
    (fun hratio =>
      logMean_ratio_le_of_ratio hPBpos hQBpos hpX hqX hratio)
    hs

/-- Same finite comparison, with the block-sum logarithmic-mean estimate also
proved in Lean.  The remaining hypotheses are the endpoint secant system and
the finite-odds comparison. -/
theorem finiteComparison_from_logMean_secant_complete
    {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} {gamma : α → α → ℝ}
    {pX qX lam delta K : ℝ} {B : Finset α}
    (hpX : 0 < pX)
    (hqX : 0 < qX)
    (hp : ∀ i : α, 0 < p i)
    (hq : ∀ i : α, 0 < q i)
    (hp_total : pX + Finset.univ.sum (fun i => p i) = 1)
    (hq_total : qX + Finset.univ.sum (fun i => q i) = 1)
    (hskew : ∀ i j : α, gamma i j = -gamma j i)
    (hbound : ∀ i j : α, |gamma i j| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hBne : B.Nonempty)
    (hodds :
      pX * B.sum (fun i => q i) ≤ qX * B.sum (fun i => p i))
    (hs :
      ∀ i : α,
        (q i - p i) / logMean (p i) (q i) +
            (pX - qX) / logMean pX qX =
          lam * Finset.univ.sum
            (fun j => gamma i j * (q j - p j)) -
            lam * delta *
              (B.sum (fun i => p i) +
                pX * if i ∈ B then (1 : ℝ) else 0)) :
    pX ≤ qX := by
  have hPBpos : 0 < B.sum (fun i => p i) :=
    Finset.sum_pos (fun i hi => hp i) hBne
  have hQBpos : 0 < B.sum (fun i => q i) :=
    Finset.sum_pos (fun i hi => hq i) hBne
  have hblockSum :
      B.sum (fun i => logMean (p i) (q i)) ≤
        logMean (B.sum (fun i => p i)) (B.sum (fun i => q i)) :=
    logMean_block_sum_le hBne (fun i _hi => hp i) (fun i _hi => hq i)
  exact finiteComparison_from_logMean_secant_and_block_sum_arithmetic
    (p := p) (q := q) (gamma := gamma) (pX := pX) (qX := qX)
    (lam := lam) (delta := delta) (K := K) (B := B)
    hpX hqX hp hq hp_total hq_total hskew hbound hlam hdelta hlamK
    hPBpos hQBpos hodds hblockSum hs

/-- Full-candidate version of the finite comparison.  This theorem starts
from the old and new NLHF fixed points, derives the secant system from the
fixed-point equations, derives the odds comparison from the two variational
inequalities, and then applies the finite comparison on the subtype
`{y // y ≠ x}`.  The two block logarithmic-mean facts remain explicit
standard inputs. -/
theorem finiteComparison_from_fixed_points_and_block_facts_arithmetic
    {β : Type*} [Fintype β] [DecidableEq β]
    {τ lam delta K : ℝ} {M Mplus : β → β → ℝ}
    {ρ p q : β → ℝ} {x : β}
    {B : Finset {y : β // y ≠ x}}
    (hfp : IsNLHFFixedPoint τ M ρ p)
    (hfp' : IsNLHFFixedPoint τ Mplus ρ q)
    (hlamdef : lam = nlhfLambda τ)
    (hMplus_skew : ∀ a b : β, Mplus b a = -Mplus a b)
    (hchange : ∀ a y : β,
      Mplus a y - M a y =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun y : β => y ≠ x)))
          delta a y)
    (hBne : B.Nonempty)
    (hbound : ∀ i j : {y : β // y ≠ x},
      |nlhfCoordinateC Mplus x i.1 j.1| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hvarOld :
      -(1 / lam) * KL p ρ ≥
        marginValue M q p - (1 / lam) * KL q ρ)
    (hvarNew :
      -(1 / lam) * KL q ρ ≥
        marginValue Mplus p q - (1 / lam) * KL p ρ)
    (hblockSum :
      B.sum (fun i => logMean (p i.1) (q i.1)) ≤
        logMean (B.sum (fun i => p i.1)) (B.sum (fun i => q i.1)))
    (hratioFact :
      B.sum (fun i => q i.1) / B.sum (fun i => p i.1) ≤ q x / p x →
        logMean (B.sum (fun i => p i.1)) (B.sum (fun i => q i.1)) /
            logMean (p x) (q x) ≤
          B.sum (fun i => p i.1) / p x) :
    p x ≤ q x := by
  classical
  let Bfull : Finset β :=
    B.map (Function.Embedding.subtype (fun y : β => y ≠ x))
  have hxBfull : x ∉ Bfull := by
    dsimp [Bfull]
    exact Finset.notMem_map_subtype_of_not_property B (by simp)
  have hp_total :
      p x + Finset.univ.sum (fun i : {y : β // y ≠ x} => p i.1) = 1 := by
    rw [sum_univ_subtype_ne_eq_erase]
    rw [Finset.add_sum_erase (s := Finset.univ) (f := fun y => p y)
      (by simp : x ∈ (Finset.univ : Finset β))]
    exact hfp.2.2.1.2
  have hq_total :
      q x + Finset.univ.sum (fun i : {y : β // y ≠ x} => q i.1) = 1 := by
    rw [sum_univ_subtype_ne_eq_erase]
    rw [Finset.add_sum_erase (s := Finset.univ) (f := fun y => q y)
      (by simp : x ∈ (Finset.univ : Finset β))]
    exact hfp'.2.2.1.2
  have hBsum_p_full :
      Bfull.sum (fun b => p b) = B.sum (fun i => p i.1) := by
    dsimp [Bfull]
    exact Finset.sum_map (s := B)
      (e := Function.Embedding.subtype (fun y : β => y ≠ x)) (f := p)
  have hBsum_q_full :
      Bfull.sum (fun b => q b) = B.sum (fun i => q i.1) := by
    dsimp [Bfull]
    exact Finset.sum_map (s := B)
      (e := Function.Embedding.subtype (fun y : β => y ≠ x)) (f := q)
  have hodds_full :
      p x * Bfull.sum (fun b => q b) ≤
        q x * Bfull.sum (fun b => p b) := by
    exact finiteOdds_from_variational_inequalities
      (M := M) (Mplus := Mplus) (p := p) (q := q) (ρ := ρ)
      (lam := lam) (delta := delta) (x := x) (B := Bfull)
      hMplus_skew hdelta (by simpa [Bfull] using hchange)
      hvarOld hvarNew
  have hodds :
      p x * B.sum (fun i => q i.1) ≤
        q x * B.sum (fun i => p i.1) := by
    rw [← hBsum_p_full, ← hBsum_q_full]
    exact hodds_full
  have hPBpos : 0 < B.sum (fun i => p i.1) :=
    Finset.sum_pos (fun i _hi => hfp.2.2.1.1 i.1) hBne
  have hgamma_skew :
      ∀ i j : {y : β // y ≠ x},
        nlhfCoordinateC Mplus x i.1 j.1 =
          -nlhfCoordinateC Mplus x j.1 i.1 := by
    intro i j
    have h :
        nlhfCoordinateC Mplus x j.1 i.1 =
          -nlhfCoordinateC Mplus x i.1 j.1 := by
      unfold nlhfCoordinateC
      rw [hMplus_skew]
      ring
    linarith
  have hs :
      ∀ i : {y : β // y ≠ x},
        (q i.1 - p i.1) / logMean (p i.1) (q i.1) +
            (p x - q x) / logMean (p x) (q x) =
          lam * Finset.univ.sum
            (fun j : {y : β // y ≠ x} =>
              nlhfCoordinateC Mplus x i.1 j.1 * (q j.1 - p j.1)) -
            lam * delta *
              (B.sum (fun i => p i.1) +
                p x * if i ∈ B then (1 : ℝ) else 0) := by
    intro i
    have hsec := secant_system_from_fixed_points_logMean
      (M := M) (Mplus := Mplus) (ρ := ρ) (p := p) (q := q)
      (τ := τ) (lam := lam) (x := x) (i := i.1) (B := Bfull)
      (delta := delta)
      hfp hfp' hlamdef hMplus_skew
      (by simpa [Bfull] using hchange) i.2 hxBfull
    have hsum :
        (Finset.univ.erase x).sum (fun j =>
            (q j - p j) * nlhfCoordinateC Mplus x i.1 j) =
          Finset.univ.sum (fun j : {y : β // y ≠ x} =>
            nlhfCoordinateC Mplus x i.1 j.1 * (q j.1 - p j.1)) := by
      rw [← sum_univ_subtype_ne_eq_erase]
      refine Finset.sum_congr rfl ?_
      intro j _hj
      ring
    have hmem : (i.1 ∈ Bfull) ↔ i ∈ B := by
      dsimp [Bfull]
      exact mem_map_subtype_ne i
    rw [hBsum_p_full, hsum] at hsec
    by_cases hiB : i ∈ B
    · have hiBfull : i.1 ∈ Bfull := hmem.mpr hiB
      simp [hiB, hiBfull] at hsec ⊢
      exact hsec
    · have hiBfull : i.1 ∉ Bfull := mt hmem.mp hiB
      simp [hiB, hiBfull] at hsec ⊢
      exact hsec
  exact finiteComparison_from_logMean_secant_and_block_facts_arithmetic
    (p := fun i : {y : β // y ≠ x} => p i.1)
    (q := fun i : {y : β // y ≠ x} => q i.1)
    (gamma := fun i j : {y : β // y ≠ x} =>
      nlhfCoordinateC Mplus x i.1 j.1)
    (pX := p x) (qX := q x) (lam := lam) (delta := delta)
    (K := K) (B := B)
    (hfp.2.2.1.1 x) (hfp'.2.2.1.1 x)
    (fun i => hfp.2.2.1.1 i.1) (fun i => hfp'.2.2.1.1 i.1)
    hp_total hq_total hgamma_skew hbound hlam hdelta hlamK
    hPBpos hodds hblockSum hratioFact hs

/-- Full-candidate finite comparison with the logarithmic-mean ratio estimate
proved in Lean.  The only logarithmic-mean input still supplied as a standard
fact is the block-sum estimate. -/
theorem finiteComparison_from_fixed_points_and_block_sum_arithmetic
    {β : Type*} [Fintype β] [DecidableEq β]
    {τ lam delta K : ℝ} {M Mplus : β → β → ℝ}
    {ρ p q : β → ℝ} {x : β}
    {B : Finset {y : β // y ≠ x}}
    (hfp : IsNLHFFixedPoint τ M ρ p)
    (hfp' : IsNLHFFixedPoint τ Mplus ρ q)
    (hlamdef : lam = nlhfLambda τ)
    (hMplus_skew : ∀ a b : β, Mplus b a = -Mplus a b)
    (hchange : ∀ a y : β,
      Mplus a y - M a y =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun y : β => y ≠ x)))
          delta a y)
    (hBne : B.Nonempty)
    (hbound : ∀ i j : {y : β // y ≠ x},
      |nlhfCoordinateC Mplus x i.1 j.1| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hvarOld :
      -(1 / lam) * KL p ρ ≥
        marginValue M q p - (1 / lam) * KL q ρ)
    (hvarNew :
      -(1 / lam) * KL q ρ ≥
        marginValue Mplus p q - (1 / lam) * KL p ρ)
    (hblockSum :
      B.sum (fun i => logMean (p i.1) (q i.1)) ≤
        logMean (B.sum (fun i => p i.1)) (B.sum (fun i => q i.1))) :
    p x ≤ q x := by
  have hPBpos : 0 < B.sum (fun i => p i.1) :=
    Finset.sum_pos (fun i _hi => hfp.2.2.1.1 i.1) hBne
  have hQBpos : 0 < B.sum (fun i => q i.1) :=
    Finset.sum_pos (fun i _hi => hfp'.2.2.1.1 i.1) hBne
  exact finiteComparison_from_fixed_points_and_block_facts_arithmetic
    (hfp := hfp) (hfp' := hfp') (hlamdef := hlamdef)
    (hMplus_skew := hMplus_skew) (hchange := hchange)
    (hBne := hBne) (hbound := hbound) (hlam := hlam)
    (hdelta := hdelta) (hlamK := hlamK)
    (hvarOld := hvarOld) (hvarNew := hvarNew)
    (hblockSum := hblockSum)
    (hratioFact := fun hratio =>
      logMean_ratio_le_of_ratio hPBpos hQBpos
        (hfp.2.2.1.1 x) (hfp'.2.2.1.1 x) hratio)

/-- Full-candidate finite comparison with the logarithmic-mean arithmetic,
ratio, and block-sum estimates all proved in Lean.  The remaining paper-level
inputs are the fixed-point characterization and the two variational
inequalities. -/
theorem finiteComparison_from_fixed_points_arithmetic
    {β : Type*} [Fintype β] [DecidableEq β]
    {τ lam delta K : ℝ} {M Mplus : β → β → ℝ}
    {ρ p q : β → ℝ} {x : β}
    {B : Finset {y : β // y ≠ x}}
    (hfp : IsNLHFFixedPoint τ M ρ p)
    (hfp' : IsNLHFFixedPoint τ Mplus ρ q)
    (hlamdef : lam = nlhfLambda τ)
    (hMplus_skew : ∀ a b : β, Mplus b a = -Mplus a b)
    (hchange : ∀ a y : β,
      Mplus a y - M a y =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun y : β => y ≠ x)))
          delta a y)
    (hBne : B.Nonempty)
    (hbound : ∀ i j : {y : β // y ≠ x},
      |nlhfCoordinateC Mplus x i.1 j.1| ≤ K)
    (hlam : 0 < lam)
    (hdelta : 0 < delta)
    (hlamK : lam * K ≤ 4)
    (hvarOld :
      -(1 / lam) * KL p ρ ≥
        marginValue M q p - (1 / lam) * KL q ρ)
    (hvarNew :
      -(1 / lam) * KL q ρ ≥
        marginValue Mplus p q - (1 / lam) * KL p ρ) :
    p x ≤ q x := by
  have hblockSum :
      B.sum (fun i => logMean (p i.1) (q i.1)) ≤
        logMean (B.sum (fun i => p i.1)) (B.sum (fun i => q i.1)) :=
    logMean_block_sum_le hBne
      (fun i _hi => hfp.2.2.1.1 i.1)
      (fun i _hi => hfp'.2.2.1.1 i.1)
  exact finiteComparison_from_fixed_points_and_block_sum_arithmetic
    (hfp := hfp) (hfp' := hfp') (hlamdef := hlamdef)
    (hMplus_skew := hMplus_skew) (hchange := hchange)
    (hBne := hBne) (hbound := hbound) (hlam := hlam)
    (hdelta := hdelta) (hlamK := hlamK)
    (hvarOld := hvarOld) (hvarNew := hvarNew)
    (hblockSum := hblockSum)

/-- Partially replace the `x` row and column of `M` by those of `Mplus`, for
the opponents in `S`. -/
def partialImprovement
    {α : Type*} [DecidableEq α]
    (M Mplus : α → α → ℝ) (x : α) (S : Finset α) : α → α → ℝ :=
  fun a b =>
    if a = x ∧ b ∈ S then Mplus a b
    else if a ∈ S ∧ b = x then Mplus a b
    else M a b

lemma partialImprovement_empty
    {α : Type*} [DecidableEq α]
    (M Mplus : α → α → ℝ) (x : α) :
    partialImprovement M Mplus x ∅ = M := by
  funext a b
  simp [partialImprovement]

lemma partialImprovement_insert_eq_improvePairMargin
    {α : Type*} [DecidableEq α]
    {M Mplus : α → α → ℝ} {x y : α} {S : Finset α}
    (hM : IsNormalizedMarginMatrix M)
    (hMplus : IsNormalizedMarginMatrix Mplus)
    (hyx : y ≠ x)
    (hxS : x ∉ S)
    (hyS : y ∉ S) :
    partialImprovement M Mplus x (insert y S) =
      improvePairMargin (partialImprovement M Mplus x S)
        x y (Mplus x y - M x y) := by
  funext a b
  by_cases hax : a = x
  · subst a
    by_cases hby : b = y
    · subst b
      simp [partialImprovement, improvePairMargin, hyx, hyS]
    · have hxy : x ≠ y := hyx ∘ Eq.symm
      have hbin : b ∈ insert y S ↔ b ∈ S := by
        simp [hby]
      simp [partialImprovement, improvePairMargin, hby, hxy, hxS, hbin]
  · by_cases hay : a = y
    · subst a
      by_cases hbx : b = x
      · subst b
        have hxy : x ≠ y := hyx ∘ Eq.symm
        simp [partialImprovement, improvePairMargin, hyx, hxy, hyS,
          hM.2.1 x y, hMplus.2.1 x y]
        ring
      · simp [partialImprovement, improvePairMargin, hax, hbx, hyS]
    · by_cases hbx : b = x
      · subst b
        have hain : a ∈ insert y S ↔ a ∈ S := by
          simp [hay]
        simp [partialImprovement, improvePairMargin, hax, hay, hain]
      · have hnot₁ : ¬ (a = x ∧ b ∈ insert y S) := by
          intro h
          exact hax h.1
        have hnot₂ : ¬ (a ∈ insert y S ∧ b = x) := by
          intro h
          exact hbx h.2
        have hnot₃ : ¬ (a = x ∧ b = y) := by
          intro h
          exact hax h.1
        have hnot₄ : ¬ (a = y ∧ b = x) := by
          intro h
          exact hay h.1
        simp [partialImprovement, improvePairMargin, hax, hay, hbx]

lemma partialImprovement_univ_erase_eq_of_improvement
    {α : Type*} [Fintype α] [DecidableEq α]
    {M Mplus : α → α → ℝ} {x : α}
    (hM : IsNormalizedMarginMatrix M)
    (hMplus : IsNormalizedMarginMatrix Mplus)
    (himp : IsImprovementOf M Mplus x) :
    partialImprovement M Mplus x (Finset.univ.erase x) = Mplus := by
  funext a b
  by_cases hax : a = x
  · subst a
    by_cases hbx : b = x
    · subst b
      simp [partialImprovement, hM.1 x, hMplus.1 x]
    · simp [partialImprovement, hbx]
  · by_cases hbx : b = x
    · subst b
      simp [partialImprovement, hax]
    · have hfixed := himp.2.2 a b hax hbx
      simp [partialImprovement, hax, hbx, hfixed]

/-- If a rule is monotone for every single pair-improvement, then it is
monotone for every finite margin improvement. -/
theorem monotonicity_from_pair_improvements
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : MatrixRule α}
    (hpair :
      ∀ {M : α → α → ℝ} {ρ : α → ℝ} {x y : α} {δ : ℝ},
        IsNormalizedMarginMatrix M →
          IsFullSupportLottery ρ →
            y ≠ x →
              0 < δ →
                δ ≤ 1 - M x y →
                  F M ρ x ≤ F (improvePairMargin M x y δ) ρ x) :
    SatisfiesProbabilisticMonotonicity F := by
  classical
  intro M Mplus ρ x hM hMplus hρ himp
  let target : Finset α := Finset.univ.erase x
  have hind :
      ∀ S : Finset α, S ⊆ target →
        F M ρ x ≤ F (partialImprovement M Mplus x S) ρ x ∧
          IsNormalizedMarginMatrix (partialImprovement M Mplus x S) := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hsub
      simp [partialImprovement_empty, hM]
    · intro y S hyS ih hsub
      have hSsub : S ⊆ target := by
        intro z hz
        exact hsub (by simp [hz])
      rcases ih hSsub with ⟨hmonoS, hnormS⟩
      have hy_target : y ∈ target := hsub (by simp)
      have hyx : y ≠ x := by simpa [target] using hy_target
      have hstep :=
        partialImprovement_insert_eq_improvePairMargin
          (M := M) (Mplus := Mplus) (x := x) (y := y) (S := S)
          hM hMplus hyx
          (by
            intro hxmem
            have hx_target : x ∉ target := by simp [target]
            exact hx_target (hSsub hxmem))
          hyS
      let δ : ℝ := Mplus x y - M x y
      have hδnonneg : 0 ≤ δ := by
        dsimp [δ]
        exact sub_nonneg.mpr (himp.1 y hyx)
      have hpartial_xy :
          partialImprovement M Mplus x S x y = M x y := by
        simp [partialImprovement, hyS, hyx]
      by_cases hδzero : δ = 0
      · have hstep0 :
            partialImprovement M Mplus x (insert y S) =
              partialImprovement M Mplus x S := by
          have hδzero' : Mplus x y - M x y = 0 := by
            simpa [δ] using hδzero
          rw [hstep, hδzero']
          exact improvePairMargin_zero
            (partialImprovement M Mplus x S) x y
        rw [hstep0]
        exact ⟨hmonoS, hnormS⟩
      · have hδpos : 0 < δ := lt_of_le_of_ne hδnonneg (Ne.symm hδzero)
        have hδle : δ ≤ 1 - partialImprovement M Mplus x S x y := by
          rw [hpartial_xy]
          have hupper := (abs_le.mp (hMplus.2.2 x y)).2
          dsimp [δ]
          linarith
        have hmono_step :
            F (partialImprovement M Mplus x S) ρ x ≤
              F (improvePairMargin (partialImprovement M Mplus x S)
                x y δ) ρ x :=
          hpair hnormS hρ hyx hδpos hδle
        have hnorm_insert :
            IsNormalizedMarginMatrix
              (partialImprovement M Mplus x (insert y S)) := by
          rw [hstep]
          exact improvePairMargin_normalized hnormS (hyx ∘ Eq.symm)
            hδpos.le hδle
        have hmono_insert :
            F M ρ x ≤ F (partialImprovement M Mplus x (insert y S)) ρ x := by
          rw [hstep]
          exact le_trans hmonoS hmono_step
        exact ⟨hmono_insert, hnorm_insert⟩
  have htarget_sub : target ⊆ target := by intro z hz; exact hz
  have hmono_target := (hind target htarget_sub).1
  rwa [partialImprovement_univ_erase_eq_of_improvement hM hMplus himp] at hmono_target

/-- Elementary continuity of the finite expected-margin expression under
coordinatewise convergence of both the margin matrix and the lottery.  This is
one checked substep of the local-regularity/closedness argument for NLHF fixed
points. -/
lemma tendsto_expectedMargin
    {α ι : Type*} [Fintype α] [DecidableEq α]
    {l : Filter ι}
    {Mseq : ι → α → α → ℝ} {πseq : ι → α → ℝ}
    {M : α → α → ℝ} {π : α → ℝ} {x : α}
    (hM : ∀ a b : α, Filter.Tendsto (fun n : ι => Mseq n a b) l (𝓝 (M a b)))
    (hπ : ∀ a : α, Filter.Tendsto (fun n : ι => πseq n a) l (𝓝 (π a))) :
    Filter.Tendsto
      (fun n : ι => expectedMargin (Mseq n) (πseq n) x)
      l (𝓝 (expectedMargin M π x)) := by
  unfold expectedMargin
  exact tendsto_finset_sum Finset.univ
    (fun y _hy => (hπ y).mul (hM x y))

/-- Closedness of the finite lottery simplex under coordinatewise limits. -/
lemma isLottery_of_tendsto
    {α ι : Type*} [Fintype α]
    {l : Filter ι} [NeBot l]
    {πseq : ι → α → ℝ} {π : α → ℝ}
    (hπ : ∀ a : α, Filter.Tendsto (fun n : ι => πseq n a) l (𝓝 (π a)))
    (hseq : ∀ᶠ n in l, IsLottery (πseq n)) :
    IsLottery π := by
  have hnonneg : ∀ a : α, 0 ≤ π a := by
    intro a
    exact ge_of_tendsto (hπ a) (hseq.mono fun n hn => hn.1 a)
  have hsum_tendsto :
      Filter.Tendsto
        (fun n : ι => Finset.univ.sum (fun a : α => πseq n a))
        l (𝓝 (Finset.univ.sum (fun a : α => π a))) :=
    tendsto_finset_sum Finset.univ (fun a _ha => hπ a)
  have hsum_const :
      Filter.Tendsto
        (fun _n : ι => (1 : ℝ)) l (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have heq :
      (fun n : ι => Finset.univ.sum (fun a : α => πseq n a)) =ᶠ[l]
        fun _n : ι => (1 : ℝ) := by
    filter_upwards [hseq] with n hn
    exact hn.2
  have hsum_one :
      Finset.univ.sum (fun a : α => π a) = 1 :=
    tendsto_nhds_unique hsum_tendsto
      (Filter.Tendsto.congr' heq.symm hsum_const)
  exact ⟨hnonneg, hsum_one⟩

/-- Closedness of normalized finite margin matrices under coordinatewise
limits. -/
lemma isNormalizedMarginMatrix_of_tendsto
    {α ι : Type*} [Fintype α] [DecidableEq α]
    {l : Filter ι} [NeBot l]
    {Mseq : ι → α → α → ℝ} {M : α → α → ℝ}
    (hM : ∀ a b : α, Filter.Tendsto (fun n : ι => Mseq n a b) l (𝓝 (M a b)))
    (hseq : ∀ᶠ n in l, IsNormalizedMarginMatrix (Mseq n)) :
    IsNormalizedMarginMatrix M := by
  refine ⟨?diag, ?skew, ?bound⟩
  · intro x
    have hzero :
        Filter.Tendsto (fun _n : ι => (0 : ℝ)) l (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds
    have heq :
        (fun n : ι => Mseq n x x) =ᶠ[l] fun _n : ι => (0 : ℝ) := by
      filter_upwards [hseq] with n hn
      exact hn.1 x
    exact tendsto_nhds_unique (hM x x)
      (Filter.Tendsto.congr' heq.symm hzero)
  · intro x y
    have hneg :
        Filter.Tendsto (fun n : ι => -Mseq n x y) l (𝓝 (-M x y)) :=
      (hM x y).neg
    have heq :
        (fun n : ι => Mseq n y x) =ᶠ[l]
          fun n : ι => -Mseq n x y := by
      filter_upwards [hseq] with n hn
      exact hn.2.1 x y
    exact tendsto_nhds_unique (hM y x)
      (Filter.Tendsto.congr' heq.symm hneg)
  · intro x y
    have habs :
        Filter.Tendsto (fun n : ι => |Mseq n x y|) l (𝓝 |M x y|) :=
      (continuous_abs.tendsto _).comp (hM x y)
    exact le_of_tendsto habs
      (hseq.mono fun n hn => hn.2.2 x y)

/-- Continuity of the finite NLHF normalizing denominator under
coordinatewise convergence of the margin matrix and lottery. -/
lemma tendsto_nlhfDenominator
    {α ι : Type*} [Fintype α] [DecidableEq α]
    {l : Filter ι} {τ : ℝ}
    {Mseq : ι → α → α → ℝ} {πseq : ι → α → ℝ}
    {M : α → α → ℝ} {π ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : ∀ a b : α, Filter.Tendsto (fun n : ι => Mseq n a b) l (𝓝 (M a b)))
    (hπ : ∀ a : α, Filter.Tendsto (fun n : ι => πseq n a) l (𝓝 (π a))) :
    Filter.Tendsto
      (fun n : ι =>
        Finset.univ.sum
          (fun z : α =>
            ρ z * Real.exp (expectedMargin (Mseq n) (πseq n) z / (2 * τ))))
      l
      (𝓝
        (Finset.univ.sum
          (fun z : α =>
            ρ z * Real.exp (expectedMargin M π z / (2 * τ))))) := by
  have htwoτ : (2 * τ) ≠ 0 := by nlinarith
  refine tendsto_finset_sum Finset.univ ?_
  intro z _hz
  have hmargin :
      Filter.Tendsto
        (fun n : ι => expectedMargin (Mseq n) (πseq n) z)
        l (𝓝 (expectedMargin M π z)) :=
    tendsto_expectedMargin (x := z) hM hπ
  have harg :
      Filter.Tendsto
        (fun n : ι => expectedMargin (Mseq n) (πseq n) z / (2 * τ))
        l (𝓝 (expectedMargin M π z / (2 * τ))) :=
    hmargin.div tendsto_const_nhds htwoτ
  have hexp :
      Filter.Tendsto
        (fun n : ι =>
          Real.exp (expectedMargin (Mseq n) (πseq n) z / (2 * τ)))
        l (𝓝 (Real.exp (expectedMargin M π z / (2 * τ)))) :=
    (Real.continuous_exp.tendsto _).comp harg
  exact tendsto_const_nhds.mul hexp

/-- Positivity of the NLHF normalizing denominator for a full-support
reference lottery. -/
lemma nlhfDenominator_pos
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {τ : ℝ} {M : α → α → ℝ} {π ρ : α → ℝ}
    (hρ : IsFullSupportLottery ρ) :
    0 <
      Finset.univ.sum
        (fun z : α =>
          ρ z * Real.exp (expectedMargin M π z / (2 * τ))) := by
  exact Finset.sum_pos
    (fun z _hz => mul_pos (hρ.1 z) (Real.exp_pos _))
    Finset.univ_nonempty

/-- Continuity of one coordinate of the right-hand side of the NLHF
fixed-point equation, assuming the limiting normalizing denominator is
nonzero. -/
lemma tendsto_nlhfFixedPointRHS
    {α ι : Type*} [Fintype α] [DecidableEq α]
    {l : Filter ι} {τ : ℝ}
    {Mseq : ι → α → α → ℝ} {πseq : ι → α → ℝ}
    {M : α → α → ℝ} {π ρ : α → ℝ} {x : α}
    (hτ : 0 < τ)
    (hM : ∀ a b : α, Filter.Tendsto (fun n : ι => Mseq n a b) l (𝓝 (M a b)))
    (hπ : ∀ a : α, Filter.Tendsto (fun n : ι => πseq n a) l (𝓝 (π a)))
    (hden :
      Finset.univ.sum
        (fun z : α =>
          ρ z * Real.exp (expectedMargin M π z / (2 * τ))) ≠ 0) :
    Filter.Tendsto
      (fun n : ι =>
        ρ x * Real.exp (expectedMargin (Mseq n) (πseq n) x / (2 * τ)) /
          Finset.univ.sum
            (fun z : α =>
              ρ z *
                Real.exp (expectedMargin (Mseq n) (πseq n) z / (2 * τ))))
      l
      (𝓝
        (ρ x * Real.exp (expectedMargin M π x / (2 * τ)) /
          Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M π z / (2 * τ))))) := by
  have htwoτ : (2 * τ) ≠ 0 := by nlinarith
  have hmargin :
      Filter.Tendsto
        (fun n : ι => expectedMargin (Mseq n) (πseq n) x)
        l (𝓝 (expectedMargin M π x)) :=
    tendsto_expectedMargin (x := x) hM hπ
  have harg :
      Filter.Tendsto
        (fun n : ι => expectedMargin (Mseq n) (πseq n) x / (2 * τ))
        l (𝓝 (expectedMargin M π x / (2 * τ))) :=
    hmargin.div tendsto_const_nhds htwoτ
  have hexp :
      Filter.Tendsto
        (fun n : ι =>
          Real.exp (expectedMargin (Mseq n) (πseq n) x / (2 * τ)))
        l (𝓝 (Real.exp (expectedMargin M π x / (2 * τ)))) :=
    (Real.continuous_exp.tendsto _).comp harg
  have hnum :
      Filter.Tendsto
        (fun n : ι =>
          ρ x * Real.exp (expectedMargin (Mseq n) (πseq n) x / (2 * τ)))
        l (𝓝 (ρ x * Real.exp (expectedMargin M π x / (2 * τ)))) :=
    tendsto_const_nhds.mul hexp
  have hden_tendsto :=
    tendsto_nlhfDenominator (τ := τ) (ρ := ρ)
      hτ hM hπ
  exact hnum.div hden_tendsto hden

/-- The displayed NLHF fixed-point equations are closed under coordinatewise
limits of the margin matrix and lottery, once the limiting normalizer is
nonzero.  This isolates the elementary continuity part of the converse proof's
local-regularity argument. -/
theorem nlhfFixedPoint_equations_of_tendsto
    {α ι : Type*} [Fintype α] [DecidableEq α]
    {l : Filter ι} [NeBot l] {τ : ℝ}
    {Mseq : ι → α → α → ℝ} {πseq : ι → α → ℝ}
    {M : α → α → ℝ} {π ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : ∀ a b : α, Filter.Tendsto (fun n : ι => Mseq n a b) l (𝓝 (M a b)))
    (hπ : ∀ a : α, Filter.Tendsto (fun n : ι => πseq n a) l (𝓝 (π a)))
    (hden :
      Finset.univ.sum
        (fun z : α =>
          ρ z * Real.exp (expectedMargin M π z / (2 * τ))) ≠ 0)
    (hfp : ∀ᶠ n in l, IsNLHFFixedPoint τ (Mseq n) ρ (πseq n)) :
    ∀ x : α,
      π x =
        ρ x * Real.exp (expectedMargin M π x / (2 * τ)) /
          Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M π z / (2 * τ))) := by
  intro x
  have hrhs :
      Filter.Tendsto
        (fun n : ι =>
          ρ x * Real.exp (expectedMargin (Mseq n) (πseq n) x / (2 * τ)) /
            Finset.univ.sum
              (fun z : α =>
                ρ z *
                  Real.exp (expectedMargin (Mseq n) (πseq n) z / (2 * τ))))
        l
        (𝓝
          (ρ x * Real.exp (expectedMargin M π x / (2 * τ)) /
            Finset.univ.sum
              (fun z : α =>
                ρ z * Real.exp (expectedMargin M π z / (2 * τ))))) :=
    tendsto_nlhfFixedPointRHS (x := x) hτ hM hπ hden
  have heq :
      (fun n : ι => πseq n x) =ᶠ[l]
        (fun n : ι =>
          ρ x * Real.exp (expectedMargin (Mseq n) (πseq n) x / (2 * τ)) /
            Finset.univ.sum
              (fun z : α =>
                ρ z *
                  Real.exp (expectedMargin (Mseq n) (πseq n) z / (2 * τ)))) := by
    filter_upwards [hfp] with n hn
    exact hn.2.2.2 x
  have hrhs_left :
      Filter.Tendsto (fun n : ι => πseq n x) l
        (𝓝
          (ρ x * Real.exp (expectedMargin M π x / (2 * τ)) /
            Finset.univ.sum
              (fun z : α =>
                ρ z * Real.exp (expectedMargin M π z / (2 * τ))))) :=
    Filter.Tendsto.congr' heq.symm hrhs
  exact tendsto_nhds_unique (hπ x) hrhs_left

/-- Paper-facing version of `nlhfFixedPoint_equations_of_tendsto`: with a
full-support reference lottery on a nonempty finite candidate set, the limiting
normalizer is automatically nonzero. -/
theorem nlhfFixedPoint_equations_of_tendsto_fullSupportReference
    {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {l : Filter ι} [NeBot l] {τ : ℝ}
    {Mseq : ι → α → α → ℝ} {πseq : ι → α → ℝ}
    {M : α → α → ℝ} {π ρ : α → ℝ}
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hM : ∀ a b : α, Filter.Tendsto (fun n : ι => Mseq n a b) l (𝓝 (M a b)))
    (hπ : ∀ a : α, Filter.Tendsto (fun n : ι => πseq n a) l (𝓝 (π a)))
    (hfp : ∀ᶠ n in l, IsNLHFFixedPoint τ (Mseq n) ρ (πseq n)) :
    ∀ x : α,
      π x =
        ρ x * Real.exp (expectedMargin M π x / (2 * τ)) /
          Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M π z / (2 * τ))) :=
  nlhfFixedPoint_equations_of_tendsto hτ hM hπ
    (nlhfDenominator_pos (τ := τ) (M := M) (π := π) hρ).ne'
    hfp

/-- Closed-graph form of the NLHF fixed-point equations: a coordinatewise
limit of fixed points is again a fixed point, for a fixed full-support
reference lottery on a nonempty finite candidate set.  This checks the
elementary finite-dimensional closedness step used in the converse continuity
argument. -/
theorem isNLHFFixedPoint_of_tendsto_fullSupportReference
    {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {l : Filter ι} [NeBot l] {τ : ℝ}
    {Mseq : ι → α → α → ℝ} {πseq : ι → α → ℝ}
    {M : α → α → ℝ} {π ρ : α → ℝ}
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hM : ∀ a b : α, Filter.Tendsto (fun n : ι => Mseq n a b) l (𝓝 (M a b)))
    (hπlim : ∀ a : α, Filter.Tendsto (fun n : ι => πseq n a) l (𝓝 (π a)))
    (hfp : ∀ᶠ n in l, IsNLHFFixedPoint τ (Mseq n) ρ (πseq n)) :
    IsNLHFFixedPoint τ M ρ π := by
  let D : ℝ :=
    Finset.univ.sum
      (fun z : α => ρ z * Real.exp (expectedMargin M π z / (2 * τ)))
  have hDpos : 0 < D := by
    dsimp [D]
    exact nlhfDenominator_pos (τ := τ) (M := M) (π := π) hρ
  have hDne : D ≠ 0 := hDpos.ne'
  have heq :
      ∀ x : α,
        π x =
          ρ x * Real.exp (expectedMargin M π x / (2 * τ)) / D := by
    intro x
    dsimp [D]
    exact nlhfFixedPoint_equations_of_tendsto_fullSupportReference
      hτ hρ hM hπlim hfp x
  have hπpos : ∀ x : α, 0 < π x := by
    intro x
    rw [heq x]
    exact div_pos (mul_pos (hρ.1 x) (Real.exp_pos _)) hDpos
  have hπsum : Finset.univ.sum (fun x : α => π x) = 1 := by
    calc
      Finset.univ.sum (fun x : α => π x) =
          Finset.univ.sum
            (fun x : α =>
              ρ x * Real.exp (expectedMargin M π x / (2 * τ)) / D) := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            exact heq x
      _ = D / D := by
            rw [Finset.sum_div]
      _ = 1 := by
            field_simp [hDne]
  exact ⟨hτ, hρ, ⟨hπpos, hπsum⟩, by
    intro x
    dsimp [D] at heq
    exact heq x⟩

/-- If the selected NLHF rule is unique and a net of fixed points converges
coordinatewise along converging margin matrices, then the limiting lottery is
the selected NLHF lottery for the limiting instance. -/
theorem fixedPoint_limit_eq_selected_of_tendsto
    {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {l : Filter ι} [NeBot l] {τ : ℝ}
    {F : ℝ → MatrixRule α}
    {Mseq : ι → α → α → ℝ} {πseq : ι → α → ℝ}
    {M : α → α → ℝ} {π ρ : α → ℝ}
    (hunique : IsTheNLHF F)
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hMnorm : IsNormalizedMarginMatrix M)
    (hM : ∀ a b : α, Filter.Tendsto (fun n : ι => Mseq n a b) l (𝓝 (M a b)))
    (hπlim : ∀ a : α, Filter.Tendsto (fun n : ι => πseq n a) l (𝓝 (π a)))
    (hfp : ∀ᶠ n in l, IsNLHFFixedPoint τ (Mseq n) ρ (πseq n)) :
    π = F τ M ρ := by
  have hlimit :
      IsNLHFFixedPoint τ M ρ π :=
    isNLHFFixedPoint_of_tendsto_fullSupportReference
      hτ hρ hM hπlim hfp
  exact (hunique hMnorm hlimit).symm

/-- Sequential continuity of the selected NLHF fixed point in the margin
matrix.  This formalizes Lemma `nlhf-continuity-in-margin` from the current
TeX proof using exactly its compactness argument: any subsequence of selected
lotteries has a further convergent subsequence in the compact simplex; the
closed graph of the fixed-point equations sends that limit to the limiting
fixed point; uniqueness forces the limit to be the selected one.  The
existence and uniqueness of the selected NLHF fixed point are the cited NLHF
inputs from Proposition `nlhf-existence`/Remark `nlhffixed`. -/
theorem selectedNLHF_tendsto_of_margin_tendsto
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {F : ℝ → MatrixRule α}
    {τ : ℝ} {Mseq : ℕ → α → α → ℝ} {M : α → α → ℝ}
    {ρ : α → ℝ}
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F)
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hMseq : ∀ n : ℕ, IsNormalizedMarginMatrix (Mseq n))
    (hM : IsNormalizedMarginMatrix M)
    (hMtendsto :
      ∀ a b : α,
        Filter.Tendsto (fun n : ℕ => Mseq n a b) Filter.atTop (𝓝 (M a b))) :
    Filter.Tendsto
      (fun n : ℕ => F τ (Mseq n) ρ)
      Filter.atTop
      (𝓝 (F τ M ρ)) := by
  classical
  have hcompact : IsCompact {π : α → ℝ | IsLottery π} :=
    isCompact_setOf_isLottery
  refine Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  let u : ℕ → α → ℝ := fun n => F τ (Mseq (ns n)) ρ
  have hu_mem : ∀ n : ℕ, u n ∈ {π : α → ℝ | IsLottery π} := by
    intro n
    have hfp : IsNLHFFixedPoint τ (Mseq (ns n)) ρ (F τ (Mseq (ns n)) ρ) :=
      hselect hτ (hMseq (ns n)) hρ
    exact hfp.2.2.1.toLottery
  rcases hcompact.tendsto_subseq hu_mem with
    ⟨q, hqmem, φ, hφmono, hφlim⟩
  have hnsφ : Filter.Tendsto (fun n : ℕ => ns (φ n)) Filter.atTop Filter.atTop :=
    hns.comp hφmono.tendsto_atTop
  have hMlim :
      ∀ a b : α,
        Filter.Tendsto
          (fun n : ℕ => Mseq (ns (φ n)) a b)
          Filter.atTop (𝓝 (M a b)) := by
    intro a b
    exact (hMtendsto a b).comp hnsφ
  have hπlim :
      ∀ a : α,
        Filter.Tendsto
          (fun n : ℕ => F τ (Mseq (ns (φ n))) ρ a)
          Filter.atTop (𝓝 (q a)) := by
    intro a
    simpa [u, Function.comp_def] using
      (tendsto_pi_nhds.1 hφlim a)
  have hfp_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        IsNLHFFixedPoint τ (Mseq (ns (φ n))) ρ
          (F τ (Mseq (ns (φ n))) ρ) :=
    Eventually.of_forall fun n =>
      hselect hτ (hMseq (ns (φ n))) hρ
  have hq :
      q = F τ M ρ :=
    fixedPoint_limit_eq_selected_of_tendsto
      (F := F) (Mseq := fun n : ℕ => Mseq (ns (φ n)))
      (πseq := fun n : ℕ => F τ (Mseq (ns (φ n))) ρ)
      (M := M) (π := q) (ρ := ρ)
      hunique hτ hρ hM hMlim hπlim hfp_event
  refine ⟨φ, ?_⟩
  simpa [u, Function.comp_def, hq] using hφlim

/-- Coordinate form of `selectedNLHF_tendsto_of_margin_tendsto`, matching the
paper's notation `\pi^n(a) -> \pi(a)`. -/
theorem selectedNLHF_coordinate_tendsto_of_margin_tendsto
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {F : ℝ → MatrixRule α}
    {τ : ℝ} {Mseq : ℕ → α → α → ℝ} {M : α → α → ℝ}
    {ρ : α → ℝ} {x : α}
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F)
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hMseq : ∀ n : ℕ, IsNormalizedMarginMatrix (Mseq n))
    (hM : IsNormalizedMarginMatrix M)
    (hMtendsto :
      ∀ a b : α,
        Filter.Tendsto (fun n : ℕ => Mseq n a b) Filter.atTop (𝓝 (M a b))) :
    Filter.Tendsto
      (fun n : ℕ => F τ (Mseq n) ρ x)
      Filter.atTop
      (𝓝 (F τ M ρ x)) :=
  tendsto_pi_nhds.1
    (selectedNLHF_tendsto_of_margin_tendsto
      hselect hunique hτ hρ hMseq hM hMtendsto) x

/-- The all-profile three-candidate converse, up to choosing an explicit
positive sequence of improvement sizes tending to `0`.  This is the formal
counterpart of the TeX step: continuity sends `π^s` to `μ`, the finite-secant
formula gives the sign of `π^s(x)-μ(x)`, and the negative limiting numerator
therefore gives an actual small positive improvement with a strict drop. -/
theorem exists_nlhfSharpAll_secant_drop_index_of_small_sequence
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F)
    {τ b η a d : ℝ}
    (hτ : 0 < τ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (ha : a = (1 - b) / 2) (hd : d = 3 - η)
    (ha0 : 0 < a) (_hd0 : 0 < d)
    (hlimitneg : 2 + b / a - nlhfLambda τ * d * a < 0)
    {sseq : ℕ → ℝ}
    (hspos : ∀ n : ℕ, 0 < sseq n)
    (hsle : ∀ n : ℕ, sseq n ≤ η)
    (hstendsto : Filter.Tendsto sseq Filter.atTop (𝓝 0)) :
    ∃ n : ℕ,
      0 < sseq n ∧ sseq n ≤ η ∧
      F τ (improvePairMargin (nlhfSharpAllMargin3 η) 0 1 (sseq n))
          (nlhfBacksolvedReference τ (nlhfSharpAllMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 <
        F τ (nlhfSharpAllMargin3 η)
          (nlhfBacksolvedReference τ (nlhfSharpAllMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 := by
  classical
  let μ : Fin 3 → ℝ := nlhfSharpSymLottery3 b
  let M : Fin 3 → Fin 3 → ℝ := nlhfSharpAllMargin3 η
  let ρ : Fin 3 → ℝ := nlhfBacksolvedReference τ M μ
  let Mseq : ℕ → Fin 3 → Fin 3 → ℝ :=
    fun n => improvePairMargin M 0 1 (sseq n)
  let πseq : ℕ → Fin 3 → ℝ := fun n => F τ (Mseq n) ρ
  let Dseq : ℕ → ℝ := fun n => nlhfCoordinateC (Mseq n) 0 1 2
  let den : ℕ → ℝ := fun n =>
    nlhfLambda τ ^ 2 * Dseq n ^ 2 +
      1 / (logMean (μ 1) (πseq n 1) * logMean (μ 2) (πseq n 2)) +
      1 / (logMean (μ 1) (πseq n 1) * logMean (μ 0) (πseq n 0)) +
      1 / (logMean (μ 2) (πseq n 2) * logMean (μ 0) (πseq n 0))
  let Δx : ℕ → ℝ := fun n => πseq n 0 - μ 0
  have hμ : IsFullSupportLottery μ := by
    dsimp [μ]
    exact nlhfSharpSymLottery3_fullSupport hb0 hb1
  have hρ : IsFullSupportLottery ρ := by
    dsimp [ρ]
    exact nlhfBacksolvedReference_fullSupport hμ
  have hM : IsNormalizedMarginMatrix M := by
    dsimp [M]
    exact nlhfSharpAllMargin3_normalized hη0.le (by linarith)
  have hMseq : ∀ n : ℕ, IsNormalizedMarginMatrix (Mseq n) := by
    intro n
    dsimp [Mseq, M]
    exact nlhfSharpAll_improve_xy_normalized hη0.le (by linarith)
      (hspos n).le (hsle n)
  have hMtendsto :
      ∀ i j : Fin 3,
        Filter.Tendsto (fun n : ℕ => Mseq n i j)
          Filter.atTop (𝓝 (M i j)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp [Mseq, M, improvePairMargin]
    · simpa [Mseq, M, improvePairMargin] using
        (tendsto_const_nhds.add hstendsto :
          Filter.Tendsto
            (fun n : ℕ => nlhfSharpAllMargin3 η 0 1 + sseq n)
            Filter.atTop (𝓝 (nlhfSharpAllMargin3 η 0 1 + 0)))
    · simp [Mseq, M, improvePairMargin]
    · simpa [Mseq, M, improvePairMargin] using
        (tendsto_const_nhds.sub hstendsto :
          Filter.Tendsto
            (fun n : ℕ => nlhfSharpAllMargin3 η 1 0 - sseq n)
            Filter.atTop (𝓝 (nlhfSharpAllMargin3 η 1 0 - 0)))
    · simp [Mseq, M, improvePairMargin]
    · simp [Mseq, M, improvePairMargin]
    · simp [Mseq, M, improvePairMargin]
    · simp [Mseq, M, improvePairMargin]
    · simp [Mseq, M, improvePairMargin]
  have hF_old : F τ M ρ = μ := by
    dsimp [ρ]
    exact nlhfBacksolvedReference_selected hunique hM hτ hμ
  have hnewY :
      Filter.Tendsto (fun n : ℕ => πseq n 1) Filter.atTop (𝓝 b) := by
    have hcoord :
        Filter.Tendsto (fun n : ℕ => F τ (Mseq n) ρ 1)
          Filter.atTop (𝓝 (F τ M ρ 1)) :=
      selectedNLHF_coordinate_tendsto_of_margin_tendsto
        hselect hunique hτ hρ hMseq hM hMtendsto
    simpa [πseq, hF_old, μ, nlhfSharpSymLottery3] using hcoord
  have hnewZ :
      Filter.Tendsto (fun n : ℕ => πseq n 2) Filter.atTop (𝓝 a) := by
    have hcoord :
        Filter.Tendsto (fun n : ℕ => F τ (Mseq n) ρ 2)
          Filter.atTop (𝓝 (F τ M ρ 2)) :=
      selectedNLHF_coordinate_tendsto_of_margin_tendsto
        hselect hunique hτ hρ hMseq hM hMtendsto
    simpa [πseq, hF_old, μ, nlhfSharpSymLottery3, ha] using hcoord
  have holdY :
      Filter.Tendsto (fun _n : ℕ => μ 1) Filter.atTop (𝓝 b) := by
    simp [μ, nlhfSharpSymLottery3]
  have holdZ :
      Filter.Tendsto (fun _n : ℕ => μ 2) Filter.atTop (𝓝 a) := by
    simp [μ, nlhfSharpSymLottery3, ha]
  have hDexpr : ∀ n : ℕ, Dseq n = d + sseq n := by
    intro n
    dsimp [Dseq, Mseq, M]
    rw [hd]
    have h20 : ¬ ((2 : Fin 3) = 0) := by decide
    have h21 : ¬ ((2 : Fin 3) = 1) := by decide
    simp [nlhfCoordinateC, nlhfSharpAllMargin3, improvePairMargin, h20, h21]
    ring_nf
  have hD :
      Filter.Tendsto Dseq Filter.atTop (𝓝 d) := by
    have hsum :
        Filter.Tendsto (fun n : ℕ => d + sseq n) Filter.atTop (𝓝 (d + 0)) :=
      tendsto_const_nhds.add hstendsto
    exact Filter.Tendsto.congr'
      (Eventually.of_forall fun n => (hDexpr n).symm)
      (by simpa using hsum)
  have hden : ∀ᶠ n in Filter.atTop, 0 < den n := by
    refine Eventually.of_forall ?_
    intro n
    have hfp : IsNLHFFixedPoint τ M ρ μ := by
      dsimp [ρ]
      exact nlhfBacksolvedReference_fixedPoint hτ hμ
    have hfp' : IsNLHFFixedPoint τ (Mseq n) ρ (πseq n) :=
      hselect hτ (hMseq n) hρ
    dsimp [den]
    exact threeCandidateSecant_den_pos
      (logMean_pos (hfp.2.2.1.1 0) (hfp'.2.2.1.1 0))
      (logMean_pos (hfp.2.2.1.1 1) (hfp'.2.2.1.1 1))
      (logMean_pos (hfp.2.2.1.1 2) (hfp'.2.2.1.1 2))
  have hformula : ∀ᶠ n in Filter.atTop,
      Δx n =
        nlhfLambda τ * sseq n *
          (a / logMean (μ 2) (πseq n 2) +
            b / logMean (μ 1) (πseq n 1) +
            b / logMean (μ 2) (πseq n 2) -
            nlhfLambda τ * Dseq n * a) / den n := by
    refine Eventually.of_forall ?_
    intro n
    have hfp : IsNLHFFixedPoint τ M ρ μ := by
      dsimp [ρ]
      exact nlhfBacksolvedReference_fixedPoint hτ hμ
    have hfp' : IsNLHFFixedPoint τ (Mseq n) ρ (πseq n) :=
      hselect hτ (hMseq n) hρ
    have hchange :
        ∀ a y : Fin 3,
          Mseq n a y - M a y =
            blockImprovementChange 0 ({1} : Finset (Fin 3)) (sseq n) a y := by
      intro a' y'
      exact improvePairMargin_change_eq_blockImprovementChange_singleton
        M (sseq n) (by decide) a' y'
    have hform :=
      threeCandidateSecant_formula_from_fixed_points_fin3
        (τ := τ) (lam := nlhfLambda τ) (δ := sseq n)
        (D := Dseq n) (den := den n)
        (M := M) (Mplus := Mseq n) (ρ := ρ) (μ := μ) (π := πseq n)
        hfp hfp' rfl (hMseq n) hchange rfl rfl
    simpa [Δx, den, μ, nlhfSharpSymLottery3, ha] using hform
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hspos_event : ∀ᶠ n in Filter.atTop, 0 < sseq n :=
    Eventually.of_forall hspos
  have hslt_event : ∀ᶠ n in Filter.atTop, sseq n < η :=
    hstendsto.eventually (Iio_mem_nhds hη0)
  rcases exists_threeCandidateSecant_drop_of_probability_tendsto_seq
      (sseq := sseq)
      (oldY := fun _n : ℕ => μ 1)
      (newY := fun n : ℕ => πseq n 1)
      (oldZ := fun _n : ℕ => μ 2)
      (newZ := fun n : ℕ => πseq n 2)
      (D := Dseq) (den := den) (Δx := Δx)
      (lam := nlhfLambda τ) (mux := a) (muy := b) (d := d) (ε := η)
      hlam hspos_event hslt_event ha0 hb0 holdY hnewY holdZ hnewZ hD
      hlimitneg hden hformula with
    ⟨n, hsnpos, hsnlt, hdrop⟩
  have hnew_lt : F τ (Mseq n) ρ 0 < μ 0 := by
    dsimp [Δx, πseq] at hdrop
    linarith
  have hold0 : F τ M ρ 0 = μ 0 := by
    rw [hF_old]
  exact ⟨n, hsnpos, le_of_lt hsnlt, by
    simpa [Mseq, M, ρ, μ, hold0] using hnew_lt⟩

/-- The unindexed form of `exists_nlhfSharpAll_secant_drop_index_of_small_sequence`,
kept as the interface used by the matrix-level certificate. -/
theorem exists_nlhfSharpAll_secant_drop_of_small_sequence
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F)
    {τ b η a d : ℝ}
    (hτ : 0 < τ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (ha : a = (1 - b) / 2) (hd : d = 3 - η)
    (ha0 : 0 < a) (hd0 : 0 < d)
    (hlimitneg : 2 + b / a - nlhfLambda τ * d * a < 0)
    {sseq : ℕ → ℝ}
    (hspos : ∀ n : ℕ, 0 < sseq n)
    (hsle : ∀ n : ℕ, sseq n ≤ η)
    (hstendsto : Filter.Tendsto sseq Filter.atTop (𝓝 0)) :
    ∃ δ : ℝ,
      0 < δ ∧ δ ≤ η ∧
      F τ (improvePairMargin (nlhfSharpAllMargin3 η) 0 1 δ)
          (nlhfBacksolvedReference τ (nlhfSharpAllMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 <
        F τ (nlhfSharpAllMargin3 η)
          (nlhfBacksolvedReference τ (nlhfSharpAllMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 := by
  rcases exists_nlhfSharpAll_secant_drop_index_of_small_sequence
      F hselect hunique hτ hb0 hb1 hη0 hη1 ha hd ha0 hd0 hlimitneg
      hspos hsle hstendsto with
    ⟨n, hsnpos, hsnle, hdrop⟩
  exact ⟨sseq n, hsnpos, hsnle, hdrop⟩

/-- The all-profile three-candidate converse with the concrete improvement
sequence `η/(n+1)`. -/
theorem exists_nlhfSharpAll_secant_drop
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F)
    {τ b η a d : ℝ}
    (hτ : 0 < τ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (ha : a = (1 - b) / 2) (hd : d = 3 - η)
    (ha0 : 0 < a) (hd0 : 0 < d)
    (hlimitneg : 2 + b / a - nlhfLambda τ * d * a < 0) :
    ∃ δ : ℝ,
      0 < δ ∧ δ ≤ η ∧
      F τ (improvePairMargin (nlhfSharpAllMargin3 η) 0 1 δ)
          (nlhfBacksolvedReference τ (nlhfSharpAllMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 <
        F τ (nlhfSharpAllMargin3 η)
          (nlhfBacksolvedReference τ (nlhfSharpAllMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 := by
  let sseq : ℕ → ℝ := fun n => η * (1 / ((n : ℝ) + 1))
  have hspos : ∀ n : ℕ, 0 < sseq n := by
    intro n
    dsimp [sseq]
    positivity
  have hsle : ∀ n : ℕ, sseq n ≤ η := by
    intro n
    have hdenpos : 0 < (n : ℝ) + 1 := by positivity
    have hone : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith
    dsimp [sseq]
    exact mul_le_of_le_one_right hη0.le hone
  have hone_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hstendsto : Filter.Tendsto sseq Filter.atTop (𝓝 0) := by
    simpa [sseq] using
      (tendsto_const_nhds.mul hone_tendsto :
        Filter.Tendsto
          (fun n : ℕ => η * (1 / ((n : ℝ) + 1)))
          Filter.atTop (𝓝 (η * 0)))
  exact exists_nlhfSharpAll_secant_drop_of_small_sequence
    F hselect hunique hτ hb0 hb1 hη0 hη1 ha hd ha0 hd0 hlimitneg
    hspos hsle hstendsto

/-- The low-temperature finite-secant drop certificate for the all-profile
three-candidate counterexample. -/
theorem nlhfSharpAll_lowTempSecantDropCertificate_fin3
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F) :
    HasNLHFLowTempSecantDropCertificate F := by
  intro τ hτ hτlt
  rcases exists_threeCandidateSharpnessScalar_of_tau_lt_three_eighths
      hτ hτlt with
    ⟨b, η, a, d, hb0, hb1, hη0, hη1, ha, hd, ha0, hd0, _hnorm, hlimitneg⟩
  rcases exists_nlhfSharpAll_secant_drop
      F hselect hunique hτ hb0 hb1 hη0 hη1 ha hd ha0 hd0 hlimitneg with
    ⟨δ, hδpos, hδleη, hdrop⟩
  let M : Fin 3 → Fin 3 → ℝ := nlhfSharpAllMargin3 η
  let μ : Fin 3 → ℝ := nlhfSharpSymLottery3 b
  let ρ : Fin 3 → ℝ := nlhfBacksolvedReference τ M μ
  have hM : IsNormalizedMarginMatrix M := by
    dsimp [M]
    exact nlhfSharpAllMargin3_normalized hη0.le (by linarith)
  have hμ : IsFullSupportLottery μ := by
    dsimp [μ]
    exact nlhfSharpSymLottery3_fullSupport hb0 hb1
  have hρ : IsFullSupportLottery ρ := by
    dsimp [ρ]
    exact nlhfBacksolvedReference_fullSupport hμ
  have hδle : δ ≤ 1 - M 0 1 := by
    dsimp [M]
    simpa [nlhfSharpAllMargin3] using hδleη
  refine ⟨M, ρ, 0, 1, δ, hM, hρ, by decide, hδpos, hδle, ?_⟩
  simpa [M, ρ, μ] using hdrop

/-- The linear-order three-candidate converse, up to choosing an explicit
positive sequence of improvement sizes tending to `0`.  This is the `1/8`
analogue of `exists_nlhfSharpAll_secant_drop_of_small_sequence`: the old
margin matrix has `D = 1 - η`, and improving `x` against `y` changes this to
`D + s`. -/
theorem exists_nlhfSharpLinear_secant_drop_of_small_sequence
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F)
    {τ b η a d : ℝ}
    (hτ : 0 < τ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (ha : a = (1 - b) / 2) (hd : d = 1 - η)
    (ha0 : 0 < a) (_hd0 : 0 < d)
    (hlimitneg : 2 + b / a - nlhfLambda τ * d * a < 0)
    {sseq : ℕ → ℝ}
    (hspos : ∀ n : ℕ, 0 < sseq n)
    (hsle : ∀ n : ℕ, sseq n ≤ η)
    (hstendsto : Filter.Tendsto sseq Filter.atTop (𝓝 0)) :
    ∃ n : ℕ,
      0 < sseq n ∧ sseq n ≤ η ∧
      F τ (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 (sseq n))
          (nlhfBacksolvedReference τ (nlhfSharpLinearMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 <
        F τ (nlhfSharpLinearMargin3 η)
          (nlhfBacksolvedReference τ (nlhfSharpLinearMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 := by
  classical
  let μ : Fin 3 → ℝ := nlhfSharpSymLottery3 b
  let M : Fin 3 → Fin 3 → ℝ := nlhfSharpLinearMargin3 η
  let ρ : Fin 3 → ℝ := nlhfBacksolvedReference τ M μ
  let Mseq : ℕ → Fin 3 → Fin 3 → ℝ :=
    fun n => improvePairMargin M 0 1 (sseq n)
  let πseq : ℕ → Fin 3 → ℝ := fun n => F τ (Mseq n) ρ
  let Dseq : ℕ → ℝ := fun n => nlhfCoordinateC (Mseq n) 0 1 2
  let den : ℕ → ℝ := fun n =>
    nlhfLambda τ ^ 2 * Dseq n ^ 2 +
      1 / (logMean (μ 1) (πseq n 1) * logMean (μ 2) (πseq n 2)) +
      1 / (logMean (μ 1) (πseq n 1) * logMean (μ 0) (πseq n 0)) +
      1 / (logMean (μ 2) (πseq n 2) * logMean (μ 0) (πseq n 0))
  let Δx : ℕ → ℝ := fun n => πseq n 0 - μ 0
  have hμ : IsFullSupportLottery μ := by
    dsimp [μ]
    exact nlhfSharpSymLottery3_fullSupport hb0 hb1
  have hρ : IsFullSupportLottery ρ := by
    dsimp [ρ]
    exact nlhfBacksolvedReference_fullSupport hμ
  have hM : IsNormalizedMarginMatrix M := by
    dsimp [M]
    exact nlhfSharpLinearMargin3_normalized hη0.le (by linarith)
  have hMseq : ∀ n : ℕ, IsNormalizedMarginMatrix (Mseq n) := by
    intro n
    dsimp [Mseq, M]
    exact nlhfSharpLinear_improve_xy_normalized hη0.le (by linarith)
      (hspos n).le (hsle n)
  have hMtendsto :
      ∀ i j : Fin 3,
        Filter.Tendsto (fun n : ℕ => Mseq n i j)
          Filter.atTop (𝓝 (M i j)) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp [Mseq, M, improvePairMargin]
    · simpa [Mseq, M, improvePairMargin] using
        (tendsto_const_nhds.add hstendsto :
          Filter.Tendsto
            (fun n : ℕ => nlhfSharpLinearMargin3 η 0 1 + sseq n)
            Filter.atTop (𝓝 (nlhfSharpLinearMargin3 η 0 1 + 0)))
    · simp [Mseq, M, improvePairMargin]
    · simpa [Mseq, M, improvePairMargin] using
        (tendsto_const_nhds.sub hstendsto :
          Filter.Tendsto
            (fun n : ℕ => nlhfSharpLinearMargin3 η 1 0 - sseq n)
            Filter.atTop (𝓝 (nlhfSharpLinearMargin3 η 1 0 - 0)))
    · simp [Mseq, M, improvePairMargin]
    · simp [Mseq, M, improvePairMargin]
    · simp [Mseq, M, improvePairMargin]
    · simp [Mseq, M, improvePairMargin]
    · simp [Mseq, M, improvePairMargin]
  have hF_old : F τ M ρ = μ := by
    dsimp [ρ]
    exact nlhfBacksolvedReference_selected hunique hM hτ hμ
  have hnewY :
      Filter.Tendsto (fun n : ℕ => πseq n 1) Filter.atTop (𝓝 b) := by
    have hcoord :
        Filter.Tendsto (fun n : ℕ => F τ (Mseq n) ρ 1)
          Filter.atTop (𝓝 (F τ M ρ 1)) :=
      selectedNLHF_coordinate_tendsto_of_margin_tendsto
        hselect hunique hτ hρ hMseq hM hMtendsto
    simpa [πseq, hF_old, μ, nlhfSharpSymLottery3] using hcoord
  have hnewZ :
      Filter.Tendsto (fun n : ℕ => πseq n 2) Filter.atTop (𝓝 a) := by
    have hcoord :
        Filter.Tendsto (fun n : ℕ => F τ (Mseq n) ρ 2)
          Filter.atTop (𝓝 (F τ M ρ 2)) :=
      selectedNLHF_coordinate_tendsto_of_margin_tendsto
        hselect hunique hτ hρ hMseq hM hMtendsto
    simpa [πseq, hF_old, μ, nlhfSharpSymLottery3, ha] using hcoord
  have holdY :
      Filter.Tendsto (fun _n : ℕ => μ 1) Filter.atTop (𝓝 b) := by
    simp [μ, nlhfSharpSymLottery3]
  have holdZ :
      Filter.Tendsto (fun _n : ℕ => μ 2) Filter.atTop (𝓝 a) := by
    simp [μ, nlhfSharpSymLottery3, ha]
  have hDexpr : ∀ n : ℕ, Dseq n = d + sseq n := by
    intro n
    dsimp [Dseq, Mseq, M]
    rw [hd]
    have h20 : ¬ ((2 : Fin 3) = 0) := by decide
    have h21 : ¬ ((2 : Fin 3) = 1) := by decide
    simp [nlhfCoordinateC, nlhfSharpLinearMargin3, improvePairMargin, h20, h21]
  have hD :
      Filter.Tendsto Dseq Filter.atTop (𝓝 d) := by
    have hsum :
        Filter.Tendsto (fun n : ℕ => d + sseq n) Filter.atTop (𝓝 (d + 0)) :=
      tendsto_const_nhds.add hstendsto
    exact Filter.Tendsto.congr'
      (Eventually.of_forall fun n => (hDexpr n).symm)
      (by simpa using hsum)
  have hden : ∀ᶠ n in Filter.atTop, 0 < den n := by
    refine Eventually.of_forall ?_
    intro n
    have hfp : IsNLHFFixedPoint τ M ρ μ := by
      dsimp [ρ]
      exact nlhfBacksolvedReference_fixedPoint hτ hμ
    have hfp' : IsNLHFFixedPoint τ (Mseq n) ρ (πseq n) :=
      hselect hτ (hMseq n) hρ
    dsimp [den]
    exact threeCandidateSecant_den_pos
      (logMean_pos (hfp.2.2.1.1 0) (hfp'.2.2.1.1 0))
      (logMean_pos (hfp.2.2.1.1 1) (hfp'.2.2.1.1 1))
      (logMean_pos (hfp.2.2.1.1 2) (hfp'.2.2.1.1 2))
  have hformula : ∀ᶠ n in Filter.atTop,
      Δx n =
        nlhfLambda τ * sseq n *
          (a / logMean (μ 2) (πseq n 2) +
            b / logMean (μ 1) (πseq n 1) +
            b / logMean (μ 2) (πseq n 2) -
            nlhfLambda τ * Dseq n * a) / den n := by
    refine Eventually.of_forall ?_
    intro n
    have hfp : IsNLHFFixedPoint τ M ρ μ := by
      dsimp [ρ]
      exact nlhfBacksolvedReference_fixedPoint hτ hμ
    have hfp' : IsNLHFFixedPoint τ (Mseq n) ρ (πseq n) :=
      hselect hτ (hMseq n) hρ
    have hchange :
        ∀ a y : Fin 3,
          Mseq n a y - M a y =
            blockImprovementChange 0 ({1} : Finset (Fin 3)) (sseq n) a y := by
      intro a' y'
      exact improvePairMargin_change_eq_blockImprovementChange_singleton
        M (sseq n) (by decide) a' y'
    have hform :=
      threeCandidateSecant_formula_from_fixed_points_fin3
        (τ := τ) (lam := nlhfLambda τ) (δ := sseq n)
        (D := Dseq n) (den := den n)
        (M := M) (Mplus := Mseq n) (ρ := ρ) (μ := μ) (π := πseq n)
        hfp hfp' rfl (hMseq n) hchange rfl rfl
    simpa [Δx, den, μ, nlhfSharpSymLottery3, ha] using hform
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hspos_event : ∀ᶠ n in Filter.atTop, 0 < sseq n :=
    Eventually.of_forall hspos
  have hslt_event : ∀ᶠ n in Filter.atTop, sseq n < η :=
    hstendsto.eventually (Iio_mem_nhds hη0)
  rcases exists_threeCandidateSecant_drop_of_probability_tendsto_seq
      (sseq := sseq)
      (oldY := fun _n : ℕ => μ 1)
      (newY := fun n : ℕ => πseq n 1)
      (oldZ := fun _n : ℕ => μ 2)
      (newZ := fun n : ℕ => πseq n 2)
      (D := Dseq) (den := den) (Δx := Δx)
      (lam := nlhfLambda τ) (mux := a) (muy := b) (d := d) (ε := η)
      hlam hspos_event hslt_event ha0 hb0 holdY hnewY holdZ hnewZ hD
      hlimitneg hden hformula with
    ⟨n, hsnpos, hsnlt, hdrop⟩
  have hnew_lt : F τ (Mseq n) ρ 0 < μ 0 := by
    dsimp [Δx, πseq] at hdrop
    linarith
  have hold0 : F τ M ρ 0 = μ 0 := by
    rw [hF_old]
  exact ⟨n, hsnpos, le_of_lt hsnlt, by
    simpa [Mseq, M, ρ, μ, hold0] using hnew_lt⟩

/-- The linear-order three-candidate converse with the concrete improvement
sequence `η/(n+1)`. -/
theorem exists_nlhfSharpLinear_secant_drop
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F)
    {τ b η a d : ℝ}
    (hτ : 0 < τ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (ha : a = (1 - b) / 2) (hd : d = 1 - η)
    (ha0 : 0 < a) (hd0 : 0 < d)
    (hlimitneg : 2 + b / a - nlhfLambda τ * d * a < 0) :
    ∃ δ : ℝ,
      0 < δ ∧ δ ≤ η ∧
      F τ (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ)
          (nlhfBacksolvedReference τ (nlhfSharpLinearMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 <
        F τ (nlhfSharpLinearMargin3 η)
          (nlhfBacksolvedReference τ (nlhfSharpLinearMargin3 η)
            (nlhfSharpSymLottery3 b)) 0 := by
  let sseq : ℕ → ℝ := fun n => η * (1 / ((n : ℝ) + 1))
  have hspos : ∀ n : ℕ, 0 < sseq n := by
    intro n
    dsimp [sseq]
    positivity
  have hsle : ∀ n : ℕ, sseq n ≤ η := by
    intro n
    have hdenpos : 0 < (n : ℝ) + 1 := by positivity
    have hone : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith
    dsimp [sseq]
    exact mul_le_of_le_one_right hη0.le hone
  have hone_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hstendsto : Filter.Tendsto sseq Filter.atTop (𝓝 0) := by
    simpa [sseq] using
      (tendsto_const_nhds.mul hone_tendsto :
        Filter.Tendsto
          (fun n : ℕ => η * (1 / ((n : ℝ) + 1)))
          Filter.atTop (𝓝 (η * 0)))
  rcases exists_nlhfSharpLinear_secant_drop_of_small_sequence
      F hselect hunique hτ hb0 hb1 hη0 hη1 ha hd ha0 hd0 hlimitneg
      hspos hsle hstendsto with
    ⟨n, hsnpos, hsnle, hdrop⟩
  exact ⟨sseq n, hsnpos, hsnle, hdrop⟩

/-- Matrix-level strict-drop package for the linear-order `1/8` converse.
The surrounding profile-realization lemmas show that these two matrices are
weighted linear-order profiles. -/
theorem nlhfSharpLinear_lowTempSecantDrop_fin3
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F) :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ b η δ : ℝ,
        0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
        0 < δ ∧ δ ≤ η ∧
        F τ (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ)
            (nlhfBacksolvedReference τ (nlhfSharpLinearMargin3 η)
              (nlhfSharpSymLottery3 b)) 0 <
          F τ (nlhfSharpLinearMargin3 η)
            (nlhfBacksolvedReference τ (nlhfSharpLinearMargin3 η)
              (nlhfSharpSymLottery3 b)) 0 := by
  intro τ hτ hτlt
  rcases exists_linearOrderSharpnessScalar_of_tau_lt_one_eighth
      hτ hτlt with
    ⟨b, η, a, d, hb0, hb1, hη0, hη1, ha, hd, ha0, hd0, _hnorm, hlimitneg⟩
  rcases exists_nlhfSharpLinear_secant_drop
      F hselect hunique hτ hb0 hb1 hη0 hη1 ha hd ha0 hd0 hlimitneg with
    ⟨δ, hδpos, hδleη, hdrop⟩
  exact ⟨b, η, δ, hb0, hb1, hη0, hη1, hδpos, hδleη, hdrop⟩

/-- Weighted-linear-profile form of the `1/8` converse.  The old matrix is
the weighted profile with ballot weights `1 - η/2` on `xyz` and `η/2` on
`yxz`; the improved matrix moves weight `δ/2` from `yxz` to `xyz`. -/
theorem nlhfSharpLinear_lowTempWeightedProfileDrop_fin3
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F) :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ b η δ : ℝ,
        0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
        0 < δ ∧ δ ≤ η ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfSharpSymLottery3 b)) ∧
        F τ
            (weightedScoreProfileMargin
              (nlhfSharpLinearWeights3Improved η δ)
              nlhfSharpLinearScore3)
            (nlhfBacksolvedReference τ
              (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
                nlhfSharpLinearScore3)
              (nlhfSharpSymLottery3 b)) 0 <
          F τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfBacksolvedReference τ
              (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
            nlhfSharpLinearScore3)
            (nlhfSharpSymLottery3 b)) 0 := by
  intro τ hτ hτlt
  rcases nlhfSharpLinear_lowTempSecantDrop_fin3
      F hselect hunique τ hτ hτlt with
    ⟨b, η, δ, hb0, hb1, hη0, hη1, hδpos, hδleη, hdrop⟩
  have hμ : IsFullSupportLottery (nlhfSharpSymLottery3 b) :=
    nlhfSharpSymLottery3_fullSupport hb0 hb1
  have hold :
      weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
          nlhfSharpLinearScore3 =
        nlhfSharpLinearMargin3 η :=
    nlhfSharpLinearMargin3_eq_weightedProfile η
  have hnew :
      weightedScoreProfileMargin (nlhfSharpLinearWeights3Improved η δ)
          nlhfSharpLinearScore3 =
        improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ :=
    nlhfSharpLinearImproved_eq_improvePairMargin η δ
  have hρ :
      IsFullSupportLottery
        (nlhfBacksolvedReference τ
          (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
            nlhfSharpLinearScore3)
          (nlhfSharpSymLottery3 b)) := by
    exact nlhfBacksolvedReference_fullSupport hμ
  have hdrop_weighted :
      F τ
          (weightedScoreProfileMargin
            (nlhfSharpLinearWeights3Improved η δ)
            nlhfSharpLinearScore3)
          (nlhfBacksolvedReference τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfSharpSymLottery3 b)) 0 <
        F τ
          (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
            nlhfSharpLinearScore3)
          (nlhfBacksolvedReference τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfSharpSymLottery3 b)) 0 := by
    simpa [hold, hnew] using hdrop
  exact ⟨b, η, δ, hb0, hb1, hη0, hη1, hδpos, hδleη, hρ, hdrop_weighted⟩

/-- Denominator-cleared finite-linear-profile form of the `1/8` converse.
The old profile is a replicated two-block electorate with linear orders
`xyz` and `yxz`; the improved profile moves one copied `yxz` voter to `xyz`.
This realizes the small secant improvement used in the limiting proof as an
actual finite profile improvement. -/
theorem nlhfSharpLinear_lowTempFiniteProfileDrop_fin3
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F) :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ N m : ℕ, ∃ b : ℝ,
        0 < N ∧ 0 < b ∧ b < 1 ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) ∧
        IsLinearScoreProfile (nlhfSharpLinearReplicatedOldScore3 N m) ∧
        IsLinearScoreProfile (nlhfSharpLinearReplicatedMovedScore3 N m) ∧
        IsImprovementOf
          (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
          (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
          0 ∧
        F τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
            (nlhfBacksolvedReference τ
              (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
              (nlhfSharpSymLottery3 b)) 0 <
          F τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfBacksolvedReference τ
              (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
              (nlhfSharpSymLottery3 b)) 0 := by
  intro τ hτ hτlt
  rcases exists_linearOrderFiniteEtaSharpnessScalar_of_tau_lt_one_eighth
      hτ hτlt with
    ⟨N, b, η, a, d, hN, hb0, hb1, hηeq, hη0, hη1, ha, hd,
      ha0, hd0, _hnorm, hlimitneg⟩
  let sseq : ℕ → ℝ := fun n => η * (1 / ((n : ℝ) + 1))
  have hspos : ∀ n : ℕ, 0 < sseq n := by
    intro n
    dsimp [sseq]
    positivity
  have hsle : ∀ n : ℕ, sseq n ≤ η := by
    intro n
    have hdenpos : 0 < (n : ℝ) + 1 := by positivity
    have hone : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith
    dsimp [sseq]
    exact mul_le_of_le_one_right hη0.le hone
  have hone_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hstendsto : Filter.Tendsto sseq Filter.atTop (𝓝 0) := by
    simpa [sseq] using
      (tendsto_const_nhds.mul hone_tendsto :
        Filter.Tendsto
          (fun n : ℕ => η * (1 / ((n : ℝ) + 1)))
          Filter.atTop (𝓝 (η * 0)))
  rcases exists_nlhfSharpLinear_secant_drop_of_small_sequence
      F hselect hunique hτ hb0 hb1 hη0 hη1 ha hd ha0 hd0 hlimitneg
      hspos hsle hstendsto with
    ⟨m, hsmpos, hsmle, hdrop⟩
  have hNreal : (0 : ℝ) < (N : ℕ) := by exact_mod_cast hN
  have hmreal : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hdelta :
      2 / ((N : ℝ) * ((m : ℝ) + 1)) = sseq m := by
    dsimp [sseq]
    rw [hηeq]
    field_simp [ne_of_gt hNreal, ne_of_gt hmreal]
  have hη2 : η ≤ 2 := by linarith
  have hold :
      scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m) =
        nlhfSharpLinearMargin3 η := by
    rw [hηeq]
    exact nlhfSharpLinearMargin3_eq_replicatedOldScoreProfile N m hN
  have hnew :
      scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m) =
        improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 (sseq m) := by
    have hnew0 :=
      nlhfSharpLinearImproved_eq_replicatedMovedScoreProfile N m hN
    simpa [hηeq, hdelta] using hnew0
  have hρ :
      IsFullSupportLottery
        (nlhfBacksolvedReference τ
          (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
          (nlhfSharpSymLottery3 b)) := by
    exact nlhfBacksolvedReference_fullSupport
      (nlhfSharpSymLottery3_fullSupport hb0 hb1)
  have himprove :
      IsImprovementOf
        (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
        (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
        0 := by
    have himprove0 :
        IsImprovementOf (nlhfSharpLinearMargin3 η)
          (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 (sseq m)) 0 :=
      nlhfSharpLinear_improve_xy_isImprovement
        hη0.le hη2 hsmpos.le hsmle
    rw [hold, hnew]
    exact himprove0
  have hdrop_profile :
      F τ
          (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) 0 <
        F τ
          (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) 0 := by
    rw [hold, hnew]
    exact hdrop
  exact ⟨N, m, b, hN, hb0, hb1, hρ,
    nlhfSharpLinearReplicatedOldScore3_linear N m,
    nlhfSharpLinearReplicatedMovedScore3_linear N m,
    himprove, hdrop_profile⟩

/-- One-coordinate form of Gibbs' inequality. -/
lemma klTerm_gap_nonneg {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    p - r ≤ p * Real.log (p / r) := by
  have hratio_pos : 0 < r / p := div_pos hr hp
  have hlog_le : Real.log (r / p) ≤ r / p - 1 :=
    Real.log_le_sub_one_of_pos hratio_pos
  have hlog_neg : Real.log (p / r) = -Real.log (r / p) := by
    rw [Real.log_div hp.ne' hr.ne', Real.log_div hr.ne' hp.ne']
    ring
  rw [hlog_neg]
  have hmul := mul_le_mul_of_nonneg_left hlog_le hp.le
  have hmul' : p * Real.log (r / p) ≤ r - p := by
    calc
      p * Real.log (r / p) ≤ p * (r / p - 1) := hmul
      _ = r - p := by
        field_simp [hp.ne']
  nlinarith

/-- Gibbs' inequality for full-support finite lotteries. -/
lemma KL_nonneg_of_fullSupport
    {α : Type*} [Fintype α]
    {π ρ : α → ℝ}
    (hπ : IsFullSupportLottery π)
    (hρ : IsFullSupportLottery ρ) :
    0 ≤ KL π ρ := by
  have hterm : ∀ x : α, π x - ρ x ≤ π x * Real.log (π x / ρ x) :=
    fun x => klTerm_gap_nonneg (hπ.1 x) (hρ.1 x)
  have hsum :
      Finset.univ.sum (fun x : α => π x - ρ x) ≤
        Finset.univ.sum (fun x : α => π x * Real.log (π x / ρ x)) :=
    Finset.sum_le_sum (fun x _hx => hterm x)
  have hzero :
      Finset.univ.sum (fun x : α => π x - ρ x) = 0 := by
    rw [Finset.sum_sub_distrib, hπ.2, hρ.2]
    ring
  simpa [KL, hzero] using hsum

/-- The bilinear value against a lottery is the lottery-weighted sum of
expected margins. -/
lemma marginValue_eq_sum_expected
    {α : Type*} [Fintype α]
    (M : α → α → ℝ) (ν π : α → ℝ) :
    marginValue M ν π =
      Finset.univ.sum (fun x : α => ν x * expectedMargin M π x) := by
  classical
  unfold marginValue expectedMargin
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro y _hy
  ring

/-- The fixed-point equation in log-reference form. -/
lemma nlhfFixedPoint_log_reference
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ π) (i : α) :
    Real.log (π i / ρ i) =
      nlhfLambda τ * expectedMargin M π i -
        Real.log
          (Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M π z / (2 * τ)))) := by
  classical
  let Z : ℝ := Finset.univ.sum
    (fun z : α => ρ z * Real.exp (expectedMargin M π z / (2 * τ)))
  have hρi : 0 < ρ i := hfp.2.1.1 i
  have hZi : π i =
      ρ i * Real.exp (expectedMargin M π i / (2 * τ)) / Z := by
    simpa [Z] using hfp.2.2.2 i
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact Finset.sum_pos
      (fun z _hz => mul_pos (hfp.2.1.1 z) (Real.exp_pos _))
      ⟨i, by simp⟩
  have hratio :
      π i / ρ i =
        Real.exp (expectedMargin M π i / (2 * τ)) / Z := by
    rw [hZi]
    field_simp [hρi.ne']
  rw [hratio]
  rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne']
  rw [Real.log_exp]
  dsimp [Z]
  unfold nlhfLambda
  ring

/-- Summed log-reference form of the fixed-point equation. -/
lemma nlhfFixedPoint_weighted_log_reference_sum
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π ν : α → ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ π)
    (hν : IsFullSupportLottery ν) :
    Finset.univ.sum (fun x : α => ν x * Real.log (π x / ρ x)) =
      nlhfLambda τ * marginValue M ν π -
        Real.log
          (Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M π z / (2 * τ)))) := by
  classical
  let Z : ℝ := Finset.univ.sum
    (fun z : α => ρ z * Real.exp (expectedMargin M π z / (2 * τ)))
  calc
    Finset.univ.sum (fun x : α => ν x * Real.log (π x / ρ x))
        =
      Finset.univ.sum
        (fun x : α =>
          ν x * (nlhfLambda τ * expectedMargin M π x - Real.log Z)) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        rw [nlhfFixedPoint_log_reference hfp x]
    _ =
      nlhfLambda τ * Finset.univ.sum
        (fun x : α => ν x * expectedMargin M π x) -
          Finset.univ.sum (fun x : α => ν x) * Real.log Z := by
        calc
          Finset.univ.sum
              (fun x : α =>
                ν x * (nlhfLambda τ * expectedMargin M π x - Real.log Z)) =
            Finset.univ.sum
              (fun x : α =>
                nlhfLambda τ * (ν x * expectedMargin M π x) -
                  ν x * Real.log Z) := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              ring
          _ =
            Finset.univ.sum
              (fun x : α =>
                nlhfLambda τ * (ν x * expectedMargin M π x)) -
              Finset.univ.sum (fun x : α => ν x * Real.log Z) := by
              rw [Finset.sum_sub_distrib]
          _ =
            nlhfLambda τ * Finset.univ.sum
              (fun x : α => ν x * expectedMargin M π x) -
                Finset.univ.sum (fun x : α => ν x) * Real.log Z := by
              rw [← Finset.mul_sum]
              rw [Finset.sum_mul]
    _ = nlhfLambda τ * marginValue M ν π - Real.log Z := by
        rw [← marginValue_eq_sum_expected]
        rw [hν.2]
        ring

/-- The selected fixed point's KL-to-reference value equals the negative
normalizer log when the margin matrix is skew-symmetric. -/
lemma nlhfFixedPoint_KL_reference_eq_neg_log_denominator
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hfp : IsNLHFFixedPoint τ M ρ π) :
    KL π ρ =
      -Real.log
        (Finset.univ.sum
          (fun z : α =>
            ρ z * Real.exp (expectedMargin M π z / (2 * τ)))) := by
  have hsum :=
    nlhfFixedPoint_weighted_log_reference_sum
      (ν := π) hfp hfp.2.2.1
  have hself : marginValue M π π = 0 :=
    marginValue_self_eq_zero_of_normalized π hM
  simpa [KL, hself] using hsum

/-- KL decomposition induced by an NLHF fixed point.  This is the algebraic
heart of the variational characterization: the objective gap is a KL
divergence. -/
lemma nlhfFixedPoint_KL_gap_identity
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π ν : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hfp : IsNLHFFixedPoint τ M ρ π)
    (hν : IsFullSupportLottery ν) :
    KL ν π =
      KL ν ρ - nlhfLambda τ * marginValue M ν π - KL π ρ := by
  classical
  let Z : ℝ := Finset.univ.sum
    (fun z : α => ρ z * Real.exp (expectedMargin M π z / (2 * τ)))
  have hπ : IsFullSupportLottery π := hfp.2.2.1
  have hρ : IsFullSupportLottery ρ := hfp.2.1
  have hdecomp :
      KL ν π =
        KL ν ρ -
          Finset.univ.sum (fun x : α => ν x * Real.log (π x / ρ x)) := by
    unfold KL
    calc
      Finset.univ.sum (fun x : α => ν x * Real.log (ν x / π x))
          =
        Finset.univ.sum
          (fun x : α =>
            ν x * (Real.log (ν x / ρ x) - Real.log (π x / ρ x))) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [Real.log_div (hν.1 x).ne' (hπ.1 x).ne',
            Real.log_div (hν.1 x).ne' (hρ.1 x).ne',
            Real.log_div (hπ.1 x).ne' (hρ.1 x).ne']
          ring
      _ =
        Finset.univ.sum (fun x : α => ν x * Real.log (ν x / ρ x)) -
          Finset.univ.sum (fun x : α => ν x * Real.log (π x / ρ x)) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
  have hsum :
      Finset.univ.sum (fun x : α => ν x * Real.log (π x / ρ x)) =
        nlhfLambda τ * marginValue M ν π - Real.log Z := by
    simpa [Z] using nlhfFixedPoint_weighted_log_reference_sum
      (ν := ν) hfp hν
  have hKLπ :
      KL π ρ = -Real.log Z := by
    simpa [Z] using
      nlhfFixedPoint_KL_reference_eq_neg_log_denominator hM hfp
  rw [hdecomp, hsum, hKLπ]
  ring

/-- Lemma `nlhf-variational`, including boundary lotteries.  As in the English
proof, take the first-player inequality of the diagonal closed-simplex saddle
point, cancel the opponent's constant KL term, and use skew-symmetry. -/
theorem nlhf_variational_inequality_of_normalized_fixedPoint
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π ν : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hfp : IsNLHFFixedPoint τ M ρ π)
    (hν : IsLottery ν) :
    -(1 / nlhfLambda τ) * KL π ρ ≥
      marginValue M ν π - (1 / nlhfLambda τ) * KL ν ρ := by
  have h := (regularizedClosedSaddle_of_fixedPoint hM hfp).2.2.1 ν hν
  have hself := marginValue_self_eq_zero_of_normalized π hM
  simp only [nlhfSionValue, hself] at h
  linarith

/-- Variational characterization of the selected NLHF fixed point.  This is
the formal interface to the cited NLHF variational theorem used in the
finite-odds step. -/
def SatisfiesNLHFVariationalInequality
    {α : Type*} [Fintype α] : Prop :=
  ∀ {τ : ℝ} {M : α → α → ℝ} {ρ π ν : α → ℝ},
    IsNLHFFixedPoint τ M ρ π →
      IsFullSupportLottery ν →
        -(1 / nlhfLambda τ) * KL π ρ ≥
          marginValue M ν π - (1 / nlhfLambda τ) * KL ν ρ

/-- The exact endpoint-optimality interface used by the finite-comparison
argument: the selected NLHF output beats each full-support comparison lottery
in the regularized margin objective.  This is weaker than exposing the full
variational characterization as an assumption. -/
def SatisfiesNLHFSelectedVariationalInequality
    {α : Type*} [Fintype α]
    (F : ℝ → MatrixRule α) : Prop :=
  ∀ {τ : ℝ} {M : α → α → ℝ} {ρ ν : α → ℝ},
    0 < τ →
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ →
          IsFullSupportLottery ν →
            -(1 / nlhfLambda τ) * KL (F τ M ρ) ρ ≥
          marginValue M ν (F τ M ρ) -
            (1 / nlhfLambda τ) * KL ν ρ

/-- The full-support endpoint interface used downstream is a restriction of
the all-lottery saddle-point variational inequality. -/
theorem selectedVariationalInequality_of_fixedPointSelection
    {α : Type*} [Fintype α]
    {F : ℝ → MatrixRule α}
    (hselect : IsNLHFFixedPointSelection F) :
    SatisfiesNLHFSelectedVariationalInequality F := by
  intro τ M ρ ν hτ hM hρ hν
  exact nlhf_variational_inequality_of_normalized_fixedPoint
    hM (hselect hτ hM hρ) hν.toLottery

/-- The selected endpoint inequality follows immediately from the cited
fixed-point selection theorem and the cited variational characterization. -/
theorem selectedVariationalInequality_of_selection_and_variational
    {α : Type*} [Fintype α]
    {F : ℝ → MatrixRule α}
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α)) :
    SatisfiesNLHFSelectedVariationalInequality F := by
  intro τ M ρ ν hτpos hM hρ hν
  exact hvar (hselect hτpos hM hρ) hν

/-- Lemma `finite-odds` in paper-facing selected-NLHF form.  If `Mplus` is
obtained from `M` by uniformly improving `x` against the block `B`, then the
selected endpoint lotteries satisfy the displayed odds comparison. -/
theorem finiteOdds_from_selected_NLHF
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M Mplus : α → α → ℝ} {ρ : α → ℝ} {x : α} {B : Finset α}
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτpos : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hMplus : IsNormalizedMarginMatrix Mplus)
    (hρ : IsFullSupportLottery ρ)
    (hδpos : 0 < δ)
    (hchange : ∀ a y : α,
      Mplus a y - M a y = blockImprovementChange x B δ a y) :
    F τ Mplus ρ x * B.sum (fun b => F τ M ρ b) ≥
      F τ M ρ x * B.sum (fun b => F τ Mplus ρ b) := by
  have hfp : IsNLHFFixedPoint τ M ρ (F τ M ρ) :=
    hselect hτpos hM hρ
  have hfp' : IsNLHFFixedPoint τ Mplus ρ (F τ Mplus ρ) :=
    hselect hτpos hMplus hρ
  have hvarOld :
      -(1 / nlhfLambda τ) * KL (F τ M ρ) ρ ≥
        marginValue M (F τ Mplus ρ) (F τ M ρ) -
          (1 / nlhfLambda τ) * KL (F τ Mplus ρ) ρ :=
    hselected hτpos hM hρ hfp'.2.2.1
  have hvarNew :
      -(1 / nlhfLambda τ) * KL (F τ Mplus ρ) ρ ≥
        marginValue Mplus (F τ M ρ) (F τ Mplus ρ) -
          (1 / nlhfLambda τ) * KL (F τ M ρ) ρ :=
    hselected hτpos hMplus hρ hfp.2.2.1
  exact finiteOdds_from_variational_inequalities
    (hMplus_skew := hMplus.2.1) (hdelta := hδpos)
    (hchange := hchange) (hvarOld := hvarOld) (hvarNew := hvarNew)

/-- Block-improvement monotonicity from a coordinate bound `K`.  This is the
paper's large-temperature argument after the selected fixed-point and
endpoint-optimality inequalities are supplied. -/
theorem nlhf_block_improvement_monotone_of_coordinate_bound_selected
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ K : ℝ}
    {M Mplus : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτpos : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hMplus : IsNormalizedMarginMatrix Mplus)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      Mplus a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hbound : ∀ i j : {z : α // z ≠ x},
      |nlhfCoordinateC Mplus x i.1 j.1| ≤ K)
    (hδpos : 0 < δ)
    (hlamK : nlhfLambda τ * K ≤ 4) :
    F τ M ρ x ≤ F τ Mplus ρ x := by
  classical
  have hfp : IsNLHFFixedPoint τ M ρ (F τ M ρ) :=
    hselect hτpos hM hρ
  have hfp' : IsNLHFFixedPoint τ Mplus ρ (F τ Mplus ρ) :=
    hselect hτpos hMplus hρ
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hvarOld :
      -(1 / nlhfLambda τ) * KL (F τ M ρ) ρ ≥
        marginValue M (F τ Mplus ρ) (F τ M ρ) -
          (1 / nlhfLambda τ) * KL (F τ Mplus ρ) ρ :=
    hselected hτpos hM hρ hfp'.2.2.1
  have hvarNew :
      -(1 / nlhfLambda τ) * KL (F τ Mplus ρ) ρ ≥
        marginValue Mplus (F τ M ρ) (F τ Mplus ρ) -
          (1 / nlhfLambda τ) * KL (F τ M ρ) ρ :=
    hselected hτpos hMplus hρ hfp.2.2.1
  exact finiteComparison_from_fixed_points_arithmetic
    (hfp := hfp) (hfp' := hfp') (hlamdef := rfl)
    (hMplus_skew := hMplus.2.1) (hchange := hchange)
    (hBne := hBne) (hbound := hbound) (hlam := hlam)
    (hdelta := hδpos) (hlamK := hlamK)
    (hvarOld := hvarOld) (hvarNew := hvarNew)

/-- Block-improvement monotonicity from a coordinate bound `K` and the NLHF
variational inequality, factored through the selected endpoint-optimality
interface above. -/
theorem nlhf_block_improvement_monotone_of_coordinate_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ K : ℝ}
    {M Mplus : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hτpos : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hMplus : IsNormalizedMarginMatrix Mplus)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      Mplus a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hbound : ∀ i j : {z : α // z ≠ x},
      |nlhfCoordinateC Mplus x i.1 j.1| ≤ K)
    (hδpos : 0 < δ)
    (hlamK : nlhfLambda τ * K ≤ 4) :
    F τ M ρ x ≤ F τ Mplus ρ x :=
  nlhf_block_improvement_monotone_of_coordinate_bound_selected
    (hselect := hselect)
    (hselected :=
      selectedVariationalInequality_of_selection_and_variational
        hselect hvar)
    (hτpos := hτpos) (hM := hM) (hMplus := hMplus) (hρ := hρ)
    (hchange := hchange) (hBne := hBne) (hbound := hbound)
    (hδpos := hδpos) (hlamK := hlamK)

/-- The `K = 1` large-temperature bridge stated with the selected
endpoint-optimality interface. -/
theorem nlhf_block_improvement_monotone_of_tau_ge_one_eighth_unit_bound_selected
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M Mplus : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hMplus : IsNormalizedMarginMatrix Mplus)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      Mplus a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hbound : ∀ i j : {z : α // z ≠ x},
      |nlhfCoordinateC Mplus x i.1 j.1| ≤ (1 : ℝ))
    (hδpos : 0 < δ) :
    F τ M ρ x ≤ F τ Mplus ρ x := by
  have hτpos : 0 < τ := by nlinarith
  have hlamK : nlhfLambda τ * (1 : ℝ) ≤ 4 := by
    have hle := nlhfLambda_le_four_of_tau_ge_one_eighth hτge
    nlinarith
  exact nlhf_block_improvement_monotone_of_coordinate_bound_selected
    (hselect := hselect) (hselected := hselected) (hτpos := hτpos)
    (hM := hM) (hMplus := hMplus) (hρ := hρ)
    (hchange := hchange) (hBne := hBne) (hbound := hbound)
    (hδpos := hδpos) (hlamK := hlamK)

/-- The `K = 1` large-temperature bridge used for weak-order and linear-order
profiles.  The profile-specific part of the proof is exactly the supplied
coordinate bound. -/
theorem nlhf_block_improvement_monotone_of_tau_ge_one_eighth_unit_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M Mplus : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hMplus : IsNormalizedMarginMatrix Mplus)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      Mplus a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hbound : ∀ i j : {z : α // z ≠ x},
      |nlhfCoordinateC Mplus x i.1 j.1| ≤ (1 : ℝ))
    (hδpos : 0 < δ) :
    F τ M ρ x ≤ F τ Mplus ρ x := by
  have hτpos : 0 < τ := by nlinarith
  have hlamK : nlhfLambda τ * (1 : ℝ) ≤ 4 := by
    have hle := nlhfLambda_le_four_of_tau_ge_one_eighth hτge
    nlinarith
  exact nlhf_block_improvement_monotone_of_coordinate_bound
    (hselect := hselect) (hvar := hvar) (hτpos := hτpos)
    (hM := hM) (hMplus := hMplus) (hρ := hρ)
    (hchange := hchange) (hBne := hBne) (hbound := hbound)
    (hδpos := hδpos) (hlamK := hlamK)

/-- Large-temperature monotonicity bridge for weighted weak-order profiles.
The new margin matrix is a weighted score-profile margin, so the `K = 1`
coordinate bound is proved directly from the voter-level order calculation. -/
theorem nlhf_weightedScoreProfile_block_improvement_monotone_of_tau_ge_one_eighth
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {w : V → ℝ} {score : V → α → ℝ}
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hw_nonneg : ∀ v : V, 0 ≤ w v)
    (hw_sum : Finset.univ.sum (fun v : V => w v) = 1)
    (hchange : ∀ a b : α,
      weightedScoreProfileMargin w score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    F τ M ρ x ≤ F τ (weightedScoreProfileMargin w score) ρ x := by
  have hMplus : IsNormalizedMarginMatrix (weightedScoreProfileMargin w score) :=
    weightedScoreProfileMargin_normalized score hw_nonneg hw_sum
  have hbound :
      ∀ i j : {z : α // z ≠ x},
        |nlhfCoordinateC (weightedScoreProfileMargin w score) x i.1 j.1| ≤
          (1 : ℝ) := by
    intro i j
    exact weightedScoreProfileMargin_coordinate_abs_le_one
      score hw_nonneg hw_sum x i.1 j.1
  exact nlhf_block_improvement_monotone_of_tau_ge_one_eighth_unit_bound
    (hselect := hselect) (hvar := hvar) (hτge := hτge)
    (hM := hM) (hMplus := hMplus) (hρ := hρ)
    (hchange := hchange) (hBne := hBne)
    (hbound := hbound) (hδpos := hδpos)

/-- Large-temperature monotonicity bridge for weighted weak-order profiles,
stated with the selected endpoint-optimality interface. -/
theorem nlhf_weightedScoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {w : V → ℝ} {score : V → α → ℝ}
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hw_nonneg : ∀ v : V, 0 ≤ w v)
    (hw_sum : Finset.univ.sum (fun v : V => w v) = 1)
    (hchange : ∀ a b : α,
      weightedScoreProfileMargin w score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    F τ M ρ x ≤ F τ (weightedScoreProfileMargin w score) ρ x := by
  have hMplus : IsNormalizedMarginMatrix (weightedScoreProfileMargin w score) :=
    weightedScoreProfileMargin_normalized score hw_nonneg hw_sum
  have hbound :
      ∀ i j : {z : α // z ≠ x},
        |nlhfCoordinateC (weightedScoreProfileMargin w score) x i.1 j.1| ≤
          (1 : ℝ) := by
    intro i j
    exact weightedScoreProfileMargin_coordinate_abs_le_one
      score hw_nonneg hw_sum x i.1 j.1
  exact nlhf_block_improvement_monotone_of_tau_ge_one_eighth_unit_bound_selected
    (hselect := hselect) (hselected := hselected) (hτge := hτge)
    (hM := hM) (hMplus := hMplus) (hρ := hρ)
    (hchange := hchange) (hBne := hBne)
    (hbound := hbound) (hδpos := hδpos)

/-- Large-temperature monotonicity bridge for actual finite weak-order
profiles, represented by score functions and the unweighted profile average. -/
theorem nlhf_scoreProfile_block_improvement_monotone_of_tau_ge_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    F τ M ρ x ≤ F τ (scoreProfileMargin score) ρ x := by
  have hMplus : IsNormalizedMarginMatrix (scoreProfileMargin score) :=
    scoreProfileMargin_normalized score
  have hbound :
      ∀ i j : {z : α // z ≠ x},
        |nlhfCoordinateC (scoreProfileMargin score) x i.1 j.1| ≤
          (1 : ℝ) := by
    intro i j
    exact scoreProfileMargin_coordinate_abs_le_one score x i.1 j.1
  exact nlhf_block_improvement_monotone_of_tau_ge_one_eighth_unit_bound
    (hselect := hselect) (hvar := hvar) (hτge := hτge)
    (hM := hM) (hMplus := hMplus) (hρ := hρ)
    (hchange := hchange) (hBne := hBne)
    (hbound := hbound) (hδpos := hδpos)

/-- Large-temperature monotonicity bridge for actual finite weak-order
profiles, stated with the selected endpoint-optimality interface. -/
theorem nlhf_scoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    F τ M ρ x ≤ F τ (scoreProfileMargin score) ρ x := by
  have hMplus : IsNormalizedMarginMatrix (scoreProfileMargin score) :=
    scoreProfileMargin_normalized score
  have hbound :
      ∀ i j : {z : α // z ≠ x},
        |nlhfCoordinateC (scoreProfileMargin score) x i.1 j.1| ≤
          (1 : ℝ) := by
    intro i j
    exact scoreProfileMargin_coordinate_abs_le_one score x i.1 j.1
  exact nlhf_block_improvement_monotone_of_tau_ge_one_eighth_unit_bound_selected
    (hselect := hselect) (hselected := hselected) (hτge := hτge)
    (hM := hM) (hMplus := hMplus) (hρ := hρ)
    (hchange := hchange) (hBne := hBne)
    (hbound := hbound) (hδpos := hδpos)

/-- Linear-order specialization of the finite-profile `1/8` bridge.  The
proof uses the weak-order theorem, since no-tie score profiles are a special
case of score-represented weak-order profiles. -/
theorem nlhf_linearScoreProfile_block_improvement_monotone_of_tau_ge_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (_hlinear : IsLinearScoreProfile score)
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    F τ M ρ x ≤ F τ (scoreProfileMargin score) ρ x := by
  exact nlhf_scoreProfile_block_improvement_monotone_of_tau_ge_one_eighth
    (hselect := hselect) (hvar := hvar) (hτge := hτge)
    (hM := hM) (hρ := hρ) (hchange := hchange)
    (hBne := hBne) (hδpos := hδpos)

/-- Linear-order specialization of the finite-profile `1/8` bridge, stated
with the selected endpoint-optimality interface. -/
theorem nlhf_linearScoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (_hlinear : IsLinearScoreProfile score)
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    F τ M ρ x ≤ F τ (scoreProfileMargin score) ρ x := by
  exact nlhf_scoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    (hselect := hselect) (hselected := hselected) (hτge := hτge)
    (hM := hM) (hρ := hρ) (hchange := hchange)
    (hBne := hBne) (hδpos := hδpos)

/-- One-pair monotonicity for NLHF at `τ ≥ 3/8`, derived from the checked
finite-comparison theorem plus the cited fixed-point and variational
characterizations. -/
theorem nlhf_pair_improvement_monotone_of_tau_ge_three_eighths
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x y : α}
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hτge : (3 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hyx : y ≠ x)
    (hδpos : 0 < δ)
    (hδle : δ ≤ 1 - M x y) :
    F τ M ρ x ≤ F τ (improvePairMargin M x y δ) ρ x := by
  classical
  let Mplus : α → α → ℝ := improvePairMargin M x y δ
  let B : Finset {z : α // z ≠ x} := {⟨y, hyx⟩}
  have hτpos : 0 < τ := by nlinarith
  have hxy : x ≠ y := hyx ∘ Eq.symm
  have hMplus : IsNormalizedMarginMatrix Mplus := by
    dsimp [Mplus]
    exact improvePairMargin_normalized hM hxy hδpos.le hδle
  have hfp : IsNLHFFixedPoint τ M ρ (F τ M ρ) :=
    hselect hτpos hM hρ
  have hfp' : IsNLHFFixedPoint τ Mplus ρ (F τ Mplus ρ) :=
    hselect hτpos hMplus hρ
  have hchange : ∀ a b : α,
      Mplus a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b := by
    intro a b
    dsimp [Mplus, B]
    simpa using
      improvePairMargin_change_eq_blockImprovementChange_singleton
        M δ hyx a b
  have hBne : B.Nonempty := by
    exact ⟨⟨y, hyx⟩, by simp [B]⟩
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hlamK : nlhfLambda τ * (3 : ℝ) ≤ 4 := by
    have hle := nlhfLambda_le_four_thirds_of_tau_ge_three_eighths hτge
    nlinarith
  have hbound :
      ∀ i j : {z : α // z ≠ x},
        |nlhfCoordinateC Mplus x i.1 j.1| ≤ (3 : ℝ) := by
    intro i j
    exact nlhfCoordinateC_abs_le_three hMplus x i.1 j.1
  have hvarOld :
      -(1 / nlhfLambda τ) * KL (F τ M ρ) ρ ≥
        marginValue M (F τ Mplus ρ) (F τ M ρ) -
          (1 / nlhfLambda τ) * KL (F τ Mplus ρ) ρ :=
    hvar hfp hfp'.2.2.1
  have hvarNew :
      -(1 / nlhfLambda τ) * KL (F τ Mplus ρ) ρ ≥
        marginValue Mplus (F τ M ρ) (F τ Mplus ρ) -
          (1 / nlhfLambda τ) * KL (F τ M ρ) ρ :=
    hvar hfp' hfp.2.2.1
  exact finiteComparison_from_fixed_points_arithmetic
    (hfp := hfp) (hfp' := hfp') (hlamdef := rfl)
    (hMplus_skew := hMplus.2.1) (hchange := hchange)
    (hBne := hBne) (hbound := hbound) (hlam := hlam)
    (hdelta := hδpos) (hlamK := hlamK)
    (hvarOld := hvarOld) (hvarNew := hvarNew)

/-- One-pair monotonicity for NLHF at `τ ≥ 3/8`, stated with the selected
endpoint-optimality interface. -/
theorem nlhf_pair_improvement_monotone_of_tau_ge_three_eighths_selected
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x y : α}
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (3 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hyx : y ≠ x)
    (hδpos : 0 < δ)
    (hδle : δ ≤ 1 - M x y) :
    F τ M ρ x ≤ F τ (improvePairMargin M x y δ) ρ x := by
  classical
  let Mplus : α → α → ℝ := improvePairMargin M x y δ
  let B : Finset {z : α // z ≠ x} := {⟨y, hyx⟩}
  have hτpos : 0 < τ := by nlinarith
  have hxy : x ≠ y := hyx ∘ Eq.symm
  have hMplus : IsNormalizedMarginMatrix Mplus := by
    dsimp [Mplus]
    exact improvePairMargin_normalized hM hxy hδpos.le hδle
  have hchange : ∀ a b : α,
      Mplus a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b := by
    intro a b
    dsimp [Mplus, B]
    simpa using
      improvePairMargin_change_eq_blockImprovementChange_singleton
        M δ hyx a b
  have hBne : B.Nonempty := by
    exact ⟨⟨y, hyx⟩, by simp [B]⟩
  have hlamK : nlhfLambda τ * (3 : ℝ) ≤ 4 := by
    have hle := nlhfLambda_le_four_thirds_of_tau_ge_three_eighths hτge
    nlinarith
  have hbound :
      ∀ i j : {z : α // z ≠ x},
        |nlhfCoordinateC Mplus x i.1 j.1| ≤ (3 : ℝ) := by
    intro i j
    exact nlhfCoordinateC_abs_le_three hMplus x i.1 j.1
  exact nlhf_block_improvement_monotone_of_coordinate_bound_selected
    (hselect := hselect) (hselected := hselected) (hτpos := hτpos)
    (hM := hM) (hMplus := hMplus) (hρ := hρ)
    (hchange := hchange) (hBne := hBne) (hbound := hbound)
    (hδpos := hδpos) (hlamK := hlamK)

/-- Full matrix-level NLHF monotonicity for `τ ≥ 3/8`, conditional only on
the cited fixed-point selection and variational characterization. -/
theorem nlhf_monotone_of_tau_ge_three_eighths
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ : ℝ}
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hτge : (3 : ℝ) / 8 ≤ τ) :
    SatisfiesProbabilisticMonotonicity (F τ) := by
  refine monotonicity_from_pair_improvements ?_
  intro M ρ x y δ hM hρ hyx hδpos hδle
  exact nlhf_pair_improvement_monotone_of_tau_ge_three_eighths
    (F := F) hselect hvar hτge hM hρ hyx hδpos hδle

/-- Full matrix-level NLHF monotonicity for `τ ≥ 3/8`, stated with the
selected endpoint-optimality interface. -/
theorem nlhf_monotone_of_tau_ge_three_eighths_selected
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α} {τ : ℝ}
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (3 : ℝ) / 8 ≤ τ) :
    SatisfiesProbabilisticMonotonicity (F τ) := by
  refine monotonicity_from_pair_improvements ?_
  intro M ρ x y δ hM hρ hyx hδpos hδle
  exact nlhf_pair_improvement_monotone_of_tau_ge_three_eighths_selected
    (F := F) hselect hselected hτge hM hρ hyx hδpos hδle

/-- The large-temperature half of Theorem `NLHFmono`, in the formal
interface where the standard NLHF existence/uniqueness and variational
theorems are cited inputs. -/
theorem nlhf_largeTau_monotone_from_variational
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α}
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α)) :
    NLHFMonotoneForLargeTau F := by
  intro τ hτge
  exact nlhf_monotone_of_tau_ge_three_eighths hselect hvar hτge

/-- The large-temperature half using the usual cited package: finite-instance
existence, uniqueness/selectability, and the variational characterization. -/
theorem nlhf_largeTau_monotone_from_exists_unique_and_variational
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α}
    (hexists : NLHFFixedPointExists (α := α))
    (hunique : IsTheNLHF F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α)) :
    NLHFMonotoneForLargeTau F :=
  nlhf_largeTau_monotone_from_variational
    (fixedPointSelection_of_exists_and_unique hexists hunique) hvar

/-- The large-temperature half of Theorem `NLHFmono`, stated with the
selected endpoint-optimality interface. -/
theorem nlhf_largeTau_monotone_from_selected_NLHF
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α}
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F) :
    NLHFMonotoneForLargeTau F := by
  intro τ hτge
  exact nlhf_monotone_of_tau_ge_three_eighths_selected
    hselect hselected hτge

/-- The large-temperature half of Theorem `NLHFmono`, proved directly from
the selected fixed-point equation.  This avoids a separate variational
characterization hypothesis. -/
theorem nlhf_largeTau_monotone_from_fixedPointSelection
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α}
    (hselect : IsNLHFFixedPointSelection F) :
    NLHFMonotoneForLargeTau F :=
  nlhf_largeTau_monotone_from_selected_NLHF hselect
    (selectedVariationalInequality_of_fixedPointSelection hselect)

/-- The large-temperature half using only the cited finite-instance
existence and uniqueness/selectability package. -/
theorem nlhf_largeTau_monotone_from_exists_unique
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : ℝ → MatrixRule α}
    (hexists : NLHFFixedPointExists (α := α))
    (hunique : IsTheNLHF F) :
    NLHFMonotoneForLargeTau F :=
  nlhf_largeTau_monotone_from_fixedPointSelection
    (fixedPointSelection_of_exists_and_unique hexists hunique)

/-- `3/8` iff assembly from fixed-point selection, the variational inequality,
and a finite-secant strict-drop certificate. -/
theorem NLHFmono_from_variational_and_lowTemp_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : ℝ → MatrixRule α)
    (hselect : IsNLHFFixedPointSelection F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hlow : HasNLHFLowTempSecantDropCertificate F)
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity (F τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_named_parts F
    (nlhf_largeTau_monotone_from_variational hselect hvar)
    (NLHFViolatesForSmallTau_of_lowTempSecantDropCertificate hlow) hτ

/-- `3/8` iff assembly from finite-instance existence,
uniqueness/selectability, the variational
characterization, and the finite-secant low-temperature strict-drop
certificate. -/
theorem NLHFmono_from_exists_unique_variational_and_lowTemp_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : ℝ → MatrixRule α)
    (hexists : NLHFFixedPointExists (α := α))
    (hunique : IsTheNLHF F)
    (hvar : SatisfiesNLHFVariationalInequality (α := α))
    (hlow : HasNLHFLowTempSecantDropCertificate F)
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity (F τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_named_parts F
    (nlhf_largeTau_monotone_from_exists_unique_and_variational
      hexists hunique hvar)
    (NLHFViolatesForSmallTau_of_lowTempSecantDropCertificate hlow) hτ

/-- `3/8` iff assembly with the large-temperature half proved directly
from the selected fixed-point equation. -/
theorem NLHFmono_from_fixedPointSelection_and_lowTemp_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : ℝ → MatrixRule α)
    (hselect : IsNLHFFixedPointSelection F)
    (hlow : HasNLHFLowTempSecantDropCertificate F)
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity (F τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_named_parts F
    (nlhf_largeTau_monotone_from_fixedPointSelection hselect)
    (NLHFViolatesForSmallTau_of_lowTempSecantDropCertificate hlow) hτ

/-- `3/8` iff assembly from NLHF existence and uniqueness/selectability, with
the variational inequality derived
inside Lean from the selected fixed-point equation. -/
theorem NLHFmono_from_exists_unique_and_lowTemp_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : ℝ → MatrixRule α)
    (hexists : NLHFFixedPointExists (α := α))
    (hunique : IsTheNLHF F)
    (hlow : HasNLHFLowTempSecantDropCertificate F)
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity (F τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_named_parts F
    (nlhf_largeTau_monotone_from_exists_unique hexists hunique)
    (NLHFViolatesForSmallTau_of_lowTempSecantDropCertificate hlow) hτ

/-- `3/8` iff assembly with the large-temperature half stated using
the selected endpoint-optimality interface. -/
theorem NLHFmono_from_selected_NLHF_and_lowTemp_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : ℝ → MatrixRule α)
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hlow : HasNLHFLowTempSecantDropCertificate F)
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity (F τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_named_parts F
    (nlhf_largeTau_monotone_from_selected_NLHF hselect hselected)
    (NLHFViolatesForSmallTau_of_lowTempSecantDropCertificate hlow) hτ

end PaperFormalization
