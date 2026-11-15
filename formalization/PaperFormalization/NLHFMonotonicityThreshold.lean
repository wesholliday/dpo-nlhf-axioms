import PaperFormalization.NLHFMonotonicity
import PaperFormalization.Multiplicative
import PaperFormalization.NLHFBasic

open scoped BigOperators Topology

namespace PaperFormalization

lemma nlhfLambda_le_four_thirds_of_tau_ge_three_eighths
    {τ : ℝ} (hτ : (3 : ℝ) / 8 ≤ τ) :
    nlhfLambda τ ≤ (4 : ℝ) / 3 := by
  have hτpos : 0 < τ := by nlinarith
  unfold nlhfLambda
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * τ)]
  nlinarith

lemma four_thirds_lt_nlhfLambda_of_tau_lt_three_eighths
    {τ : ℝ} (hτpos : 0 < τ) (hτ : τ < (3 : ℝ) / 8) :
    (4 : ℝ) / 3 < nlhfLambda τ := by
  unfold nlhfLambda
  rw [lt_div_iff₀' (by positivity : (0 : ℝ) < 2 * τ)]
  nlinarith

lemma four_lt_nlhfLambda_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτ : τ < (1 : ℝ) / 8) :
    (4 : ℝ) < nlhfLambda τ := by
  unfold nlhfLambda
  rw [lt_div_iff₀' (by positivity : (0 : ℝ) < 2 * τ)]
  nlinarith

lemma nlhfLambda_le_four_of_tau_ge_one_eighth
    {τ : ℝ} (hτ : (1 : ℝ) / 8 ≤ τ) :
    nlhfLambda τ ≤ (4 : ℝ) := by
  have hτpos : 0 < τ := by nlinarith
  unfold nlhfLambda
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * τ)]
  nlinarith

/-- The logarithmic ratio form of the NLHF fixed-point equation. -/
lemma nlhfFixedPoint_log_ratio
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ π) (i x : α) :
    Real.log (π i / π x) =
      Real.log (ρ i / ρ x) +
        (expectedMargin M π i - expectedMargin M π x) / (2 * τ) := by
  classical
  let Z : ℝ := Finset.univ.sum
    (fun z => ρ z * Real.exp (expectedMargin M π z / (2 * τ)))
  have hρi : 0 < ρ i := hfp.2.1.1 i
  have hρx : 0 < ρ x := hfp.2.1.1 x
  have hZi : π i =
      ρ i * Real.exp (expectedMargin M π i / (2 * τ)) / Z := by
    simpa [Z] using hfp.2.2.2 i
  have hZx : π x =
      ρ x * Real.exp (expectedMargin M π x / (2 * τ)) / Z := by
    simpa [Z] using hfp.2.2.2 x
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact Finset.sum_pos
      (fun z _hz => mul_pos (hfp.2.1.1 z) (Real.exp_pos _))
      ⟨i, by simp⟩
  have hratio :
      π i / π x =
        (ρ i / ρ x) *
          Real.exp
            ((expectedMargin M π i - expectedMargin M π x) /
              (2 * τ)) := by
    rw [hZi, hZx]
    field_simp
      [ne_of_gt hZpos, ne_of_gt hρx,
        ne_of_gt (Real.exp_pos (expectedMargin M π x / (2 * τ)))]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hratio]
  rw [Real.log_mul (ne_of_gt (div_pos hρi hρx))
    (ne_of_gt (Real.exp_pos _))]
  rw [Real.log_exp]

/-- Subtracting two logarithmic ratio fixed-point equations with the same
reference lottery cancels the reference term. -/
lemma nlhfFixedPoint_log_ratio_sub
    {α : Type*} [Fintype α]
    {τ : ℝ} {M M' : α → α → ℝ} {ρ π π' : α → ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ π)
    (hfp' : IsNLHFFixedPoint τ M' ρ π') (i x : α) :
    Real.log (π' i / π' x) - Real.log (π i / π x) =
      ((expectedMargin M' π' i - expectedMargin M' π' x) -
        (expectedMargin M π i - expectedMargin M π x)) / (2 * τ) := by
  have hnew := nlhfFixedPoint_log_ratio hfp' i x
  have hold := nlhfFixedPoint_log_ratio hfp i x
  rw [hnew, hold]
  ring

/-- Elementary logarithm algebra converting a difference of two odds ratios
into the endpoint-log form used in the finite proof. -/
lemma log_ratio_sub_eq_endpoint_logs
    {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    Real.log (b / d) - Real.log (a / c) =
      Real.log (b / a) + Real.log (c / d) := by
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt hd),
    Real.log_div (ne_of_gt ha) (ne_of_gt hc),
    Real.log_div (ne_of_gt hb) (ne_of_gt ha),
    Real.log_div (ne_of_gt hc) (ne_of_gt hd)]
  ring

/-- The endpoint-log equation obtained by comparing two NLHF fixed points for
the same reference lottery. -/
lemma nlhfFixedPoint_endpoint_log_difference
    {α : Type*} [Fintype α]
    {τ : ℝ} {M M' : α → α → ℝ} {ρ π π' : α → ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ π)
    (hfp' : IsNLHFFixedPoint τ M' ρ π') (i x : α) :
    Real.log (π' i / π i) + Real.log (π x / π' x) =
      ((expectedMargin M' π' i - expectedMargin M' π' x) -
        (expectedMargin M π i - expectedMargin M π x)) / (2 * τ) := by
  have hsub := nlhfFixedPoint_log_ratio_sub hfp hfp' i x
  have hlog := log_ratio_sub_eq_endpoint_logs
    (hfp.2.2.1.1 i) (hfp'.2.2.1.1 i)
    (hfp.2.2.1.1 x) (hfp'.2.2.1.1 x)
  rw [hlog] at hsub
  exact hsub

/-- The coordinate coefficient
`c_{ij}=M_{ij}+M_{xi}-M_{xj}` used in the elementary monotonicity proof. -/
noncomputable def nlhfCoordinateC {α : Type*}
    (M : α → α → ℝ) (x i j : α) : ℝ :=
  M i j + M x i - M x j

lemma nlhfCoordinateC_skew
    {α : Type*} {M : α → α → ℝ} (hM : IsNormalizedMarginMatrix M)
    (x i j : α) :
    nlhfCoordinateC M x j i = -nlhfCoordinateC M x i j := by
  unfold nlhfCoordinateC
  rw [hM.2.1 i j]
  ring

lemma nlhfCoordinateC_abs_le_three
    {α : Type*} {M : α → α → ℝ} (hM : IsNormalizedMarginMatrix M)
    (x i j : α) :
    |nlhfCoordinateC M x i j| ≤ (3 : ℝ) := by
  unfold nlhfCoordinateC
  have htri :
      |M i j + M x i - M x j| ≤ |M i j| + |M x i| + |M x j| := by
    calc
      |M i j + M x i - M x j|
          = |(M i j + M x i) + (-M x j)| := by ring_nf
      _ ≤ |M i j + M x i| + |-M x j| := abs_add_le _ _
      _ = |M i j + M x i| + |M x j| := by simp
      _ ≤ (|M i j| + |M x i|) + |M x j| := by
        gcongr
        exact abs_add_le (M i j) (M x i)
      _ = |M i j| + |M x i| + |M x j| := by ring
  have hij := hM.2.2 i j
  have hxi := hM.2.2 x i
  have hxj := hM.2.2 x j
  linarith

/-- Pairwise margin contribution of one complete strict weak order represented
by real-valued scores.  It is `1` for strictly above, `0` for tied, and `-1`
for strictly below. -/
noncomputable def scoreMarginSignReal (a b : ℝ) : ℝ :=
  if a > b then 1 else if a = b then 0 else -1

noncomputable def scoreMarginSign {α : Type*}
    (score : α → ℝ) (i j : α) : ℝ :=
  scoreMarginSignReal (score i) (score j)

lemma scoreMarginSignReal_le_one (a b : ℝ) :
    scoreMarginSignReal a b ≤ (1 : ℝ) := by
  unfold scoreMarginSignReal
  split_ifs <;> norm_num

lemma neg_one_le_scoreMarginSignReal (a b : ℝ) :
    -(1 : ℝ) ≤ scoreMarginSignReal a b := by
  unfold scoreMarginSignReal
  split_ifs <;> norm_num

lemma scoreMarginSignReal_of_gt {a b : ℝ} (h : b < a) :
    scoreMarginSignReal a b = (1 : ℝ) := by
  unfold scoreMarginSignReal
  simp [h]

lemma scoreMarginSignReal_of_lt {a b : ℝ} (h : a < b) :
    scoreMarginSignReal a b = -(1 : ℝ) := by
  unfold scoreMarginSignReal
  have hnot : ¬ b < a := by linarith
  have hne : a ≠ b := by linarith
  simp [gt_iff_lt, hnot, hne]

lemma scoreMarginSignReal_of_eq {a b : ℝ} (h : a = b) :
    scoreMarginSignReal a b = 0 := by
  subst b
  unfold scoreMarginSignReal
  simp

lemma scoreMarginSignReal_antisymm (a b : ℝ) :
    scoreMarginSignReal a b = -scoreMarginSignReal b a := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · rw [scoreMarginSignReal_of_lt hlt, scoreMarginSignReal_of_gt hlt]
  · rw [scoreMarginSignReal_of_eq heq, scoreMarginSignReal_of_eq heq.symm]
    norm_num
  · rw [scoreMarginSignReal_of_gt hgt, scoreMarginSignReal_of_lt hgt]
    norm_num

lemma scoreMarginSignReal_abs_le_one (a b : ℝ) :
    |scoreMarginSignReal a b| ≤ (1 : ℝ) :=
  abs_le.mpr
    ⟨neg_one_le_scoreMarginSignReal a b, scoreMarginSignReal_le_one a b⟩

lemma scoreMarginSign_coordinate_le_one
    (sx si sj : ℝ) :
    scoreMarginSignReal si sj +
      scoreMarginSignReal sx si -
      scoreMarginSignReal sx sj ≤ (1 : ℝ) := by
  by_cases hxi : sx < si
  · have hxilt : scoreMarginSignReal sx si = -(1 : ℝ) :=
      scoreMarginSignReal_of_lt hxi
    have hsij : scoreMarginSignReal si sj ≤ (1 : ℝ) :=
      scoreMarginSignReal_le_one si sj
    have hxj : -(scoreMarginSignReal sx sj) ≤ (1 : ℝ) := by
      have h := neg_one_le_scoreMarginSignReal sx sj
      linarith
    linarith
  · have hsxige : si ≤ sx := le_of_not_gt hxi
    rcases lt_trichotomy si sj with hsilt | heq | hsjlt
    · have hsij : scoreMarginSignReal si sj = -(1 : ℝ) :=
        scoreMarginSignReal_of_lt hsilt
      have hxi_le : scoreMarginSignReal sx si ≤ (1 : ℝ) :=
        scoreMarginSignReal_le_one sx si
      have hxj : -(scoreMarginSignReal sx sj) ≤ (1 : ℝ) := by
        have h := neg_one_le_scoreMarginSignReal sx sj
        linarith
      linarith
    · subst sj
      rw [scoreMarginSignReal_of_eq rfl]
      ring_nf
      norm_num
    · have hsij : scoreMarginSignReal si sj = (1 : ℝ) :=
        scoreMarginSignReal_of_gt hsjlt
      have hsjx : sj < sx := lt_of_lt_of_le hsjlt hsxige
      have hxj : scoreMarginSignReal sx sj = (1 : ℝ) :=
        scoreMarginSignReal_of_gt hsjx
      have hxi_le : scoreMarginSignReal sx si ≤ (1 : ℝ) :=
        scoreMarginSignReal_le_one sx si
      linarith

/-- Voter-level coordinate bound for complete strict weak orders. -/
lemma scoreMarginSign_coordinate_abs_le_one
    (sx si sj : ℝ) :
    |scoreMarginSignReal si sj +
      scoreMarginSignReal sx si -
      scoreMarginSignReal sx sj| ≤ (1 : ℝ) := by
  have hle := scoreMarginSign_coordinate_le_one sx si sj
  have hswap := scoreMarginSign_coordinate_le_one sx sj si
  have hge : -(1 : ℝ) ≤
      scoreMarginSignReal si sj +
        scoreMarginSignReal sx si -
        scoreMarginSignReal sx sj := by
    rw [scoreMarginSignReal_antisymm sj si] at hswap
    linarith
  exact abs_le.mpr ⟨hge, hle⟩

/-- Normalized margin matrix obtained by averaging score-represented complete
strict weak orders over voters. -/
noncomputable def scoreProfileMargin
    {V α : Type*} [Fintype V]
    (score : V → α → ℝ) (i j : α) : ℝ :=
  (Finset.univ.sum (fun v : V => scoreMarginSign (score v) i j)) /
    (Fintype.card V : ℝ)

/-- A score-represented profile is linear when each voter's score function has
no ties.  The weak-order arguments below do not need this stronger hypothesis,
but naming it makes the linear-order specialization explicit. -/
def IsLinearScoreProfile {V α : Type*} (score : V → α → ℝ) : Prop :=
  ∀ v : V, Function.Injective (score v)

lemma scoreProfileMargin_abs_le_one
    {V α : Type*} [Fintype V] [Nonempty V]
    (score : V → α → ℝ) (i j : α) :
    |scoreProfileMargin score i j| ≤ (1 : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hsum_abs :
      |Finset.univ.sum (fun v : V => scoreMarginSign (score v) i j)| ≤
        (Fintype.card V : ℝ) := by
    calc
      |Finset.univ.sum (fun v : V => scoreMarginSign (score v) i j)|
          ≤ Finset.univ.sum (fun v : V => |scoreMarginSign (score v) i j|) :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ Finset.univ.sum (fun _v : V => (1 : ℝ)) := by
            exact Finset.sum_le_sum
              (fun v _hv =>
                by
                  simpa [scoreMarginSign] using
                    scoreMarginSignReal_abs_le_one (score v i) (score v j))
      _ = (Fintype.card V : ℝ) := by simp
  unfold scoreProfileMargin
  rw [abs_div, abs_of_pos hn_pos]
  rw [div_le_iff₀ hn_pos]
  simpa [n] using hsum_abs

lemma scoreProfileMargin_normalized
    {V α : Type*} [Fintype V] [Nonempty V]
    (score : V → α → ℝ) :
    IsNormalizedMarginMatrix (scoreProfileMargin score) := by
  classical
  refine ⟨?diag, ?skew, ?bound⟩
  · intro x
    unfold scoreProfileMargin scoreMarginSign
    simp [scoreMarginSignReal_of_eq rfl]
  · intro x y
    unfold scoreProfileMargin scoreMarginSign
    calc
      (Finset.univ.sum (fun v : V => scoreMarginSignReal (score v y) (score v x))) /
          (Fintype.card V : ℝ)
          =
        (Finset.univ.sum
          (fun v : V => -scoreMarginSignReal (score v x) (score v y))) /
          (Fintype.card V : ℝ) := by
            refine congrArg (fun r : ℝ => r / (Fintype.card V : ℝ)) ?_
            refine Finset.sum_congr rfl ?_
            intro v _hv
            exact scoreMarginSignReal_antisymm (score v y) (score v x)
      _ =
        -((Finset.univ.sum
          (fun v : V => scoreMarginSignReal (score v x) (score v y))) /
          (Fintype.card V : ℝ)) := by
            rw [Finset.sum_neg_distrib]
            ring
  · intro x y
    exact scoreProfileMargin_abs_le_one score x y

/-- Averaging the voter-level bound gives the `K = 1` coordinate bound for
score-represented complete strict weak-order profiles. -/
lemma scoreProfileMargin_coordinate_abs_le_one
    {V α : Type*} [Fintype V] [Nonempty V]
    (score : V → α → ℝ) (x i j : α) :
    |scoreProfileMargin score i j +
      scoreProfileMargin score x i -
      scoreProfileMargin score x j| ≤ (1 : ℝ) := by
  classical
  let n : ℝ := Fintype.card V
  let term : V → ℝ := fun v =>
    scoreMarginSign (score v) i j +
      scoreMarginSign (score v) x i -
      scoreMarginSign (score v) x j
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hnum_eq :
      scoreProfileMargin score i j +
        scoreProfileMargin score x i -
        scoreProfileMargin score x j =
      (Finset.univ.sum (fun v : V => term v)) / n := by
    unfold scoreProfileMargin term scoreMarginSign
    dsimp [n]
    have hn_ne : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
    field_simp [hn_ne]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hterm :
      ∀ v : V, |term v| ≤ (1 : ℝ) := by
    intro v
    simpa [term, scoreMarginSign] using
      scoreMarginSign_coordinate_abs_le_one
        (score v x) (score v i) (score v j)
  have hsum_abs :
      |Finset.univ.sum (fun v : V => term v)| ≤
        (Fintype.card V : ℝ) := by
    calc
      |Finset.univ.sum (fun v : V => term v)|
          ≤ Finset.univ.sum (fun v : V => |term v|) :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ Finset.univ.sum (fun _v : V => (1 : ℝ)) := by
            exact Finset.sum_le_sum (fun v _hv => hterm v)
      _ = (Fintype.card V : ℝ) := by simp
  rw [hnum_eq]
  rw [abs_div, abs_of_pos hn_pos]
  rw [div_le_iff₀ hn_pos]
  simpa [n] using hsum_abs

/-- Weighted normalized margin matrix obtained by averaging
score-represented complete strict weak orders with real weights summing to
one.  This is the convenient formal model for rational weighted profiles before
clearing denominators. -/
noncomputable def weightedScoreProfileMargin
    {V α : Type*} [Fintype V]
    (w : V → ℝ) (score : V → α → ℝ) (i j : α) : ℝ :=
  Finset.univ.sum (fun v : V => w v * scoreMarginSign (score v) i j)

/-- Denominator clearing for weighted score profiles.  If the weight of each
ballot type is the fraction of an expanded finite electorate assigned to that
type, then the weighted margin is exactly the ordinary unweighted profile
margin of the expanded electorate. -/
lemma weightedScoreProfileMargin_eq_scoreProfileMargin_of_fiber_weights
    {V W α : Type*} [Fintype V] [DecidableEq V] [Fintype W] [Nonempty W]
    (assign : W → V) (score : V → α → ℝ) (w : V → ℝ)
    (hw : ∀ v : V,
      w v =
        ((Finset.univ.filter (fun u : W => assign u = v)).card : ℝ) /
          (Fintype.card W : ℝ)) :
    weightedScoreProfileMargin w score =
      scoreProfileMargin (fun u : W => score (assign u)) := by
  classical
  funext i j
  let n : ℝ := Fintype.card W
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  let term : W → ℝ := fun u =>
    scoreMarginSign (score (assign u)) i j
  let fiber : V → Finset W := fun v =>
    Finset.univ.filter (fun u : W => assign u = v)
  have hinner :
      ∀ v : V,
        (fiber v).sum term =
          ((fiber v).card : ℝ) * scoreMarginSign (score v) i j := by
    intro v
    calc
      (fiber v).sum term =
          (fiber v).sum (fun _u : W => scoreMarginSign (score v) i j) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            have huv : assign u = v := by
              simpa [fiber] using hu
            simp [term, huv]
      _ = ((fiber v).card : ℝ) * scoreMarginSign (score v) i j := by
            simp
  have hfiberwise :
      Finset.univ.sum (fun v : V => (fiber v).sum term) =
        Finset.univ.sum term := by
    simpa [fiber, term] using
      (Finset.sum_fiberwise
        (s := (Finset.univ : Finset W))
        (g := assign)
        (f := term))
  calc
    weightedScoreProfileMargin w score i j =
        Finset.univ.sum (fun v : V =>
          (((fiber v).card : ℝ) / n) *
            scoreMarginSign (score v) i j) := by
          unfold weightedScoreProfileMargin
          refine Finset.sum_congr rfl ?_
          intro v _hv
          rw [hw v]
    _ =
        (Finset.univ.sum (fun v : V =>
          ((fiber v).card : ℝ) * scoreMarginSign (score v) i j)) / n := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro v _hv
          ring
    _ =
        (Finset.univ.sum (fun v : V => (fiber v).sum term)) / n := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro v _hv
          exact (hinner v).symm
    _ = (Finset.univ.sum term) / n := by
          rw [hfiberwise]
    _ = scoreProfileMargin (fun u : W => score (assign u)) i j := by
          rfl

lemma weightedScoreProfileMargin_abs_le_one
    {V α : Type*} [Fintype V]
    {w : V → ℝ} (score : V → α → ℝ)
    (hw_nonneg : ∀ v : V, 0 ≤ w v)
    (hw_sum : Finset.univ.sum (fun v : V => w v) = 1)
    (i j : α) :
    |weightedScoreProfileMargin w score i j| ≤ (1 : ℝ) := by
  classical
  calc
    |weightedScoreProfileMargin w score i j|
        ≤ Finset.univ.sum
            (fun v : V => |w v * scoreMarginSign (score v) i j|) := by
          unfold weightedScoreProfileMargin
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.univ.sum (fun v : V => w v) := by
          refine Finset.sum_le_sum ?_
          intro v _hv
          rw [abs_mul, abs_of_nonneg (hw_nonneg v)]
          exact mul_le_of_le_one_right (hw_nonneg v)
            (by
              simpa [scoreMarginSign] using
                scoreMarginSignReal_abs_le_one (score v i) (score v j))
    _ = 1 := hw_sum

lemma weightedScoreProfileMargin_normalized
    {V α : Type*} [Fintype V]
    {w : V → ℝ} (score : V → α → ℝ)
    (hw_nonneg : ∀ v : V, 0 ≤ w v)
    (hw_sum : Finset.univ.sum (fun v : V => w v) = 1) :
    IsNormalizedMarginMatrix (weightedScoreProfileMargin w score) := by
  classical
  refine ⟨?diag, ?skew, ?bound⟩
  · intro x
    unfold weightedScoreProfileMargin scoreMarginSign
    simp [scoreMarginSignReal_of_eq rfl]
  · intro x y
    unfold weightedScoreProfileMargin scoreMarginSign
    calc
      Finset.univ.sum
          (fun v : V => w v * scoreMarginSignReal (score v y) (score v x))
          =
        Finset.univ.sum
          (fun v : V => w v * (-scoreMarginSignReal (score v x) (score v y))) := by
            refine Finset.sum_congr rfl ?_
            intro v _hv
            rw [scoreMarginSignReal_antisymm (score v y) (score v x)]
      _ =
        -Finset.univ.sum
          (fun v : V => w v * scoreMarginSignReal (score v x) (score v y)) := by
            simp [Finset.sum_neg_distrib]
  · intro x y
    exact weightedScoreProfileMargin_abs_le_one score hw_nonneg hw_sum x y

lemma weightedScoreProfileMargin_coordinate_abs_le_one
    {V α : Type*} [Fintype V]
    {w : V → ℝ} (score : V → α → ℝ)
    (hw_nonneg : ∀ v : V, 0 ≤ w v)
    (hw_sum : Finset.univ.sum (fun v : V => w v) = 1)
    (x i j : α) :
    |weightedScoreProfileMargin w score i j +
      weightedScoreProfileMargin w score x i -
      weightedScoreProfileMargin w score x j| ≤ (1 : ℝ) := by
  classical
  let term : V → ℝ := fun v =>
    scoreMarginSign (score v) i j +
      scoreMarginSign (score v) x i -
      scoreMarginSign (score v) x j
  have hnum_eq :
      weightedScoreProfileMargin w score i j +
        weightedScoreProfileMargin w score x i -
        weightedScoreProfileMargin w score x j =
      Finset.univ.sum (fun v : V => w v * term v) := by
    unfold weightedScoreProfileMargin term scoreMarginSign
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro v _hv
    ring
  have hterm :
      ∀ v : V, |term v| ≤ (1 : ℝ) := by
    intro v
    simpa [term, scoreMarginSign] using
      scoreMarginSign_coordinate_abs_le_one
        (score v x) (score v i) (score v j)
  calc
    |weightedScoreProfileMargin w score i j +
      weightedScoreProfileMargin w score x i -
      weightedScoreProfileMargin w score x j|
        =
      |Finset.univ.sum (fun v : V => w v * term v)| := by
        rw [hnum_eq]
    _ ≤ Finset.univ.sum (fun v : V => |w v * term v|) :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.univ.sum (fun v : V => w v) := by
          refine Finset.sum_le_sum ?_
          intro v _hv
          rw [abs_mul, abs_of_nonneg (hw_nonneg v)]
          exact mul_le_of_le_one_right (hw_nonneg v) (hterm v)
    _ = 1 := hw_sum

lemma coordinateCz_le_of_abs_sum_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    {c : α → α → ℝ} {z : α → ℝ} {K : ℝ} {y : α}
    (hK : 0 ≤ K)
    (hdiag : c y y = 0)
    (hbound : ∀ j : α, |c y j| ≤ K)
    (habs :
      (Finset.univ.erase y).sum (fun j => |z j|) ≤ (1 : ℝ) / 4) :
    Finset.univ.sum (fun j => c y j * z j) ≤ K / 4 := by
  classical
  have hsum_eq :
      Finset.univ.sum (fun j => c y j * z j) =
        (Finset.univ.erase y).sum (fun j => c y j * z j) := by
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j => c y j * z j) (by simp : y ∈ (Finset.univ : Finset α))]
    simp [hdiag]
  calc
    Finset.univ.sum (fun j => c y j * z j)
        = (Finset.univ.erase y).sum (fun j => c y j * z j) := hsum_eq
    _ ≤ |(Finset.univ.erase y).sum (fun j => c y j * z j)| := le_abs_self _
    _ ≤ (Finset.univ.erase y).sum (fun j => |c y j * z j|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.univ.erase y).sum (fun j => K * |z j|) := by
      refine Finset.sum_le_sum ?_
      intro j _hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hbound j) (abs_nonneg (z j))
    _ = K * (Finset.univ.erase y).sum (fun j => |z j|) := by
      rw [Finset.mul_sum]
    _ ≤ K * ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left habs hK
    _ = K / 4 := by ring

lemma coordinateResponse_nonneg_of_cz_bound
    {lam K cyz g : ℝ}
    (hlam : 0 ≤ lam)
    (hlamK : lam * K ≤ 4)
    (hcyz : cyz ≤ K / 4)
    (hg : g = 1 - lam * cyz) :
    0 ≤ g := by
  have hmul : lam * cyz ≤ lam * (K / 4) :=
    mul_le_mul_of_nonneg_left hcyz hlam
  have hlamK' : lam * (K / 4) ≤ 1 := by
    nlinarith
  nlinarith

/-- Scalar part of the Cauchy/energy estimate in the elementary proof.

Once Cauchy's inequality and the energy identity give
`S^2 ≤ (1 - pX) * (T - T^2 / pX)`, the elementary one-variable bound below
implies `S ≤ 1/4`. -/
lemma absSumBound_of_sq_le_energyBound
    {S pX T : ℝ}
    (hS0 : 0 ≤ S)
    (hpXpos : 0 < pX)
    (hpXle : pX ≤ 1)
    (hSsq : S ^ 2 ≤ (1 - pX) * (T - T ^ 2 / pX)) :
    S ≤ (1 : ℝ) / 4 := by
  have hpX_nonneg : 0 ≤ pX := hpXpos.le
  have hone_minus_nonneg : 0 ≤ 1 - pX := by linarith
  have hTquad : T - T ^ 2 / pX ≤ pX / 4 := by
    have hsq : 0 ≤ (pX - 2 * T) ^ 2 := sq_nonneg _
    rw [le_div_iff₀' (by positivity : (0 : ℝ) < 4)]
    field_simp [hpXpos.ne']
    nlinarith
  have henergy_le_quarter :
      (1 - pX) * (T - T ^ 2 / pX) ≤ (1 - pX) * (pX / 4) :=
    mul_le_mul_of_nonneg_left hTquad hone_minus_nonneg
  have hpxprod : (1 - pX) * (pX / 4) ≤ (1 : ℝ) / 16 := by
    have hsq : 0 ≤ (2 * pX - 1) ^ 2 := sq_nonneg _
    nlinarith
  have hSsq_le : S ^ 2 ≤ ((1 : ℝ) / 4) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ hS0 (by norm_num : (0 : ℝ) ≤ 1 / 4)).mp hSsq_le

/-- The final coordinate-algebra step used in the finite comparison proof.

In the paper, the Cauchy/energy argument proves the hypothesis `habs`.  This
lemma then verifies the remaining finite-sum response argument: the auxiliary
solution gives `g ≥ 0`, hence the relevant signed finite sum `U` is
nonpositive. -/
theorem coordinateEstimate_from_absSumBound
    {α : Type*} [Fintype α] [DecidableEq α]
    {c : α → α → ℝ} {z : α → ℝ} {K lam pX pY U g : ℝ} {y : α}
    (hK : 0 ≤ K)
    (hpX : 0 < pX)
    (hpY : 0 < pY)
    (hlam : 0 < lam)
    (hlamK : lam * K ≤ 4)
    (hdiag : c y y = 0)
    (hbound : ∀ j : α, |c y j| ≤ K)
    (habs :
      (Finset.univ.erase y).sum (fun j => |z j|) ≤ (1 : ℝ) / 4)
    (hg :
      g = 1 - lam * Finset.univ.sum (fun j => c y j * z j))
    (hU : U = -lam * (pX * pY * g)) :
    U ≤ 0 := by
  classical
  have hcyz :
      Finset.univ.sum (fun j => c y j * z j) ≤ K / 4 :=
    coordinateCz_le_of_abs_sum_bound hK hdiag hbound habs
  have hg_nonneg : 0 ≤ g :=
    coordinateResponse_nonneg_of_cz_bound hlam.le hlamK hcyz hg
  have hprod : 0 ≤ pX * pY * g := by positivity
  rw [hU]
  nlinarith

/-- Version of `coordinateEstimate_from_absSumBound` where the supplied input is
the squared Cauchy/energy bound, rather than the final absolute-sum bound. -/
theorem coordinateEstimate_from_sqEnergyBound
    {α : Type*} [Fintype α] [DecidableEq α]
    {c : α → α → ℝ} {z : α → ℝ} {K lam pX pY T U g : ℝ} {y : α}
    (hK : 0 ≤ K)
    (hpX : 0 < pX)
    (hpXle : pX ≤ 1)
    (hpY : 0 < pY)
    (hlam : 0 < lam)
    (hlamK : lam * K ≤ 4)
    (hdiag : c y y = 0)
    (hbound : ∀ j : α, |c y j| ≤ K)
    (hsq :
      ((Finset.univ.erase y).sum (fun j => |z j|)) ^ 2 ≤
        (1 - pX) * (T - T ^ 2 / pX))
    (hg :
      g = 1 - lam * Finset.univ.sum (fun j => c y j * z j))
    (hU : U = -lam * (pX * pY * g)) :
    U ≤ 0 := by
  classical
  have hS0 :
      0 ≤ (Finset.univ.erase y).sum (fun j => |z j|) := by
    exact Finset.sum_nonneg (fun j _hj => abs_nonneg (z j))
  have habs :
      (Finset.univ.erase y).sum (fun j => |z j|) ≤ (1 : ℝ) / 4 :=
    absSumBound_of_sq_le_energyBound hS0 hpX hpXle hsq
  exact coordinateEstimate_from_absSumBound
    hK hpX hpY hlam hlamK hdiag hbound habs hg hU

/-- Finite-sum Cauchy step used in the coordinate estimate.

The hypotheses `hP_le` and `hZ_le` are the bookkeeping consequences of the
lottery normalization and the auxiliary energy identity, respectively. -/
lemma sqAbsSum_le_energyProduct_of_cauchy
    {α : Type*} [Fintype α] [DecidableEq α]
    {p z : α → ℝ} {pX T : ℝ} {y : α}
    (hp : ∀ i : α, 0 < p i)
    (hPpos : 0 < (Finset.univ.erase y).sum (fun i => p i))
    (hP_le :
      (Finset.univ.erase y).sum (fun i => p i) ≤ 1 - pX)
    (hZ_le :
      (Finset.univ.erase y).sum (fun i => |z i| ^ 2 / p i) ≤
        T - T ^ 2 / pX) :
    ((Finset.univ.erase y).sum (fun i => |z i|)) ^ 2 ≤
      (1 - pX) * (T - T ^ 2 / pX) := by
  classical
  let s : Finset α := Finset.univ.erase y
  let P : ℝ := s.sum (fun i => p i)
  let Z : ℝ := s.sum (fun i => |z i| ^ 2 / p i)
  have hPpos' : 0 < P := by simpa [P, s] using hPpos
  have hP_le' : P ≤ 1 - pX := by simpa [P, s] using hP_le
  have hZ_le' : Z ≤ T - T ^ 2 / pX := by simpa [Z, s] using hZ_le
  have hZ_nonneg : 0 ≤ Z := by
    unfold Z
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact div_nonneg (sq_nonneg _) (hp i).le
  have hR_nonneg : 0 ≤ T - T ^ 2 / pX :=
    le_trans hZ_nonneg hZ_le'
  have hOneMinus_nonneg : 0 ≤ 1 - pX :=
    le_trans hPpos'.le hP_le'
  have hcauchy :
      ((s.sum (fun i => |z i|)) ^ 2) / P ≤ Z := by
    have hsed :
        ((s.sum (fun i => |z i|)) ^ 2) / (s.sum (fun i => p i)) ≤
          s.sum (fun i => |z i| ^ 2 / p i) :=
      Finset.sq_sum_div_le_sum_sq_div s (fun i => |z i|)
        (g := p) (fun i hi => hp i)
    simpa [P, Z] using hsed
  have hSsq_le_PZ :
      (s.sum (fun i => |z i|)) ^ 2 ≤ P * Z := by
    have hmul := (div_le_iff₀ hPpos').mp hcauchy
    nlinarith
  have hPZ_le :
      P * Z ≤ (1 - pX) * (T - T ^ 2 / pX) :=
    mul_le_mul hP_le' hZ_le' hZ_nonneg hOneMinus_nonneg
  exact hSsq_le_PZ.trans hPZ_le

lemma erase_probability_sum_le_one_sub
    {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → ℝ} {pX : ℝ} {y : α}
    (hp_nonneg : ∀ i : α, 0 ≤ p i)
    (hsum : pX + Finset.univ.sum (fun i => p i) = 1) :
    (Finset.univ.erase y).sum (fun i => p i) ≤ 1 - pX := by
  classical
  have hsubset :
      (Finset.univ.erase y : Finset α) ⊆ Finset.univ := by
    intro i hi
    simp
  have hle_univ :
      (Finset.univ.erase y).sum (fun i => p i) ≤
        Finset.univ.sum (fun i => p i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro i _hi _hnot; exact hp_nonneg i)
  have huniv : Finset.univ.sum (fun i => p i) = 1 - pX := by
    linarith
  linarith

lemma erase_probability_sum_pos_of_exists
    {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → ℝ} {y : α}
    (hp : ∀ i : α, 0 < p i)
    (hex : ∃ i : α, i ≠ y) :
    0 < (Finset.univ.erase y).sum (fun i => p i) := by
  classical
  obtain ⟨i, hiy⟩ := hex
  refine Finset.sum_pos ?_ ?_
  · intro j _hj
    exact hp j
  · exact ⟨i, by simp [hiy]⟩

lemma erase_energy_sum_le_remainder
    {α : Type*} [Fintype α] [DecidableEq α]
    {p z : α → ℝ} {pX T : ℝ} {y : α}
    (hp : ∀ i : α, 0 < p i)
    (henergy :
      Finset.univ.sum (fun i => |z i| ^ 2 / p i) + T ^ 2 / pX = T) :
    (Finset.univ.erase y).sum (fun i => |z i| ^ 2 / p i) ≤
      T - T ^ 2 / pX := by
  classical
  have hsubset :
      (Finset.univ.erase y : Finset α) ⊆ Finset.univ := by
    intro i hi
    simp
  have hle_univ :
      (Finset.univ.erase y).sum (fun i => |z i| ^ 2 / p i) ≤
        Finset.univ.sum (fun i => |z i| ^ 2 / p i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro i _hi _hnot
        exact div_nonneg (sq_nonneg _) (hp i).le)
  have huniv :
      Finset.univ.sum (fun i => |z i| ^ 2 / p i) = T - T ^ 2 / pX := by
    linarith
  linarith

/-- Coordinate estimate with the Cauchy step supplied in the form that comes
directly from the auxiliary energy identity. -/
theorem coordinateEstimate_from_cauchyEnergy
    {α : Type*} [Fintype α] [DecidableEq α]
    {c : α → α → ℝ} {p z : α → ℝ}
    {K lam pX pY T U g : ℝ} {y : α}
    (hK : 0 ≤ K)
    (hp : ∀ i : α, 0 < p i)
    (hpX : 0 < pX)
    (hpXle : pX ≤ 1)
    (hpY : 0 < pY)
    (hPpos : 0 < (Finset.univ.erase y).sum (fun i => p i))
    (hP_le :
      (Finset.univ.erase y).sum (fun i => p i) ≤ 1 - pX)
    (hZ_le :
      (Finset.univ.erase y).sum (fun i => |z i| ^ 2 / p i) ≤
        T - T ^ 2 / pX)
    (hlam : 0 < lam)
    (hlamK : lam * K ≤ 4)
    (hdiag : c y y = 0)
    (hbound : ∀ j : α, |c y j| ≤ K)
    (hg :
      g = 1 - lam * Finset.univ.sum (fun j => c y j * z j))
    (hU : U = -lam * (pX * pY * g)) :
    U ≤ 0 := by
  classical
  have hsq :
      ((Finset.univ.erase y).sum (fun j => |z j|)) ^ 2 ≤
        (1 - pX) * (T - T ^ 2 / pX) :=
    sqAbsSum_le_energyProduct_of_cauchy hp hPpos hP_le hZ_le
  exact coordinateEstimate_from_sqEnergyBound
    hK hpX hpXle hpY hlam hlamK hdiag hbound hsq hg hU

/-- Coordinate estimate with the Cauchy inputs derived from normalization and
the auxiliary energy identity.  The hypothesis `hex` is the nontrivial case
where there is at least one opponent other than `y`; the one-opponent case is
handled separately in the paper. -/
theorem coordinateEstimate_from_energyIdentity
    {α : Type*} [Fintype α] [DecidableEq α]
    {c : α → α → ℝ} {p z : α → ℝ}
    {K lam pX pY T U g : ℝ} {y : α}
    (hK : 0 ≤ K)
    (hp : ∀ i : α, 0 < p i)
    (hpX : 0 < pX)
    (hpXle : pX ≤ 1)
    (hpY : 0 < pY)
    (hsum : pX + Finset.univ.sum (fun i => p i) = 1)
    (hex : ∃ i : α, i ≠ y)
    (henergy :
      Finset.univ.sum (fun i => |z i| ^ 2 / p i) + T ^ 2 / pX = T)
    (hlam : 0 < lam)
    (hlamK : lam * K ≤ 4)
    (hdiag : c y y = 0)
    (hbound : ∀ j : α, |c y j| ≤ K)
    (hg :
      g = 1 - lam * Finset.univ.sum (fun j => c y j * z j))
    (hU : U = -lam * (pX * pY * g)) :
    U ≤ 0 := by
  classical
  have hPpos :
      0 < (Finset.univ.erase y).sum (fun i => p i) :=
    erase_probability_sum_pos_of_exists hp hex
  have hP_le :
      (Finset.univ.erase y).sum (fun i => p i) ≤ 1 - pX :=
    erase_probability_sum_le_one_sub (fun i => (hp i).le) hsum
  have hZ_le :
      (Finset.univ.erase y).sum (fun i => |z i| ^ 2 / p i) ≤
        T - T ^ 2 / pX :=
    erase_energy_sum_le_remainder hp henergy
  exact coordinateEstimate_from_cauchyEnergy
    hK hp hpX hpXle hpY hPpos hP_le hZ_le
    hlam hlamK hdiag hbound hg hU

/-- The one-opponent edge case of the coordinate estimate.  If every coordinate
in `A` is the improved opponent `y`, then the skew term in the auxiliary
response vanishes directly. -/
theorem coordinateEstimate_singleOpponent
    {α : Type*} [Fintype α] [DecidableEq α]
    {c : α → α → ℝ} {z : α → ℝ}
    {lam pX pY U g : ℝ} {y : α}
    (honly : ∀ j : α, j = y)
    (hpX : 0 < pX)
    (hpY : 0 < pY)
    (hlam : 0 < lam)
    (hdiag : c y y = 0)
    (hg :
      g = 1 - lam * Finset.univ.sum (fun j => c y j * z j))
    (hU : U = -lam * (pX * pY * g)) :
    U ≤ 0 := by
  classical
  have hsum_zero : Finset.univ.sum (fun j => c y j * z j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j _hj
    have hj : j = y := honly j
    subst hj
    simp [hdiag]
  have hg_one : g = 1 := by
    rw [hsum_zero] at hg
    linarith
  rw [hU, hg_one]
  nlinarith [mul_pos hpX hpY, hlam]

lemma skew_weighted_double_sum_eq_zero
    {α : Type*} [Fintype α]
    {c : α → α → ℝ} {z : α → ℝ}
    (hskew : ∀ i j : α, c i j = -c j i) :
    Finset.univ.sum
        (fun i => z i * Finset.univ.sum (fun j => c i j * z j)) = 0 := by
  classical
  let S : ℝ :=
    Finset.univ.sum
      (fun i => z i * Finset.univ.sum (fun j => c i j * z j))
  have hswap :
      S =
        Finset.univ.sum
          (fun j => Finset.univ.sum (fun i => z i * (c i j * z j))) := by
    unfold S
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hneg :
      Finset.univ.sum
          (fun j => Finset.univ.sum (fun i => z i * (c i j * z j))) =
        -S := by
    unfold S
    calc
      Finset.univ.sum
          (fun j => Finset.univ.sum (fun i => z i * (c i j * z j)))
          =
        Finset.univ.sum
          (fun j => Finset.univ.sum (fun i => -(z j * (c j i * z i)))) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hskew i j]
            ring
      _ = -Finset.univ.sum
          (fun j => Finset.univ.sum (fun i => z j * (c j i * z i))) := by
            simp [Finset.sum_neg_distrib]
      _ = -S := by
            unfold S
            simp_rw [Finset.mul_sum]
  have hS : S = -S := hswap.trans hneg
  linarith

lemma skew_weighted_double_sum_swap
    {α : Type*} [Fintype α]
    {c : α → α → ℝ} {z s : α → ℝ}
    (hskew : ∀ i j : α, c i j = -c j i) :
    Finset.univ.sum
        (fun i => z i * Finset.univ.sum (fun j => c i j * s j)) =
      -Finset.univ.sum
        (fun i => s i * Finset.univ.sum (fun j => c i j * z j)) := by
  classical
  calc
    Finset.univ.sum
        (fun i => z i * Finset.univ.sum (fun j => c i j * s j))
        =
      Finset.univ.sum
        (fun j => Finset.univ.sum (fun i => z i * (c i j * s j))) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ =
      Finset.univ.sum
        (fun j => Finset.univ.sum (fun i => -(s j * (c j i * z i)))) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hskew i j]
          ring
    _ =
      -Finset.univ.sum
        (fun j => Finset.univ.sum (fun i => s j * (c j i * z i))) := by
          simp [Finset.sum_neg_distrib]
    _ =
      -Finset.univ.sum
        (fun i => s i * Finset.univ.sum (fun j => c i j * z j)) := by
          simp_rw [Finset.mul_sum]

lemma auxiliary_energy_identity_from_weighted_sum
    {α : Type*} [Fintype α]
    {p z : α → ℝ} {c : α → α → ℝ} {pX T lam : ℝ}
    (hT : Finset.univ.sum (fun i => z i) = T)
    (hskew : ∀ i j : α, c i j = -c j i)
    (hweighted :
      Finset.univ.sum
        (fun i =>
          z i *
            (z i / p i + T / pX +
              lam * Finset.univ.sum (fun j => c i j * z j))) = T) :
    Finset.univ.sum (fun i => |z i| ^ 2 / p i) + T ^ 2 / pX = T := by
  classical
  have hdouble :
      Finset.univ.sum
          (fun i => z i * Finset.univ.sum (fun j => c i j * z j)) = 0 :=
    skew_weighted_double_sum_eq_zero hskew
  have hsq_abs :
      Finset.univ.sum (fun i => |z i| ^ 2 / p i) =
        Finset.univ.sum (fun i => z i ^ 2 / p i) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [sq_abs]
  have hexpand :
      Finset.univ.sum
        (fun i =>
          z i *
            (z i / p i + T / pX +
              lam * Finset.univ.sum (fun j => c i j * z j))) =
        Finset.univ.sum (fun i => z i ^ 2 / p i) +
          T ^ 2 / pX +
            lam *
              Finset.univ.sum
                (fun i => z i * Finset.univ.sum (fun j => c i j * z j)) := by
    calc
      Finset.univ.sum
        (fun i =>
          z i *
            (z i / p i + T / pX +
              lam * Finset.univ.sum (fun j => c i j * z j)))
          =
        Finset.univ.sum
          (fun i =>
            z i ^ 2 / p i + (T / pX) * z i +
              lam * (z i * Finset.univ.sum (fun j => c i j * z j))) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ =
        Finset.univ.sum (fun i => z i ^ 2 / p i) +
          Finset.univ.sum (fun i => (T / pX) * z i) +
            Finset.univ.sum
              (fun i => lam * (z i * Finset.univ.sum (fun j => c i j * z j))) := by
            simp [Finset.sum_add_distrib]
      _ =
        Finset.univ.sum (fun i => z i ^ 2 / p i) +
          (T / pX) * Finset.univ.sum (fun i => z i) +
            lam *
              Finset.univ.sum
                (fun i => z i * Finset.univ.sum (fun j => c i j * z j)) := by
            simp [Finset.mul_sum]
      _ =
        Finset.univ.sum (fun i => z i ^ 2 / p i) +
          T ^ 2 / pX +
            lam *
              Finset.univ.sum
                (fun i => z i * Finset.univ.sum (fun j => c i j * z j)) := by
            rw [hT]
            ring
  have hmain := hweighted
  rw [hexpand] at hmain
  rw [hdouble] at hmain
  rw [hsq_abs]
  linarith

/-- Positivity of the denominator in the three-candidate finite-secant
calculation. -/
lemma threeCandidateSecant_den_pos
    {lam D Lx Ly Lz : ℝ}
    (hLx : 0 < Lx) (hLy : 0 < Ly) (hLz : 0 < Lz) :
    0 < lam ^ 2 * D ^ 2 +
      1 / (Ly * Lz) + 1 / (Ly * Lx) + 1 / (Lz * Lx) := by
  positivity

/-- The two-equation linear algebra in Lemma `three-candidate-secant-response`.

The variables `Lx`, `Ly`, and `Lz` are the three logarithmic means
`L_x^s`, `L_y^s`, and `L_z^s`; `D` is the displayed margin coefficient
`D_s`; and `Δx`, `Δy`, `Δz` are the changes in the three probabilities. -/
lemma threeCandidateSecant_formula_from_linear_system
    {lam s mux muy D Lx Ly Lz Δx Δy Δz den : ℝ}
    (hLx : Lx ≠ 0) (hLy : Ly ≠ 0) (hLz : Lz ≠ 0)
    (hden :
      den = lam ^ 2 * D ^ 2 +
        1 / (Ly * Lz) + 1 / (Ly * Lx) + 1 / (Lz * Lx))
    (hden_ne : den ≠ 0)
    (hsum : Δx + Δy + Δz = 0)
    (hy :
      (1 / Ly + 1 / Lx) * Δy + (1 / Lx - lam * D) * Δz =
        -lam * s * (mux + muy))
    (hz :
      (1 / Lx + lam * D) * Δy + (1 / Lz + 1 / Lx) * Δz =
        -lam * s * muy) :
    Δx =
      lam * s * (mux / Lz + muy / Ly + muy / Lz - lam * D * mux) / den := by
  rw [eq_div_iff hden_ne]
  rw [hden]
  field_simp [hLx, hLy, hLz] at hy hz ⊢
  ring_nf at hy hz hsum ⊢
  linear_combination
    (D * Lz * lam - 1) * hy +
    (-D * Ly * lam - 1) * hz +
    (D ^ 2 * Lx * Ly * Lz * lam ^ 2 + Lx + Ly + Lz) * hsum

/-- The same finite-secant calculation, stated in the form in the TeX proof:
first the two log-ratio secant equations, then substitution of
`Δx = -Δy - Δz`. -/
lemma threeCandidateSecant_formula_from_log_equations
    {lam s mux muy D Lx Ly Lz Δx Δy Δz den : ℝ}
    (hLx : Lx ≠ 0) (hLy : Ly ≠ 0) (hLz : Lz ≠ 0)
    (hden :
      den = lam ^ 2 * D ^ 2 +
        1 / (Ly * Lz) + 1 / (Ly * Lx) + 1 / (Lz * Lx))
    (hden_ne : den ≠ 0)
    (hsum : Δx + Δy + Δz = 0)
    (hy :
      Δy / Ly - Δx / Lx =
        lam * D * Δz - lam * s * (mux + muy))
    (hz :
      Δz / Lz - Δx / Lx =
        -lam * D * Δy - lam * s * muy) :
    Δx =
      lam * s * (mux / Lz + muy / Ly + muy / Lz - lam * D * mux) / den := by
  have hx : Δx = -Δy - Δz := by linarith
  have hy' :
      (1 / Ly + 1 / Lx) * Δy + (1 / Lx - lam * D) * Δz =
        -lam * s * (mux + muy) := by
    rw [hx] at hy
    ring_nf at hy ⊢
    linarith
  have hz' :
      (1 / Lx + lam * D) * Δy + (1 / Lz + 1 / Lx) * Δz =
        -lam * s * muy := by
    rw [hx] at hz
    ring_nf at hz ⊢
    linarith
  exact threeCandidateSecant_formula_from_linear_system
    hLx hLy hLz hden hden_ne hsum hy' hz'

lemma threeCandidateSecant_drop_of_negative_numerator
    {lam s N den Δx : ℝ}
    (hlam : 0 < lam) (hs : 0 < s)
    (hN : N < 0) (hden : 0 < den)
    (hformula : Δx = lam * s * N / den) :
    Δx < 0 := by
  rw [hformula]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (mul_pos hlam hs) hN) hden

lemma threeCandidateSecant_limit_expression_negative
    {lam a b d : ℝ}
    (ha : 0 < a)
    (hnorm : 2 * a + b = 1)
    (hcrit : 1 < lam * a ^ 2 * d) :
    2 + b / a - lam * d * a < 0 := by
  have htwo : 2 + b / a = 1 / a := by
    field_simp [ha.ne']
    linarith
  rw [htwo]
  have hmul : 1 / a < lam * d * a := by
    rw [div_lt_iff₀ ha]
    nlinarith
  linarith

/-- Limit calculation for the numerator in the three-candidate finite-secant
formula.  The continuity of the logarithmic means is proved separately; this
lemma records the remaining algebraic limit step. -/
lemma threeCandidateSecant_numerator_tendsto
    {ι : Type*} {l : Filter ι}
    {lam mux muy d : ℝ} {Ly Lz D : ι → ℝ}
    (hmux : 0 < mux) (hmuy : 0 < muy)
    (hLy : Filter.Tendsto Ly l (𝓝 muy))
    (hLz : Filter.Tendsto Lz l (𝓝 mux))
    (hD : Filter.Tendsto D l (𝓝 d)) :
    Filter.Tendsto
      (fun s => mux / Lz s + muy / Ly s + muy / Lz s - lam * D s * mux)
      l (𝓝 (2 + muy / mux - lam * d * mux)) := by
  have h1 :
      Filter.Tendsto (fun s => mux / Lz s) l (𝓝 (mux / mux)) :=
    tendsto_const_nhds.div hLz hmux.ne'
  have h2 :
      Filter.Tendsto (fun s => muy / Ly s) l (𝓝 (muy / muy)) :=
    tendsto_const_nhds.div hLy hmuy.ne'
  have h3 :
      Filter.Tendsto (fun s => muy / Lz s) l (𝓝 (muy / mux)) :=
    tendsto_const_nhds.div hLz hmux.ne'
  have hprod :
      Filter.Tendsto (fun s => lam * D s * mux) l
        (𝓝 (lam * d * mux)) := by
    simpa [mul_assoc] using
      (tendsto_const_nhds.mul hD).mul tendsto_const_nhds
  have hsum :
      Filter.Tendsto
        (fun s => mux / Lz s + muy / Ly s + muy / Lz s)
        l (𝓝 (mux / mux + muy / muy + muy / mux)) :=
    (h1.add h2).add h3
  have hlim := hsum.sub hprod
  have hlimit_eq :
      mux / mux + muy / muy + muy / mux - lam * d * mux =
        2 + muy / mux - lam * d * mux := by
    field_simp [hmux.ne', hmuy.ne']
    ring
  simpa [hlimit_eq] using hlim

/-- If the secant numerator tends to a negative number along positive
improvements, then it is negative for some sufficiently small positive
improvement.  This is the topological step in the converse proof, with
differentiability absent. -/
theorem exists_pos_lt_of_tendsto_nhdsWithin_Ioi_lt
    {f : ℝ → ℝ} {L ε : ℝ}
    (hε : 0 < ε) (hL : L < 0)
    (hf : Filter.Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∃ s : ℝ, 0 < s ∧ s < ε ∧ f s < 0 := by
  have hneg_event : ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < 0 :=
    hf.eventually_lt_const hL
  have hpos_event : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs
  have hlt_event : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < ε :=
    nhdsWithin_le_nhds (Iio_mem_nhds hε)
  rcases (hneg_event.and (hpos_event.and hlt_event)).exists with
    ⟨s, hneg, hpos, hlt⟩
  exact ⟨s, hpos, hlt, hneg⟩

/-- If the secant numerator tends to a negative limit, and the denominator and
finite-secant formula hold for all sufficiently small positive improvements,
then some sufficiently small positive improvement produces a strict drop. -/
theorem exists_threeCandidateSecant_drop_of_tendsto_negative_numerator
    {N den Δx : ℝ → ℝ} {lam L ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) (hL : L < 0)
    (hN : Filter.Tendsto N (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hden : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < den s)
    (hformula : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Δx s = lam * s * N s / den s) :
    ∃ s : ℝ, 0 < s ∧ s < ε ∧ Δx s < 0 := by
  have hneg : ∀ᶠ s in 𝓝[>] (0 : ℝ), N s < 0 :=
    hN.eventually_lt_const hL
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs
  have hlt : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < ε :=
    nhdsWithin_le_nhds (Iio_mem_nhds hε)
  have hgood : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      N s < 0 ∧ 0 < den s ∧
        Δx s = lam * s * N s / den s ∧ 0 < s ∧ s < ε := by
    filter_upwards [hneg, hden, hformula, hpos, hlt] with s hn hd hf hp he
    exact ⟨hn, hd, hf, hp, he⟩
  rcases hgood.exists with ⟨s, hn, hd, hf, hp, he⟩
  exact ⟨s, hp, he,
    threeCandidateSecant_drop_of_negative_numerator hlam hp hn hd hf⟩

/-- The three-candidate normalized margin matrix used for the all-profile
sharpness example: `x = 0`, `y = 1`, and `z = 2`. -/
noncomputable def nlhfSharpAllMargin3 (η : ℝ) : Fin 3 → Fin 3 → ℝ
  | 0, 1 => 1 - η
  | 1, 0 => -(1 - η)
  | 0, 2 => -1
  | 2, 0 => 1
  | 1, 2 => 1
  | 2, 1 => -1
  | _, _ => 0

lemma nlhfSharpAllMargin3_normalized
    {η : ℝ} (hη0 : 0 ≤ η) (hη2 : η ≤ 2) :
    IsNormalizedMarginMatrix (nlhfSharpAllMargin3 η) := by
  refine ⟨?diag, ?skew, ?bound⟩
  · intro x
    fin_cases x <;> simp [nlhfSharpAllMargin3]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [nlhfSharpAllMargin3]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [nlhfSharpAllMargin3] <;>
      try norm_num
    all_goals
      rw [abs_le]
      constructor <;> linarith

lemma nlhfSharpAllMargin3_coordinate_yz (η : ℝ) :
    nlhfCoordinateC (nlhfSharpAllMargin3 η) 0 1 2 = 3 - η := by
  norm_num [nlhfCoordinateC, nlhfSharpAllMargin3]
  ring

/-- The three-candidate normalized margin matrix used for the linear-order
sharpness example: `x = 0`, `y = 1`, and `z = 2`. -/
noncomputable def nlhfSharpLinearMargin3 (η : ℝ) : Fin 3 → Fin 3 → ℝ
  | 0, 1 => 1 - η
  | 1, 0 => -(1 - η)
  | 0, 2 => 1
  | 2, 0 => -1
  | 1, 2 => 1
  | 2, 1 => -1
  | _, _ => 0

lemma nlhfSharpLinearMargin3_normalized
    {η : ℝ} (hη0 : 0 ≤ η) (hη2 : η ≤ 2) :
    IsNormalizedMarginMatrix (nlhfSharpLinearMargin3 η) := by
  refine ⟨?diag, ?skew, ?bound⟩
  · intro x
    fin_cases x <;> simp [nlhfSharpLinearMargin3]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [nlhfSharpLinearMargin3]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [nlhfSharpLinearMargin3] <;>
      try norm_num
    all_goals
      rw [abs_le]
      constructor <;> linarith

lemma nlhfSharpLinearMargin3_coordinate_yz (η : ℝ) :
    nlhfCoordinateC (nlhfSharpLinearMargin3 η) 0 1 2 = 1 - η := by
  norm_num [nlhfCoordinateC, nlhfSharpLinearMargin3]

/-- The weights of the two ballot types in the linear-order sharpness
construction: `xyz` has weight `1 - η/2`, and `yxz` has weight `η/2`. -/
noncomputable def nlhfSharpLinearWeights3 (η : ℝ) : Fin 2 → ℝ
  | 0 => 1 - η / 2
  | 1 => η / 2

/-- Scores representing the two linear orders in the linear-order sharpness
construction.  Voter `0` has `x > y > z`; voter `1` has `y > x > z`. -/
noncomputable def nlhfSharpLinearScore3 : Fin 2 → Fin 3 → ℝ
  | 0, 0 => 2
  | 0, 1 => 1
  | 0, 2 => 0
  | 1, 0 => 1
  | 1, 1 => 2
  | 1, 2 => 0

lemma nlhfSharpLinearScore3_linear :
    IsLinearScoreProfile nlhfSharpLinearScore3 := by
  intro v i j hij
  fin_cases v <;> fin_cases i <;> fin_cases j <;>
    first | rfl | norm_num [nlhfSharpLinearScore3] at hij

lemma nlhfSharpLinearScore3_assigned_linear
    {W : Type*} (assign : W → Fin 2) :
    IsLinearScoreProfile (fun u : W => nlhfSharpLinearScore3 (assign u)) := by
  intro u
  exact nlhfSharpLinearScore3_linear (assign u)

/-- Expanded finite electorate with two blocks: the left block has ballot type
`0` (`xyz`) and the right block has ballot type `1` (`yxz`). -/
def twoBlockAssign (n k : ℕ) : Sum (Fin n) (Fin k) → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

lemma twoBlockAssign_fiber_zero_card (n k : ℕ) :
    (Finset.univ.filter (fun u : Sum (Fin n) (Fin k) =>
      twoBlockAssign n k u = 0)).card = n := by
  let s : Finset (Sum (Fin n) (Fin k)) :=
    Finset.univ.filter (fun u => twoBlockAssign n k u = 0)
  have hcard : s.card = (Finset.univ : Finset (Fin n)).card := by
    refine Finset.card_bij
      (fun u hu =>
        match u with
        | Sum.inl v => v
        | Sum.inr _ =>
            False.elim (by
              have hprop := (Finset.mem_filter.mp hu).2
              simp [twoBlockAssign] at hprop))
      ?hi ?hinj ?hsurj
    · intro u hu
      simp
    · intro u₁ hu₁ u₂ hu₂ heq
      cases u₁ with
      | inl v₁ =>
          cases u₂ with
          | inl v₂ =>
              simp at heq
              subst v₂
              rfl
          | inr _ =>
              have hprop := (Finset.mem_filter.mp hu₂).2
              simp [twoBlockAssign] at hprop
      | inr _ =>
          have hprop := (Finset.mem_filter.mp hu₁).2
          simp [twoBlockAssign] at hprop
    · intro v _hv
      refine ⟨Sum.inl v, ?_, rfl⟩
      simp [s, twoBlockAssign]
  simpa [s, Finset.card_fin] using hcard

lemma twoBlockAssign_fiber_one_card (n k : ℕ) :
    (Finset.univ.filter (fun u : Sum (Fin n) (Fin k) =>
      twoBlockAssign n k u = 1)).card = k := by
  let s : Finset (Sum (Fin n) (Fin k)) :=
    Finset.univ.filter (fun u => twoBlockAssign n k u = 1)
  have hcard : s.card = (Finset.univ : Finset (Fin k)).card := by
    refine Finset.card_bij
      (fun u hu =>
        match u with
        | Sum.inl _ =>
            False.elim (by
              have hprop := (Finset.mem_filter.mp hu).2
              simp [twoBlockAssign] at hprop)
        | Sum.inr w => w)
      ?hi ?hinj ?hsurj
    · intro u hu
      simp
    · intro u₁ hu₁ u₂ hu₂ heq
      cases u₁ with
      | inl _ =>
          have hprop := (Finset.mem_filter.mp hu₁).2
          simp [twoBlockAssign] at hprop
      | inr w₁ =>
          cases u₂ with
          | inl _ =>
              have hprop := (Finset.mem_filter.mp hu₂).2
              simp [twoBlockAssign] at hprop
          | inr w₂ =>
              simp at heq
              subst w₂
              rfl
    · intro v _hv
      refine ⟨Sum.inr v, ?_, rfl⟩
      simp [s, twoBlockAssign]
  simpa [s, Finset.card_fin] using hcard

lemma nlhfSharpLinearWeights3_nonneg
    {η : ℝ} (hη0 : 0 ≤ η) (hη2 : η ≤ 2) :
    ∀ v : Fin 2, 0 ≤ nlhfSharpLinearWeights3 η v := by
  intro v
  fin_cases v <;> simp [nlhfSharpLinearWeights3] <;> linarith

lemma nlhfSharpLinearWeights3_sum (η : ℝ) :
    Finset.univ.sum (fun v : Fin 2 => nlhfSharpLinearWeights3 η v) = 1 := by
  norm_num [nlhfSharpLinearWeights3]

lemma nlhfSharpLinearWeights3_twoBlock_fiber_weights
    (n k : ℕ) (hN : 0 < n + k) :
    ∀ v : Fin 2,
      nlhfSharpLinearWeights3 (2 * (k : ℝ) / (n + k : ℝ)) v =
        ((Finset.univ.filter (fun u : Sum (Fin n) (Fin k) =>
          twoBlockAssign n k u = v)).card : ℝ) /
          (Fintype.card (Sum (Fin n) (Fin k)) : ℝ) := by
  have hNreal : (0 : ℝ) < (n : ℝ) + (k : ℝ) := by
    have hcast : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by
      exact_mod_cast hN
    simpa using hcast
  have hKNreal : (0 : ℝ) < (k : ℝ) + (n : ℝ) := by nlinarith
  intro v
  fin_cases v
  · simp [nlhfSharpLinearWeights3, twoBlockAssign_fiber_zero_card,
      Fintype.card_sum]
    field_simp [ne_of_gt hNreal, ne_of_gt hKNreal]
    ring
  · simp [nlhfSharpLinearWeights3, twoBlockAssign_fiber_one_card,
      Fintype.card_sum]
    field_simp [ne_of_gt hNreal]

/-- The two weighted linear-order ballot types produce exactly the
linear-order sharpness margin matrix used in the converse proof. -/
lemma nlhfSharpLinearMargin3_eq_weightedProfile (η : ℝ) :
    weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
        nlhfSharpLinearScore3 =
      nlhfSharpLinearMargin3 η := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [weightedScoreProfileMargin, nlhfSharpLinearWeights3,
      nlhfSharpLinearScore3, nlhfSharpLinearMargin3,
      scoreMarginSign, scoreMarginSignReal] <;>
    ring

/-- Denominator-cleared finite-profile form of the linear-order sharpness
matrix.  The hypotheses say that the two displayed weights are the fractions
of the expanded electorate assigned to the two ballot types. -/
lemma nlhfSharpLinearMargin3_eq_scoreProfile_of_fiber_weights
    {W : Type*} [Fintype W] [Nonempty W]
    (assign : W → Fin 2) {η : ℝ}
    (hw : ∀ v : Fin 2,
      nlhfSharpLinearWeights3 η v =
        ((Finset.univ.filter (fun u : W => assign u = v)).card : ℝ) /
          (Fintype.card W : ℝ)) :
    scoreProfileMargin (fun u : W => nlhfSharpLinearScore3 (assign u)) =
      nlhfSharpLinearMargin3 η := by
  rw [← nlhfSharpLinearMargin3_eq_weightedProfile η]
  exact (weightedScoreProfileMargin_eq_scoreProfileMargin_of_fiber_weights
    assign nlhfSharpLinearScore3 (nlhfSharpLinearWeights3 η) hw).symm

/-- Concrete denominator-cleared finite-profile form of the linear-order
sharpness matrix, with `n` voters of type `xyz` and `k` voters of type `yxz`. -/
lemma nlhfSharpLinearMargin3_eq_twoBlockScoreProfile
    (n k : ℕ) (hN : 0 < n + k) :
    scoreProfileMargin
      (fun u : Sum (Fin n) (Fin k) =>
        nlhfSharpLinearScore3 (twoBlockAssign n k u)) =
      nlhfSharpLinearMargin3 (2 * (k : ℝ) / (n + k : ℝ)) := by
  have hnonempty : Nonempty (Sum (Fin n) (Fin k)) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · simp [hn, hk] at hN
      · exact ⟨Sum.inr ⟨0, hk⟩⟩
    · exact ⟨Sum.inl ⟨0, hn⟩⟩
  letI : Nonempty (Sum (Fin n) (Fin k)) := hnonempty
  exact nlhfSharpLinearMargin3_eq_scoreProfile_of_fiber_weights
    (twoBlockAssign n k)
    (nlhfSharpLinearWeights3_twoBlock_fiber_weights n k hN)

/-- The finite linear sharpness profile with one `yxz` voter among `N` total
voters realizes the parameter `eta = 2/N`. -/
lemma nlhfSharpLinearMargin3_eq_oneYxzScoreProfile
    (N : ℕ) (hN : 0 < N) :
    scoreProfileMargin
      (fun u : Sum (Fin (N - 1)) (Fin 1) =>
        nlhfSharpLinearScore3 (twoBlockAssign (N - 1) 1 u)) =
      nlhfSharpLinearMargin3 (2 / (N : ℝ)) := by
  have htotal : 0 < (N - 1) + 1 := by omega
  have hden_nat : (N - 1) + 1 = N := by omega
  have hden_real : (((N - 1) + 1 : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast hden_nat
  have hden_real' : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast hden_nat
  have h := nlhfSharpLinearMargin3_eq_twoBlockScoreProfile (N - 1) 1 htotal
  simpa [hden_real, hden_real'] using h

/-- The linear-order sharpness matrix inherits the `K = 1` coordinate bound
from its weighted linear-order profile representation. -/
lemma nlhfSharpLinearMargin3_coordinate_abs_le_one_from_profile
    {η : ℝ} (hη0 : 0 ≤ η) (hη2 : η ≤ 2) (x i j : Fin 3) :
    |nlhfCoordinateC (nlhfSharpLinearMargin3 η) x i j| ≤ (1 : ℝ) := by
  rw [← nlhfSharpLinearMargin3_eq_weightedProfile η]
  exact weightedScoreProfileMargin_coordinate_abs_le_one
    nlhfSharpLinearScore3
    (nlhfSharpLinearWeights3_nonneg hη0 hη2)
    (nlhfSharpLinearWeights3_sum η) x i j

/-- The weights after moving weight `s/2` from the `yxz` ballot type to the
`xyz` ballot type in the linear-order sharpness construction. -/
noncomputable def nlhfSharpLinearWeights3Improved
    (η s : ℝ) : Fin 2 → ℝ
  | 0 => 1 - η / 2 + s / 2
  | 1 => η / 2 - s / 2

lemma nlhfSharpLinearWeights3Improved_nonneg
    {η s : ℝ} (hη2 : η ≤ 2)
    (hs0 : 0 ≤ s) (hsη : s ≤ η) :
    ∀ v : Fin 2, 0 ≤ nlhfSharpLinearWeights3Improved η s v := by
  intro v
  fin_cases v <;> simp [nlhfSharpLinearWeights3Improved] <;> linarith

lemma nlhfSharpLinearWeights3Improved_sum (η s : ℝ) :
    Finset.univ.sum
      (fun v : Fin 2 => nlhfSharpLinearWeights3Improved η s v) = 1 := by
  norm_num [nlhfSharpLinearWeights3Improved]

lemma nlhfSharpLinearWeights3Improved_twoBlock_fiber_weights
    (n k r : ℕ) (hr : r ≤ k) (hN : 0 < n + k) :
    ∀ v : Fin 2,
      nlhfSharpLinearWeights3Improved
          (2 * (k : ℝ) / (n + k : ℝ))
          (2 * (r : ℝ) / (n + k : ℝ)) v =
        ((Finset.univ.filter (fun u : Sum (Fin (n + r)) (Fin (k - r)) =>
          twoBlockAssign (n + r) (k - r) u = v)).card : ℝ) /
          (Fintype.card (Sum (Fin (n + r)) (Fin (k - r))) : ℝ) := by
  have hNreal : (0 : ℝ) < (n : ℝ) + (k : ℝ) := by
    have hcast : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by
      exact_mod_cast hN
    simpa using hcast
  have hKNreal : (0 : ℝ) < (k : ℝ) + (n : ℝ) := by nlinarith
  have hden_nat : n + r + (k - r) = n + k := by omega
  have hden_real :
      (n : ℝ) + (r : ℝ) + ((k - r : ℕ) : ℝ) =
        (n : ℝ) + (k : ℝ) := by
    exact_mod_cast hden_nat
  intro v
  fin_cases v
  · simp [nlhfSharpLinearWeights3Improved, twoBlockAssign_fiber_zero_card,
      Fintype.card_sum]
    rw [hden_real]
    field_simp [ne_of_gt hNreal, ne_of_gt hKNreal]
    ring
  · simp [nlhfSharpLinearWeights3Improved, twoBlockAssign_fiber_one_card,
      Fintype.card_sum]
    rw [hden_real]
    field_simp [ne_of_gt hNreal]
    rw [Nat.cast_sub hr]

/-- The symmetric lottery used in the three-candidate sharpness constructions:
`x` and `z` have probability `(1 - b) / 2`, while `y` has probability `b`. -/
noncomputable def nlhfSharpSymLottery3 (b : ℝ) : Fin 3 → ℝ
  | 0 => (1 - b) / 2
  | 1 => b
  | 2 => (1 - b) / 2

lemma nlhfSharpSymLottery3_apply_zero (b : ℝ) :
    nlhfSharpSymLottery3 b 0 = (1 - b) / 2 := rfl

lemma nlhfSharpSymLottery3_apply_one (b : ℝ) :
    nlhfSharpSymLottery3 b 1 = b := rfl

lemma nlhfSharpSymLottery3_apply_two (b : ℝ) :
    nlhfSharpSymLottery3 b 2 = (1 - b) / 2 := rfl

lemma nlhfSharpSymLottery3_fullSupport
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    IsFullSupportLottery (nlhfSharpSymLottery3 b) := by
  refine ⟨?pos, ?sum⟩
  · intro x
    fin_cases x <;> simp [nlhfSharpSymLottery3] <;> linarith
  · norm_num [Fin.sum_univ_three, nlhfSharpSymLottery3]
    ring

/-- Reference lottery obtained by backsolving the NLHF fixed-point equation for
a prescribed full-support lottery `p`. -/
noncomputable def nlhfBacksolvedReference
    {α : Type*} [Fintype α]
    (τ : ℝ) (M : α → α → ℝ) (p : α → ℝ) : α → ℝ :=
  tilt p (fun x => Real.exp (-(expectedMargin M p x / (2 * τ))))

lemma nlhfBacksolvedReference_fullSupport
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {τ : ℝ} {M : α → α → ℝ} {p : α → ℝ}
    (hp : IsFullSupportLottery p) :
    IsFullSupportLottery (nlhfBacksolvedReference τ M p) :=
  ⟨tilt_pos hp.1 (fun _ => Real.exp_pos _),
    tilt_sum_one hp.1 (fun _ => Real.exp_pos _)⟩

/-- Backsolving really makes the prescribed lottery `p` an NLHF fixed point. -/
lemma nlhfBacksolvedReference_fixedPoint
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {τ : ℝ} {M : α → α → ℝ} {p : α → ℝ}
    (hτ : 0 < τ) (hp : IsFullSupportLottery p) :
    IsNLHFFixedPoint τ M (nlhfBacksolvedReference τ M p) p := by
  classical
  let ℓ : α → ℝ := fun x => Real.exp (-(expectedMargin M p x / (2 * τ)))
  let D : ℝ := tiltDen p ℓ
  have hDpos : 0 < D := by
    dsimp [D]
    exact tiltDen_pos hp.1 (fun _ => Real.exp_pos _)
  have hDne : D ≠ 0 := hDpos.ne'
  have hρfull : IsFullSupportLottery (nlhfBacksolvedReference τ M p) :=
    nlhfBacksolvedReference_fullSupport hp
  refine ⟨hτ, hρfull, hp, ?_⟩
  intro x
  let E : α → ℝ := fun z => expectedMargin M p z / (2 * τ)
  have hden :
      Finset.univ.sum
        (fun z =>
          nlhfBacksolvedReference τ M p z * Real.exp (E z)) =
        1 / D := by
    calc
      Finset.univ.sum
        (fun z =>
          nlhfBacksolvedReference τ M p z * Real.exp (E z))
          =
        Finset.univ.sum
          (fun z => (p z * ℓ z / D) * Real.exp (E z)) := by
            refine Finset.sum_congr rfl ?_
            intro z _hz
            rfl
      _ =
        Finset.univ.sum (fun z => p z / D) := by
            refine Finset.sum_congr rfl ?_
            intro z _hz
            dsimp [ℓ, E]
            have hexp : Real.exp (-(expectedMargin M p z / (2 * τ))) *
                Real.exp (expectedMargin M p z / (2 * τ)) = 1 := by
              rw [← Real.exp_add]
              ring_nf
              simp
            field_simp [hDne]
            rw [mul_assoc, hexp]
            ring
      _ =
        Finset.univ.sum (fun z => p z) / D := by
            simp [Finset.sum_div]
      _ = 1 / D := by
            rw [hp.2]
  have hnum :
      nlhfBacksolvedReference τ M p x * Real.exp (E x) = p x / D := by
    dsimp [nlhfBacksolvedReference, tilt, D, ℓ, E]
    have hexp : Real.exp (-(expectedMargin M p x / (2 * τ))) *
        Real.exp (expectedMargin M p x / (2 * τ)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    change
      (p x * Real.exp (-(expectedMargin M p x / (2 * τ))) / D) *
        Real.exp (expectedMargin M p x / (2 * τ)) = p x / D
    field_simp [hDne]
    rw [mul_assoc, hexp]
    ring
  rw [hden]
  rw [hnum]
  field_simp [hDne]

/-- If `NLHF` is the selector determined by the fixed-point characterization,
then the backsolved reference makes the prescribed lottery selected. -/
theorem nlhfBacksolvedReference_selected
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {NLHF : ℝ → (α → α → ℝ) → (α → ℝ) → α → ℝ}
    (hNLHF : IsTheNLHF NLHF)
    {τ : ℝ} {M : α → α → ℝ} {p : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hτ : 0 < τ) (hp : IsFullSupportLottery p) :
    NLHF τ M (nlhfBacksolvedReference τ M p) = p :=
  hNLHF hM (nlhfBacksolvedReference_fixedPoint hτ hp)

/-- Concrete backsolving step for the all-profile sharpness matrix. -/
theorem nlhfSharpAll_backsolvedReference_selected
    {NLHF : ℝ → (Fin 3 → Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hNLHF : IsTheNLHF NLHF)
    {τ b η : ℝ}
    (hM : IsNormalizedMarginMatrix (nlhfSharpAllMargin3 η))
    (hτ : 0 < τ) (hb0 : 0 < b) (hb1 : b < 1) :
    NLHF τ (nlhfSharpAllMargin3 η)
        (nlhfBacksolvedReference τ (nlhfSharpAllMargin3 η)
          (nlhfSharpSymLottery3 b)) =
      nlhfSharpSymLottery3 b :=
  nlhfBacksolvedReference_selected hNLHF hM hτ
    (nlhfSharpSymLottery3_fullSupport hb0 hb1)

/-- Concrete backsolving step for the linear-order sharpness matrix. -/
theorem nlhfSharpLinear_backsolvedReference_selected
    {NLHF : ℝ → (Fin 3 → Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hNLHF : IsTheNLHF NLHF)
    {τ b η : ℝ}
    (hM : IsNormalizedMarginMatrix (nlhfSharpLinearMargin3 η))
    (hτ : 0 < τ) (hb0 : 0 < b) (hb1 : b < 1) :
    NLHF τ (nlhfSharpLinearMargin3 η)
        (nlhfBacksolvedReference τ (nlhfSharpLinearMargin3 η)
          (nlhfSharpSymLottery3 b)) =
      nlhfSharpSymLottery3 b :=
  nlhfBacksolvedReference_selected hNLHF hM hτ
    (nlhfSharpSymLottery3_fullSupport hb0 hb1)

/-- Change only the `x` versus `y` margin by `δ`, together with the opposite
entry forced by skew-symmetry. -/
noncomputable def improvePairMargin
    {α : Type*} [DecidableEq α]
    (M : α → α → ℝ) (x y : α) (δ : ℝ) : α → α → ℝ :=
  fun i j =>
    if i = x ∧ j = y then M i j + δ
    else if i = y ∧ j = x then M i j - δ
    else M i j

lemma improvePairMargin_zero
    {α : Type*} [DecidableEq α]
    (M : α → α → ℝ) (x y : α) :
    improvePairMargin M x y 0 = M := by
  funext i j
  by_cases hij : i = x ∧ j = y
  · simp [improvePairMargin, hij]
  · by_cases hji : i = y ∧ j = x
    · simp [improvePairMargin, hji]
    · simp [improvePairMargin, hij, hji]

lemma improvePairMargin_normalized
    {α : Type*} [DecidableEq α]
    {M : α → α → ℝ} {x y : α} {δ : ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hxy : x ≠ y)
    (hδ0 : 0 ≤ δ)
    (hδle : δ ≤ 1 - M x y) :
    IsNormalizedMarginMatrix (improvePairMargin M x y δ) := by
  classical
  refine ⟨?diag, ?skew, ?bound⟩
  · intro i
    have hnot₁ : ¬ (i = x ∧ i = y) := by
      intro h
      exact hxy (h.1.symm.trans h.2)
    have hnot₂ : ¬ (i = y ∧ i = x) := by
      intro h
      exact hxy (h.2.symm.trans h.1)
    simp [improvePairMargin, hnot₁, hnot₂, hM.1 i]
  · intro i j
    by_cases hij : i = x ∧ j = y
    · obtain ⟨hix, hjy⟩ := hij
      subst i
      subst j
      simp [improvePairMargin, hxy, hM.2.1 x y]
      ring
    · by_cases hji : i = y ∧ j = x
      · obtain ⟨hiy, hjx⟩ := hji
        subst i
        subst j
        simp [improvePairMargin, hxy, hM.2.1 x y]
        ring
      · have hnot_xy_swap : ¬ (j = x ∧ i = y) := by
          intro h
          exact hji ⟨h.2, h.1⟩
        have hnot_yx_swap : ¬ (j = y ∧ i = x) := by
          intro h
          exact hij ⟨h.2, h.1⟩
        simp [improvePairMargin, hij, hji, hnot_xy_swap, hnot_yx_swap,
          hM.2.1 i j]
  · intro i j
    have hchanged : |M x y + δ| ≤ (1 : ℝ) := by
      have hbase := abs_le.mp (hM.2.2 x y)
      rw [abs_le]
      constructor <;> linarith
    by_cases hij : i = x ∧ j = y
    · obtain ⟨hix, hjy⟩ := hij
      subst i
      subst j
      simpa [improvePairMargin, hxy] using hchanged
    · by_cases hji : i = y ∧ j = x
      · obtain ⟨hiy, hjx⟩ := hji
        subst i
        subst j
        have hchanged_neg : |-M x y - δ| ≤ (1 : ℝ) := by
          have hrew : -M x y - δ = -(M x y + δ) := by ring
          rw [hrew, abs_neg]
          exact hchanged
        simpa [improvePairMargin, hxy, hM.2.1 x y] using hchanged_neg
      · simp [improvePairMargin, hij, hji]
        exact hM.2.2 i j

/-- Moving weight `s/2` from `yxz` to `xyz` increases only the `x`-against-`y`
margin, by exactly `s`. -/
lemma nlhfSharpLinearImproved_eq_improvePairMargin (η s : ℝ) :
    weightedScoreProfileMargin (nlhfSharpLinearWeights3Improved η s)
        nlhfSharpLinearScore3 =
      improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 s := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [weightedScoreProfileMargin, nlhfSharpLinearWeights3Improved,
      nlhfSharpLinearScore3, nlhfSharpLinearMargin3, improvePairMargin,
      scoreMarginSign, scoreMarginSignReal] <;>
    ring

/-- Denominator-cleared finite-profile form of the improved linear-order
sharpness matrix. -/
lemma nlhfSharpLinearImproved_eq_scoreProfile_of_fiber_weights
    {W : Type*} [Fintype W] [Nonempty W]
    (assign : W → Fin 2) {η s : ℝ}
    (hw : ∀ v : Fin 2,
      nlhfSharpLinearWeights3Improved η s v =
        ((Finset.univ.filter (fun u : W => assign u = v)).card : ℝ) /
          (Fintype.card W : ℝ)) :
    scoreProfileMargin (fun u : W => nlhfSharpLinearScore3 (assign u)) =
      improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 s := by
  rw [← nlhfSharpLinearImproved_eq_improvePairMargin η s]
  exact (weightedScoreProfileMargin_eq_scoreProfileMargin_of_fiber_weights
    assign nlhfSharpLinearScore3 (nlhfSharpLinearWeights3Improved η s) hw).symm

/-- Concrete denominator-cleared finite-profile form of the improved
linear-order sharpness matrix: `r` voters have been moved from the `yxz` block
to the `xyz` block. -/
lemma nlhfSharpLinearImproved_eq_twoBlockScoreProfile
    (n k r : ℕ) (hr : r ≤ k) (hN : 0 < n + k) :
    scoreProfileMargin
      (fun u : Sum (Fin (n + r)) (Fin (k - r)) =>
        nlhfSharpLinearScore3 (twoBlockAssign (n + r) (k - r) u)) =
      improvePairMargin
        (nlhfSharpLinearMargin3 (2 * (k : ℝ) / (n + k : ℝ))) 0 1
        (2 * (r : ℝ) / (n + k : ℝ)) := by
  have htotal : 0 < n + r + (k - r) := by omega
  have hnonempty : Nonempty (Sum (Fin (n + r)) (Fin (k - r))) := by
    rcases Nat.eq_zero_or_pos (n + r) with hn | hn
    · rcases Nat.eq_zero_or_pos (k - r) with hk | hk
      · simp [hn, hk] at htotal
      · exact ⟨Sum.inr ⟨0, hk⟩⟩
    · exact ⟨Sum.inl ⟨0, hn⟩⟩
  letI : Nonempty (Sum (Fin (n + r)) (Fin (k - r))) := hnonempty
  exact nlhfSharpLinearImproved_eq_scoreProfile_of_fiber_weights
    (twoBlockAssign (n + r) (k - r))
    (nlhfSharpLinearWeights3Improved_twoBlock_fiber_weights n k r hr hN)

/-- Moving the single `yxz` voter to `xyz` realizes the improved matrix with
improvement size `s = 2/N`. -/
lemma nlhfSharpLinearImproved_eq_oneYxzMovedScoreProfile
    (N : ℕ) (hN : 0 < N) :
    scoreProfileMargin
      (fun u : Sum (Fin ((N - 1) + 1)) (Fin (1 - 1)) =>
        nlhfSharpLinearScore3 (twoBlockAssign ((N - 1) + 1) (1 - 1) u)) =
      improvePairMargin (nlhfSharpLinearMargin3 (2 / (N : ℝ))) 0 1
        (2 / (N : ℝ)) := by
  have htotal : 0 < (N - 1) + 1 := by omega
  have hden_nat : (N - 1) + 1 = N := by omega
  have hden_real : (((N - 1) + 1 : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast hden_nat
  have hden_real' : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast hden_nat
  have h := nlhfSharpLinearImproved_eq_twoBlockScoreProfile
    (N - 1) 1 1 (by omega) htotal
  simpa [hden_real, hden_real'] using h

/-- The replicated old finite profile used to denominator-clear the
linear-order low-temperature converse: `(N - 1) * (m + 1)` voters have ballot
type `xyz`, while `m + 1` voters have ballot type `yxz`. -/
noncomputable def nlhfSharpLinearReplicatedOldScore3
    (N m : ℕ) :
    Sum (Fin ((N - 1) * (m + 1))) (Fin (m + 1)) → Fin 3 → ℝ :=
  fun u => nlhfSharpLinearScore3
    (twoBlockAssign ((N - 1) * (m + 1)) (m + 1) u)

/-- The replicated improved finite profile obtained by moving one copied
`yxz` voter in `nlhfSharpLinearReplicatedOldScore3 N m` to `xyz`. -/
noncomputable def nlhfSharpLinearReplicatedMovedScore3
    (N m : ℕ) :
    Sum (Fin (((N - 1) * (m + 1)) + 1)) (Fin ((m + 1) - 1)) →
      Fin 3 → ℝ :=
  fun u => nlhfSharpLinearScore3
    (twoBlockAssign (((N - 1) * (m + 1)) + 1) ((m + 1) - 1) u)

lemma nlhfSharpLinearReplicatedOldScore3_linear (N m : ℕ) :
    IsLinearScoreProfile (nlhfSharpLinearReplicatedOldScore3 N m) :=
  nlhfSharpLinearScore3_assigned_linear
    (twoBlockAssign ((N - 1) * (m + 1)) (m + 1))

lemma nlhfSharpLinearReplicatedMovedScore3_linear (N m : ℕ) :
    IsLinearScoreProfile (nlhfSharpLinearReplicatedMovedScore3 N m) :=
  nlhfSharpLinearScore3_assigned_linear
    (twoBlockAssign (((N - 1) * (m + 1)) + 1) ((m + 1) - 1))

/-- Replicating the one-`yxz` profile preserves the old sharpness margin
parameter `eta = 2 / N`. -/
lemma nlhfSharpLinearMargin3_eq_replicatedOldScoreProfile
    (N m : ℕ) (hN : 0 < N) :
    scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m) =
      nlhfSharpLinearMargin3 (2 / (N : ℝ)) := by
  have hden_nat : (N - 1) * (m + 1) + (m + 1) = N * (m + 1) := by
    calc
      (N - 1) * (m + 1) + (m + 1)
          = (N - 1) * (m + 1) + 1 * (m + 1) := by simp
      _ = ((N - 1) + 1) * (m + 1) :=
          (Nat.add_mul (N - 1) 1 (m + 1)).symm
      _ = N * (m + 1) := by rw [Nat.sub_add_cancel hN]
  have htotal : 0 < (N - 1) * (m + 1) + (m + 1) := by
    rw [hden_nat]
    exact Nat.mul_pos hN (Nat.succ_pos m)
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hNpos : (0 : ℝ) < (N : ℕ) := by exact_mod_cast hN
  have hden_real :
      ((N - 1 : ℕ) : ℝ) * ((m : ℝ) + 1) + ((m : ℝ) + 1) =
        (N : ℝ) * ((m : ℝ) + 1) := by
    exact_mod_cast hden_nat
  have hparam :
      2 * ((m : ℝ) + 1) /
          (((N - 1 : ℕ) : ℝ) * ((m : ℝ) + 1) + ((m : ℝ) + 1)) =
        2 / (N : ℝ) := by
    rw [hden_real]
    field_simp [ne_of_gt hNpos, ne_of_gt hmpos]
  have h := nlhfSharpLinearMargin3_eq_twoBlockScoreProfile
    ((N - 1) * (m + 1)) (m + 1) htotal
  simpa [nlhfSharpLinearReplicatedOldScore3, hparam] using h

/-- Moving one copied `yxz` voter realizes the small improvement
`s = 2 / (N * (m + 1))` while keeping the old margin parameter `2 / N`. -/
lemma nlhfSharpLinearImproved_eq_replicatedMovedScoreProfile
    (N m : ℕ) (hN : 0 < N) :
    scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m) =
      improvePairMargin (nlhfSharpLinearMargin3 (2 / (N : ℝ))) 0 1
        (2 / ((N : ℝ) * ((m : ℝ) + 1))) := by
  have hden_nat : (N - 1) * (m + 1) + (m + 1) = N * (m + 1) := by
    calc
      (N - 1) * (m + 1) + (m + 1)
          = (N - 1) * (m + 1) + 1 * (m + 1) := by simp
      _ = ((N - 1) + 1) * (m + 1) :=
          (Nat.add_mul (N - 1) 1 (m + 1)).symm
      _ = N * (m + 1) := by rw [Nat.sub_add_cancel hN]
  have htotal : 0 < (N - 1) * (m + 1) + (m + 1) := by
    rw [hden_nat]
    exact Nat.mul_pos hN (Nat.succ_pos m)
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hNpos : (0 : ℝ) < (N : ℕ) := by exact_mod_cast hN
  have hden_real :
      ((N - 1 : ℕ) : ℝ) * ((m : ℝ) + 1) + ((m : ℝ) + 1) =
        (N : ℝ) * ((m : ℝ) + 1) := by
    exact_mod_cast hden_nat
  have hparam :
      2 * ((m : ℝ) + 1) /
          (((N - 1 : ℕ) : ℝ) * ((m : ℝ) + 1) + ((m : ℝ) + 1)) =
        2 / (N : ℝ) := by
    rw [hden_real]
    field_simp [ne_of_gt hNpos, ne_of_gt hmpos]
  have hdelta :
      2 / (((N - 1 : ℕ) : ℝ) * ((m : ℝ) + 1) + ((m : ℝ) + 1)) =
        2 / ((N : ℝ) * ((m : ℝ) + 1)) := by
    rw [hden_real]
  have h := nlhfSharpLinearImproved_eq_twoBlockScoreProfile
    ((N - 1) * (m + 1)) (m + 1) 1 (by omega) htotal
  simpa [nlhfSharpLinearReplicatedMovedScore3, hparam, hdelta] using h

/-- The improved linear-order sharpness matrix is again a weighted
linear-order profile whenever `0 <= s <= η`. -/
lemma nlhfSharpLinearImproved_normalized_from_profile
    {η s : ℝ} (hη2 : η ≤ 2)
    (hs0 : 0 ≤ s) (hsη : s ≤ η) :
    IsNormalizedMarginMatrix
      (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 s) := by
  rw [← nlhfSharpLinearImproved_eq_improvePairMargin η s]
  exact weightedScoreProfileMargin_normalized nlhfSharpLinearScore3
    (nlhfSharpLinearWeights3Improved_nonneg hη2 hs0 hsη)
    (nlhfSharpLinearWeights3Improved_sum η s)

lemma improvePairMargin_isImprovement
    {α : Type*} [DecidableEq α]
    {M : α → α → ℝ} {x y : α} {δ : ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hxy : x ≠ y)
    (hδ0 : 0 ≤ δ)
    (hδle : δ ≤ 1 - M x y) :
    IsImprovementOf M (improvePairMargin M x y δ) x := by
  classical
  have hM' : IsNormalizedMarginMatrix (improvePairMargin M x y δ) :=
    improvePairMargin_normalized hM hxy hδ0 hδle
  refine ⟨?improves, ?skew, ?fixed⟩
  · intro z _hzx
    by_cases hzy : z = y
    · subst z
      simp [improvePairMargin]
      linarith
    · simp [improvePairMargin, hxy, hzy]
  · intro z _hzx
    exact hM'.2.1 x z
  · intro i j hix hjx
    have hnot₁ : ¬ (i = x ∧ j = y) := by
      intro h
      exact hix h.1
    have hnot₂ : ¬ (i = y ∧ j = x) := by
      intro h
      exact hjx h.2
    simp [improvePairMargin, hnot₁, hnot₂]

/-- The same weighted-profile change is an improvement of `x` against `y`. -/
lemma nlhfSharpLinearImproved_isImprovement_from_profile
    {η s : ℝ} (hη0 : 0 ≤ η) (hη2 : η ≤ 2)
    (hs0 : 0 ≤ s) (hsη : s ≤ η) :
    IsImprovementOf (nlhfSharpLinearMargin3 η)
      (weightedScoreProfileMargin (nlhfSharpLinearWeights3Improved η s)
        nlhfSharpLinearScore3) 0 := by
  rw [nlhfSharpLinearImproved_eq_improvePairMargin]
  refine improvePairMargin_isImprovement
    (nlhfSharpLinearMargin3_normalized hη0 hη2) (by decide) hs0 ?_
  simpa [nlhfSharpLinearMargin3] using hsη

lemma exists_positive_improvement_size
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ η := by
  refine ⟨η / 2, by linarith, by linarith⟩

lemma nlhfSharpAll_improve_xy_normalized
    {η δ : ℝ}
    (hη0 : 0 ≤ η) (hη2 : η ≤ 2)
    (hδ0 : 0 ≤ δ) (hδle : δ ≤ η) :
    IsNormalizedMarginMatrix
      (improvePairMargin (nlhfSharpAllMargin3 η) 0 1 δ) := by
  refine improvePairMargin_normalized
    (nlhfSharpAllMargin3_normalized hη0 hη2)
    (by decide) hδ0 ?_
  simpa [nlhfSharpAllMargin3] using hδle

lemma nlhfSharpAll_improve_xy_isImprovement
    {η δ : ℝ}
    (hη0 : 0 ≤ η) (hη2 : η ≤ 2)
    (hδ0 : 0 ≤ δ) (hδle : δ ≤ η) :
    IsImprovementOf (nlhfSharpAllMargin3 η)
      (improvePairMargin (nlhfSharpAllMargin3 η) 0 1 δ) 0 := by
  refine improvePairMargin_isImprovement
    (nlhfSharpAllMargin3_normalized hη0 hη2)
    (by decide) hδ0 ?_
  simpa [nlhfSharpAllMargin3] using hδle

lemma nlhfSharpLinear_improve_xy_normalized
    {η δ : ℝ}
    (hη0 : 0 ≤ η) (hη2 : η ≤ 2)
    (hδ0 : 0 ≤ δ) (hδle : δ ≤ η) :
    IsNormalizedMarginMatrix
      (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ) := by
  refine improvePairMargin_normalized
    (nlhfSharpLinearMargin3_normalized hη0 hη2)
    (by decide) hδ0 ?_
  simpa [nlhfSharpLinearMargin3] using hδle

lemma nlhfSharpLinear_improve_xy_isImprovement
    {η δ : ℝ}
    (hη0 : 0 ≤ η) (hη2 : η ≤ 2)
    (hδ0 : 0 ≤ δ) (hδle : δ ≤ η) :
    IsImprovementOf (nlhfSharpLinearMargin3 η)
      (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ) 0 := by
  refine improvePairMargin_isImprovement
    (nlhfSharpLinearMargin3_normalized hη0 hη2)
    (by decide) hδ0 ?_
  simpa [nlhfSharpLinearMargin3] using hδle

lemma nlhfSharpLinear_oneYxzMoved_isImprovement
    (N : ℕ) (hN : 0 < N) :
    IsImprovementOf
      (scoreProfileMargin
        (fun u : Sum (Fin (N - 1)) (Fin 1) =>
          nlhfSharpLinearScore3 (twoBlockAssign (N - 1) 1 u)))
      (scoreProfileMargin
        (fun u : Sum (Fin ((N - 1) + 1)) (Fin (1 - 1)) =>
          nlhfSharpLinearScore3 (twoBlockAssign ((N - 1) + 1) (1 - 1) u)))
      0 := by
  let η : ℝ := 2 / (N : ℝ)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hη0 : 0 ≤ η := by
    dsimp [η]
    positivity
  have hη2 : η ≤ 2 := by
    dsimp [η]
    rw [div_le_iff₀ hNreal]
    have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hδle : η ≤ η := le_rfl
  rw [nlhfSharpLinearMargin3_eq_oneYxzScoreProfile N hN]
  rw [nlhfSharpLinearImproved_eq_oneYxzMovedScoreProfile N hN]
  exact nlhfSharpLinear_improve_xy_isImprovement hη0 hη2 hη0 hδle

lemma exists_nlhfSharpAll_positive_improvement
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ,
      0 < δ ∧
      IsNormalizedMarginMatrix
        (improvePairMargin (nlhfSharpAllMargin3 η) 0 1 δ) ∧
      IsImprovementOf (nlhfSharpAllMargin3 η)
        (improvePairMargin (nlhfSharpAllMargin3 η) 0 1 δ) 0 := by
  rcases exists_positive_improvement_size hη0 with ⟨δ, hδpos, hδle⟩
  have hη_nonneg : 0 ≤ η := hη0.le
  have hη_two : η ≤ 2 := by linarith
  exact ⟨δ, hδpos,
    nlhfSharpAll_improve_xy_normalized hη_nonneg hη_two hδpos.le hδle,
    nlhfSharpAll_improve_xy_isImprovement hη_nonneg hη_two hδpos.le hδle⟩

lemma exists_nlhfSharpLinear_positive_improvement
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ,
      0 < δ ∧
      IsNormalizedMarginMatrix
        (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ) ∧
      IsImprovementOf (nlhfSharpLinearMargin3 η)
        (improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ) 0 := by
  rcases exists_positive_improvement_size hη0 with ⟨δ, hδpos, hδle⟩
  have hη_nonneg : 0 ≤ η := hη0.le
  have hη_two : η ≤ 2 := by linarith
  exact ⟨δ, hδpos,
    nlhfSharpLinear_improve_xy_normalized hη_nonneg hη_two hδpos.le hδle,
    nlhfSharpLinear_improve_xy_isImprovement hη_nonneg hη_two hδpos.le hδle⟩

theorem violatesProbabilisticMonotonicity_of_pair_improvement_drop
    {α : Type*} [Fintype α] [DecidableEq α]
    {F : MatrixRule α}
    {M : α → α → ℝ} {ρ : α → ℝ} {x y : α} {δ : ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hxy : x ≠ y)
    (hδ0 : 0 ≤ δ)
    (hδle : δ ≤ 1 - M x y)
    (hdrop :
      F (improvePairMargin M x y δ) ρ x < F M ρ x) :
    ViolatesProbabilisticMonotonicity F := by
  intro hmono
  exact not_lt_of_ge
    (hmono M (improvePairMargin M x y δ) ρ x
      hM
      (improvePairMargin_normalized hM hxy hδ0 hδle)
      hρ
      (improvePairMargin_isImprovement hM hxy hδ0 hδle))
    hdrop

lemma exists_nat_two_div_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ (2 : ℝ) / N < ε := by
  rcases exists_nat_gt ((2 : ℝ) / ε) with ⟨N, hNgt⟩
  have hNposR : (0 : ℝ) < N := by
    have htwo : (0 : ℝ) < 2 / ε := div_pos (by norm_num) hε
    nlinarith
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hmul : (2 : ℝ) < ε * N := by
    rw [div_lt_iff₀ hε] at hNgt
    nlinarith
  have hdiv : (2 : ℝ) / N < ε := by
    rw [div_lt_iff₀ hNposR]
    nlinarith
  exact ⟨N, hNpos, hdiv⟩

/-- Explicit small-parameter choice for the all-profile sharpness construction:
if `λ > 4/3`, then one can choose positive `b, η` with
`a = (1 - b)/2` and `λ a^2 (3 - η) > 1`. -/
lemma exists_threeCandidateParams_of_lambda_gt_four_thirds
    {lam : ℝ} (hlam : (4 : ℝ) / 3 < lam) :
    ∃ b η a d : ℝ,
      0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
      a = (1 - b) / 2 ∧ d = 3 - η ∧
      0 < a ∧ 0 < d ∧ 1 < lam * a ^ 2 * d := by
  let b : ℝ := (3 * lam - 4) / (16 * lam)
  let η : ℝ := b
  let a : ℝ := (1 - b) / 2
  let d : ℝ := 3 - η
  have hlam_pos : 0 < lam := by nlinarith
  have hgap_pos : 0 < 3 * lam - 4 := by nlinarith
  have hden_pos : 0 < 16 * lam := by positivity
  have hb_pos : 0 < b := by
    dsimp [b]
    exact div_pos hgap_pos hden_pos
  have hb_lt_one : b < 1 := by
    dsimp [b]
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  have heta_pos : 0 < η := by simpa [η] using hb_pos
  have heta_lt_one : η < 1 := by
    dsimp [η, b]
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith
  have hd_pos : 0 < d := by
    dsimp [d]
    nlinarith
  have hsq_lower : 1 - 2 * b ≤ (1 - b) ^ 2 := by
    nlinarith [sq_nonneg b]
  have hd_nonneg : 0 ≤ 3 - η := by nlinarith
  have hprod_lower :
      lam * (1 - 2 * b) * (3 - η) ≤ lam * (1 - b) ^ 2 * (3 - η) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsq_lower hd_nonneg) hlam_pos.le
  have hlower_gt : 4 < lam * (1 - 2 * b) * (3 - η) := by
    dsimp [b, η]
    field_simp [hlam_pos.ne']
    nlinarith
  have hmain : 4 < lam * (1 - b) ^ 2 * (3 - η) :=
    lt_of_lt_of_le hlower_gt hprod_lower
  have hcrit : 1 < lam * a ^ 2 * d := by
    dsimp [a, d]
    nlinarith
  exact ⟨b, η, a, d, hb_pos, hb_lt_one, heta_pos, heta_lt_one,
    rfl, rfl, ha_pos, hd_pos, hcrit⟩

/-- Explicit small-parameter choice for the linear-order sharpness construction:
if `λ > 4`, then one can choose positive `b, η` with
`a = (1 - b)/2` and `λ a^2 (1 - η) > 1`. -/
lemma exists_linearOrderParams_of_lambda_gt_four
    {lam : ℝ} (hlam : (4 : ℝ) < lam) :
    ∃ b η a d : ℝ,
      0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
      a = (1 - b) / 2 ∧ d = 1 - η ∧
      0 < a ∧ 0 < d ∧ 1 < lam * a ^ 2 * d := by
  let b : ℝ := (lam - 4) / (8 * lam)
  let η : ℝ := b
  let a : ℝ := (1 - b) / 2
  let d : ℝ := 1 - η
  have hlam_pos : 0 < lam := by nlinarith
  have hgap_pos : 0 < lam - 4 := by nlinarith
  have hden_pos : 0 < 8 * lam := by positivity
  have hb_pos : 0 < b := by
    dsimp [b]
    exact div_pos hgap_pos hden_pos
  have hb_lt_one : b < 1 := by
    dsimp [b]
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  have heta_pos : 0 < η := by simpa [η] using hb_pos
  have heta_lt_one : η < 1 := by
    dsimp [η, b]
    rw [div_lt_iff₀ hden_pos]
    nlinarith
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith
  have hd_pos : 0 < d := by
    dsimp [d]
    nlinarith
  have hsq_lower : 1 - 2 * b ≤ (1 - b) ^ 2 := by
    nlinarith [sq_nonneg b]
  have hd_nonneg : 0 ≤ 1 - η := by nlinarith
  have hprod_lower :
      lam * (1 - 2 * b) * (1 - η) ≤ lam * (1 - b) ^ 2 * (1 - η) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hsq_lower hd_nonneg) hlam_pos.le
  have hlower_gt : 4 < lam * (1 - 2 * b) * (1 - η) := by
    dsimp [b, η]
    field_simp [hlam_pos.ne']
    nlinarith
  have hmain : 4 < lam * (1 - b) ^ 2 * (1 - η) :=
    lt_of_lt_of_le hlower_gt hprod_lower
  have hcrit : 1 < lam * a ^ 2 * d := by
    dsimp [a, d]
    nlinarith
  exact ⟨b, η, a, d, hb_pos, hb_lt_one, heta_pos, heta_lt_one,
    rfl, rfl, ha_pos, hd_pos, hcrit⟩

/-- Natural-denominator version of the linear-order sharpness parameter
choice.  This is the arithmetic input used with the two-block finite electorate:
the sharpness parameter can be taken to be `2 / N` for a natural `N`. -/
lemma exists_linearOrderFiniteEtaParams_of_lambda_gt_four
    {lam : ℝ} (hlam : (4 : ℝ) < lam) :
    ∃ N : ℕ, ∃ b η a d : ℝ,
      0 < N ∧ 0 < b ∧ b < 1 ∧
      η = 2 / (N : ℝ) ∧ 0 < η ∧ η < 1 ∧
      a = (1 - b) / 2 ∧ d = 1 - η ∧
      0 < a ∧ 0 < d ∧ 2 * a + b = 1 ∧
      1 < lam * a ^ 2 * d := by
  rcases exists_linearOrderParams_of_lambda_gt_four hlam with
    ⟨b, η0, a, d0, hb0, hb1, hη0, hη1, ha, hd0, ha0, _hd0pos, hcrit0⟩
  rcases exists_nat_two_div_lt hη0 with ⟨Nnat, hNnat0, hNsmall⟩
  let η : ℝ := 2 / (Nnat : ℝ)
  let d : ℝ := 1 - η
  have hηeq : η = 2 / (Nnat : ℝ) := rfl
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hηltη0 : η < η0 := by
    simpa [η] using hNsmall
  have hηlt1 : η < 1 := lt_trans hηltη0 hη1
  have hd : d = 1 - η := rfl
  have hdpos : 0 < d := by
    dsimp [d]
    linarith
  have hd0eq : d0 = 1 - η0 := hd0
  have hdgt : d0 < d := by
    dsimp [d]
    rw [hd0eq]
    linarith
  have hcoef : 0 < lam * a ^ 2 := by
    have hlampos : 0 < lam := by nlinarith
    positivity
  have hcrit : 1 < lam * a ^ 2 * d := by
    have hlt : lam * a ^ 2 * d0 < lam * a ^ 2 * d :=
      mul_lt_mul_of_pos_left hdgt hcoef
    exact lt_trans hcrit0 hlt
  have hnorm : 2 * a + b = 1 := by
    rw [ha]
    ring
  exact ⟨Nnat, b, η, a, d, hNnat0, hb0, hb1, hηeq, hηpos, hηlt1,
    ha, hd, ha0, hdpos, hnorm, hcrit⟩

/-- Scalar sharpness package for the all-profile threshold, starting from the
paper's temperature hypothesis `τ < 3/8`. -/
lemma exists_threeCandidateSharpnessScalar_of_tau_lt_three_eighths
    {τ : ℝ} (hτpos : 0 < τ) (hτ : τ < (3 : ℝ) / 8) :
    ∃ b η a d : ℝ,
      0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
      a = (1 - b) / 2 ∧ d = 3 - η ∧
      0 < a ∧ 0 < d ∧ 2 * a + b = 1 ∧
      2 + b / a - nlhfLambda τ * d * a < 0 := by
  have hlam : (4 : ℝ) / 3 < nlhfLambda τ :=
    four_thirds_lt_nlhfLambda_of_tau_lt_three_eighths hτpos hτ
  rcases exists_threeCandidateParams_of_lambda_gt_four_thirds hlam with
    ⟨b, η, a, d, hbpos, hblt, hetapos, hetalt, haeq, hdeq,
      hapos, hdpos, hcrit⟩
  have hnorm : 2 * a + b = 1 := by
    rw [haeq]
    ring
  have hlimit :
      2 + b / a - nlhfLambda τ * d * a < 0 :=
    threeCandidateSecant_limit_expression_negative hapos hnorm hcrit
  exact ⟨b, η, a, d, hbpos, hblt, hetapos, hetalt, haeq, hdeq,
    hapos, hdpos, hnorm, hlimit⟩

/-- Scalar sharpness package for the linear-order threshold, starting from the
paper's temperature hypothesis `τ < 1/8`. -/
lemma exists_linearOrderSharpnessScalar_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτ : τ < (1 : ℝ) / 8) :
    ∃ b η a d : ℝ,
      0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
      a = (1 - b) / 2 ∧ d = 1 - η ∧
      0 < a ∧ 0 < d ∧ 2 * a + b = 1 ∧
      2 + b / a - nlhfLambda τ * d * a < 0 := by
  have hlam : (4 : ℝ) < nlhfLambda τ :=
    four_lt_nlhfLambda_of_tau_lt_one_eighth hτpos hτ
  rcases exists_linearOrderParams_of_lambda_gt_four hlam with
    ⟨b, η, a, d, hbpos, hblt, hetapos, hetalt, haeq, hdeq,
      hapos, hdpos, hcrit⟩
  have hnorm : 2 * a + b = 1 := by
    rw [haeq]
    ring
  have hlimit :
      2 + b / a - nlhfLambda τ * d * a < 0 :=
    threeCandidateSecant_limit_expression_negative hapos hnorm hcrit
  exact ⟨b, η, a, d, hbpos, hblt, hetapos, hetalt, haeq, hdeq,
    hapos, hdpos, hnorm, hlimit⟩

/-- Natural-denominator scalar sharpness package for the linear-order
threshold.  This is the finite-profile version of
`exists_linearOrderSharpnessScalar_of_tau_lt_one_eighth`: the margin parameter
is `eta = 2/N`, matching the two-block electorate with one `yxz` voter and
`N - 1` `xyz` voters. -/
lemma exists_linearOrderFiniteEtaSharpnessScalar_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτ : τ < (1 : ℝ) / 8) :
    ∃ N : ℕ, ∃ b η a d : ℝ,
      0 < N ∧ 0 < b ∧ b < 1 ∧
      η = 2 / (N : ℝ) ∧ 0 < η ∧ η < 1 ∧
      a = (1 - b) / 2 ∧ d = 1 - η ∧
      0 < a ∧ 0 < d ∧ 2 * a + b = 1 ∧
      2 + b / a - nlhfLambda τ * d * a < 0 := by
  have hlam : (4 : ℝ) < nlhfLambda τ :=
    four_lt_nlhfLambda_of_tau_lt_one_eighth hτpos hτ
  rcases exists_linearOrderFiniteEtaParams_of_lambda_gt_four hlam with
    ⟨N, b, η, a, d, hN, hbpos, hblt, heta, hetapos, hetalt, haeq, hdeq,
      hapos, hdpos, hnorm, hcrit⟩
  have hlimit :
      2 + b / a - nlhfLambda τ * d * a < 0 :=
    threeCandidateSecant_limit_expression_negative hapos hnorm hcrit
  exact ⟨N, b, η, a, d, hN, hbpos, hblt, heta, hetapos, hetalt, haeq, hdeq,
    hapos, hdpos, hnorm, hlimit⟩

/-- Natural-denominator version of the all-profile sharpness parameter
choice.  This is the arithmetic input used with the paper's transitive
pair-block electorate: the sharpness parameter can be taken to be `2 / N` for
a natural `N`.  Because `d = 3 - η` increases as `η` decreases, replacing the
parameter of `exists_threeCandidateParams_of_lambda_gt_four_thirds` by a
smaller natural-denominator value preserves the criticality inequality. -/
lemma exists_threeCandidateFiniteEtaParams_of_lambda_gt_four_thirds
    {lam : ℝ} (hlam : (4 : ℝ) / 3 < lam) :
    ∃ N : ℕ, ∃ b η a d : ℝ,
      0 < N ∧ 0 < b ∧ b < 1 ∧
      η = 2 / (N : ℝ) ∧ 0 < η ∧ η < 1 ∧
      a = (1 - b) / 2 ∧ d = 3 - η ∧
      0 < a ∧ 0 < d ∧ 2 * a + b = 1 ∧
      1 < lam * a ^ 2 * d := by
  rcases exists_threeCandidateParams_of_lambda_gt_four_thirds hlam with
    ⟨b, η0, a, d0, hb0, hb1, hη0, hη1, ha, hd0, ha0, _hd0pos, hcrit0⟩
  rcases exists_nat_two_div_lt hη0 with ⟨Nnat, hNnat0, hNsmall⟩
  have hNposR : (0 : ℝ) < (Nnat : ℝ) := by exact_mod_cast hNnat0
  let η : ℝ := 2 / (Nnat : ℝ)
  let d : ℝ := 3 - η
  have hηeq : η = 2 / (Nnat : ℝ) := rfl
  have hηpos : 0 < η := by
    dsimp [η]
    exact div_pos (by norm_num) hNposR
  have hηltη0 : η < η0 := by
    simpa [η] using hNsmall
  have hηlt1 : η < 1 := lt_trans hηltη0 hη1
  have hd : d = 3 - η := rfl
  have hdpos : 0 < d := by
    dsimp [d]
    linarith
  have hd0eq : d0 = 3 - η0 := hd0
  have hdgt : d0 < d := by
    dsimp [d]
    rw [hd0eq]
    linarith
  have hcoef : 0 < lam * a ^ 2 := by
    have hlampos : 0 < lam := by linarith
    positivity
  have hcrit : 1 < lam * a ^ 2 * d := by
    have hlt : lam * a ^ 2 * d0 < lam * a ^ 2 * d :=
      mul_lt_mul_of_pos_left hdgt hcoef
    exact lt_trans hcrit0 hlt
  have hnorm : 2 * a + b = 1 := by
    rw [ha]
    ring
  exact ⟨Nnat, b, η, a, d, hNnat0, hb0, hb1, hηeq, hηpos, hηlt1,
    ha, hd, ha0, hdpos, hnorm, hcrit⟩

/-- Natural-denominator scalar sharpness package for the all-profile `3/8`
threshold.  The margin parameter is `eta = 2/N`, matching the paper's
transitive electorate in which `N` voters compare each pair and exactly
`m + 1` of the `x`-versus-`y` voters rank `y` above `x`. -/
lemma exists_threeCandidateFiniteEtaSharpnessScalar_of_tau_lt_three_eighths
    {τ : ℝ} (hτpos : 0 < τ) (hτ : τ < (3 : ℝ) / 8) :
    ∃ N : ℕ, ∃ b η a d : ℝ,
      0 < N ∧ 0 < b ∧ b < 1 ∧
      η = 2 / (N : ℝ) ∧ 0 < η ∧ η < 1 ∧
      a = (1 - b) / 2 ∧ d = 3 - η ∧
      0 < a ∧ 0 < d ∧ 2 * a + b = 1 ∧
      2 + b / a - nlhfLambda τ * d * a < 0 := by
  have hlam : (4 : ℝ) / 3 < nlhfLambda τ :=
    four_thirds_lt_nlhfLambda_of_tau_lt_three_eighths hτpos hτ
  rcases exists_threeCandidateFiniteEtaParams_of_lambda_gt_four_thirds hlam with
    ⟨N, b, η, a, d, hN, hbpos, hblt, heta, hetapos, hetalt, haeq, hdeq,
      hapos, hdpos, hnorm, hcrit⟩
  have hlimit :
      2 + b / a - nlhfLambda τ * d * a < 0 :=
    threeCandidateSecant_limit_expression_negative hapos hnorm hcrit
  exact ⟨N, b, η, a, d, hN, hbpos, hblt, heta, hetapos, hetalt, haeq, hdeq,
    hapos, hdpos, hnorm, hlimit⟩

/-- Finite-profile data for the linear-order low-temperature converse.  The
profile has one `yxz` voter among `N` total voters, and the improved profile is
obtained by moving that voter to `xyz`. -/
lemma exists_linearOrderFiniteProfileSharpnessData_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτ : τ < (1 : ℝ) / 8) :
    ∃ N : ℕ, ∃ b a d : ℝ,
      0 < N ∧ 0 < b ∧ b < 1 ∧
      0 < a ∧ 0 < d ∧ 2 * a + b = 1 ∧
      2 + b / a - nlhfLambda τ * d * a < 0 ∧
      IsImprovementOf
        (scoreProfileMargin
          (fun u : Sum (Fin (N - 1)) (Fin 1) =>
            nlhfSharpLinearScore3 (twoBlockAssign (N - 1) 1 u)))
        (scoreProfileMargin
          (fun u : Sum (Fin ((N - 1) + 1)) (Fin (1 - 1)) =>
            nlhfSharpLinearScore3
              (twoBlockAssign ((N - 1) + 1) (1 - 1) u)))
        0 := by
  rcases exists_linearOrderFiniteEtaSharpnessScalar_of_tau_lt_one_eighth
      hτpos hτ with
    ⟨N, b, _η, a, d, hN, hbpos, hblt, _heta, _hetapos, _hetalt,
      _haeq, _hdeq, hapos, hdpos, hnorm, hlimit⟩
  exact ⟨N, b, a, d, hN, hbpos, hblt, hapos, hdpos, hnorm, hlimit,
    nlhfSharpLinear_oneYxzMoved_isImprovement N hN⟩

/-- Low-temperature finite-secant sharpness certificate:
below the threshold, an actual sufficiently small one-pair improvement causes a
strict drop.  The TeX proof obtains this actual drop from the finite-secant
formula, continuity of the NLHF fixed point in the margin matrix, and the
negative limiting numerator. -/
def HasNLHFLowTempSecantDropCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (NLHF : ℝ → MatrixRule α) : Prop :=
  ∀ τ : ℝ, 0 < τ → τ < (3 : ℝ) / 8 →
    ∃ (M : α → α → ℝ) (ρ : α → ℝ) (x y : α) (δ : ℝ),
      IsNormalizedMarginMatrix M ∧
      IsFullSupportLottery ρ ∧
      x ≠ y ∧
      0 < δ ∧
      δ ≤ 1 - M x y ∧
      NLHF τ (improvePairMargin M x y δ) ρ x < NLHF τ M ρ x

theorem NLHFViolatesForSmallTau_of_lowTempSecantDropCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    {NLHF : ℝ → MatrixRule α}
    (hcert : HasNLHFLowTempSecantDropCertificate NLHF) :
    NLHFViolatesForSmallTau NLHF := by
  intro τ hτ hτlt
  rcases hcert τ hτ hτlt with
    ⟨M, ρ, x, y, δ, hM, hρ, hxy, hδpos, hδle, hdrop⟩
  exact violatesProbabilisticMonotonicity_of_pair_improvement_drop
    hM hρ hxy hδpos.le hδle hdrop

/-- Certificate for the monotonicity-threshold proof.
The large-temperature half is supplied by the finite-comparison argument, and
the low-temperature half by the finite-secant strict-drop construction. -/
def HasNLHFThresholdCertificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (NLHF : ℝ → MatrixRule α) : Prop :=
  NLHFMonotoneForLargeTau NLHF ∧
  HasNLHFLowTempSecantDropCertificate NLHF

/-- Threshold assembly with no path-calculus assumptions. -/
theorem NLHFmono_from_threshold_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (NLHF : ℝ → MatrixRule α)
    (hcert : HasNLHFThresholdCertificate NLHF)
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity (NLHF τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_named_parts NLHF hcert.1
    (NLHFViolatesForSmallTau_of_lowTempSecantDropCertificate hcert.2) hτ

end PaperFormalization
