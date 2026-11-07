import PaperFormalization.Core

open scoped BigOperators

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def sigmoid (t : ℝ) : ℝ :=
  1 / (1 + Real.exp (-t))

/-- The DPO objective in the finite profile abstraction from the paper. The
input `c x y` is the strict count of voters preferring `x` to `y`. -/
noncomputable def dpoObjective
    (β : ℝ) (c : α → α → ℝ) (ρ π : α → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun x =>
    Finset.sum (Finset.univ.erase x) (fun y =>
      c x y *
        Real.log
          (sigmoid
            (β * (Real.log (π x / ρ x) - Real.log (π y / ρ y))))))

/-- Bradley--Terry/Zermelo log-likelihood objective. -/
noncomputable def btObjective
    (c : α → α → ℝ) (u : α → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun x =>
    Finset.sum (Finset.univ.erase x) (fun y =>
      c x y * Real.log (u x / (u x + u y))))

noncomputable def btFraction (u : α → ℝ) (x y : α) : ℝ :=
  u x / (u x + u y)

omit [Fintype α] [DecidableEq α] in
lemma btFraction_pos_of_pos
    {u : α → ℝ} (hu : ∀ x : α, 0 < u x) (x y : α) :
    0 < btFraction u x y := by
  unfold btFraction
  exact div_pos (hu x) (add_pos (hu x) (hu y))

omit [Fintype α] [DecidableEq α] in
lemma btFraction_lt_one_of_pos
    {u : α → ℝ} (hu : ∀ x : α, 0 < u x) (x y : α) :
    btFraction u x y < 1 := by
  have hden_pos : 0 < u x + u y := add_pos (hu x) (hu y)
  have hlt : u x < u x + u y := lt_add_of_pos_right (u x) (hu y)
  unfold btFraction
  calc
    u x / (u x + u y) < (u x + u y) / (u x + u y) :=
      div_lt_div_of_pos_right hlt hden_pos
    _ = 1 := div_self hden_pos.ne'

omit [Fintype α] [DecidableEq α] in
lemma btFraction_nonneg_of_nonneg_and_pos_sum
    {u : α → ℝ} {x y : α}
    (hx : 0 ≤ u x) (hden : 0 < u x + u y) :
    0 ≤ btFraction u x y := by
  unfold btFraction
  exact div_nonneg hx hden.le

omit [Fintype α] [DecidableEq α] in
lemma btFraction_eq_zero_of_left_eq_zero
    {u : α → ℝ} {x y : α}
    (hx : u x = 0) :
    btFraction u x y = 0 := by
  unfold btFraction
  rw [hx]
  simp

omit [Fintype α] [DecidableEq α] in
lemma btFraction_add_swap_eq_one
    {u : α → ℝ} (hu : ∀ x : α, 0 < u x) (x y : α) :
    btFraction u x y + btFraction u y x = 1 := by
  have hden : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
  unfold btFraction
  field_simp [hden, add_comm]
  ring

omit [Fintype α] [DecidableEq α] in
lemma btFraction_scaled
    {u : α → ℝ} {a : ℝ} (ha : 0 < a)
    (hu : ∀ x : α, 0 < u x) (x y : α) :
    btFraction (fun z => a * u z) x y = btFraction u x y := by
  have hxy : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
  unfold btFraction
  field_simp [ha.ne', hxy]

def IsDPOArgmax
    (β : ℝ) (c : α → α → ℝ) (ρ π : α → ℝ) : Prop :=
  IsFullSupportLottery π ∧
    ∀ π' : α → ℝ, IsFullSupportLottery π' →
      dpoObjective β c ρ π' ≤ dpoObjective β c ρ π

def dpoArgmaxSet
    (β : ℝ) (c : α → α → ℝ) (ρ : α → ℝ) : Set (α → ℝ) :=
  {π | IsDPOArgmax β c ρ π}

/-- The BT/Zermelo variable used in the DPO change of variables:
`u_x = (π(x)/ρ(x))^β`. -/
noncomputable def dpoBTVariable
    (β : ℝ) (ρ π : α → ℝ) : α → ℝ :=
  fun x => (π x / ρ x) ^ β

/-- The inverse map from a positive BT variable to a lottery-shaped vector,
before imposing the normalization constraint. -/
noncomputable def dpoLotteryFromBTVariable
    (β : ℝ) (ρ u : α → ℝ) : α → ℝ :=
  fun x => ρ x * (u x) ^ (1 / β)

/-- The normalization constraint appearing in the proof of `DPOasRTBT`. -/
noncomputable def dpoBTNormalization
    (β : ℝ) (ρ u : α → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun x => ρ x * (u x) ^ (1 / β))

omit [DecidableEq α] in
lemma dpoLotteryFromBTVariable_sum
    (β : ℝ) (ρ u : α → ℝ) :
    Finset.sum Finset.univ (fun x => dpoLotteryFromBTVariable β ρ u x) =
      dpoBTNormalization β ρ u := by
  rfl

omit [Fintype α] [DecidableEq α] in
lemma dpoBTVariable_pos
    {β : ℝ} {ρ π : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hπ : ∀ x : α, 0 < π x) :
    ∀ x : α, 0 < dpoBTVariable β ρ π x := by
  intro x
  exact Real.rpow_pos_of_pos (div_pos (hπ x) (hρ x)) β

omit [Fintype α] [DecidableEq α] in
/-- The DPO-to-BT change of variables followed by the inverse map recovers the
original positive lottery. -/
lemma dpoLotteryFromBTVariable_dpoBTVariable
    {β : ℝ} (hβ : 0 < β) {ρ π : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hπ : ∀ x : α, 0 < π x) :
    dpoLotteryFromBTVariable β ρ (dpoBTVariable β ρ π) = π := by
  funext x
  have hxpos : 0 < π x / ρ x := div_pos (hπ x) (hρ x)
  unfold dpoLotteryFromBTVariable dpoBTVariable
  rw [← Real.rpow_mul hxpos.le]
  have hexp : β * (1 / β) = 1 := by
    field_simp [hβ.ne']
  rw [hexp, Real.rpow_one]
  field_simp [hρ x |>.ne']

omit [DecidableEq α] in
/-- The normalization constraint for the BT variable associated to a positive
lottery is exactly the lottery sum. -/
lemma dpoBTNormalization_dpoBTVariable
    {β : ℝ} (hβ : 0 < β) {ρ π : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hπ : ∀ x : α, 0 < π x) :
    dpoBTNormalization β ρ (dpoBTVariable β ρ π) =
      Finset.sum Finset.univ (fun x => π x) := by
  rw [← dpoLotteryFromBTVariable_sum β ρ (dpoBTVariable β ρ π)]
  rw [dpoLotteryFromBTVariable_dpoBTVariable hβ hρ hπ]

omit [DecidableEq α] in
/-- Hence a full-support lottery maps to a normalized BT variable. -/
lemma dpoBTNormalization_dpoBTVariable_of_fullSupport
    {β : ℝ} (hβ : 0 < β) {ρ π : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hπ : IsFullSupportLottery π) :
    dpoBTNormalization β ρ (dpoBTVariable β ρ π) = 1 := by
  rw [dpoBTNormalization_dpoBTVariable hβ hρ hπ.1]
  exact hπ.2

lemma dpoBTNormalization_pos
    [Nonempty α] {β : ℝ} {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hu : ∀ x : α, 0 < u x) :
    0 < dpoBTNormalization β ρ u := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty α›
  have hterm : 0 < ρ x0 * (u x0) ^ (1 / β) :=
    mul_pos (hρ x0) (Real.rpow_pos_of_pos (hu x0) (1 / β))
  have hrest :
      0 ≤ Finset.sum (Finset.univ.erase x0)
        (fun x => ρ x * (u x) ^ (1 / β)) := by
    refine Finset.sum_nonneg ?_
    intro x hx
    exact (mul_pos (hρ x) (Real.rpow_pos_of_pos (hu x) (1 / β))).le
  unfold dpoBTNormalization
  rw [← Finset.add_sum_erase (s := Finset.univ)
    (f := fun x => ρ x * (u x) ^ (1 / β)) (by simp)]
  exact add_pos_of_pos_of_nonneg hterm hrest

omit [Fintype α] [DecidableEq α] in
/-- The inverse map followed by the DPO-to-BT variable recovers the original
positive BT variable. -/
lemma dpoBTVariable_dpoLotteryFromBTVariable
    {β : ℝ} (hβ : 0 < β) {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hu : ∀ x : α, 0 < u x) :
    dpoBTVariable β ρ (dpoLotteryFromBTVariable β ρ u) = u := by
  funext x
  have hroot_pos : 0 < (u x) ^ (1 / β) :=
    Real.rpow_pos_of_pos (hu x) (1 / β)
  have hdiv :
      ρ x * (u x) ^ (1 / β) / ρ x = (u x) ^ (1 / β) := by
    field_simp [hρ x |>.ne']
  unfold dpoBTVariable dpoLotteryFromBTVariable
  rw [hdiv, ← Real.rpow_mul (hu x).le]
  have hexp : (1 / β) * β = 1 := by
    field_simp [hβ.ne']
  rw [hexp, Real.rpow_one]

omit [DecidableEq α] in
/-- A normalized positive BT variable maps to a full-support lottery. -/
lemma dpoLotteryFromBTVariable_fullSupport
    {β : ℝ} {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hu : ∀ x : α, 0 < u x)
    (hnorm : dpoBTNormalization β ρ u = 1) :
    IsFullSupportLottery (dpoLotteryFromBTVariable β ρ u) := by
  refine ⟨?_, ?_⟩
  · intro x
    unfold dpoLotteryFromBTVariable
    exact mul_pos (hρ x) (Real.rpow_pos_of_pos (hu x) (1 / β))
  · rw [dpoLotteryFromBTVariable_sum]
    exact hnorm

omit [Fintype α] [DecidableEq α] in
/-- Scaling a positive BT variable scales the inverse-map vector by
`a^(1/β)`. -/
lemma dpoLotteryFromBTVariable_scaled
    {β a : ℝ} {ρ u : α → ℝ}
    (ha : 0 < a) (hu : ∀ x : α, 0 ≤ u x) :
    dpoLotteryFromBTVariable β ρ (fun x => a * u x) =
      fun x => a ^ (1 / β) * dpoLotteryFromBTVariable β ρ u x := by
  funext x
  unfold dpoLotteryFromBTVariable
  rw [Real.mul_rpow ha.le (hu x)]
  ring

omit [DecidableEq α] in
/-- The corresponding scaling rule for the DPO normalization constraint. -/
lemma dpoBTNormalization_scaled
    {β a : ℝ} {ρ u : α → ℝ}
    (ha : 0 < a) (hu : ∀ x : α, 0 ≤ u x) :
    dpoBTNormalization β ρ (fun x => a * u x) =
      a ^ (1 / β) * dpoBTNormalization β ρ u := by
  classical
  unfold dpoBTNormalization
  calc
    Finset.sum Finset.univ (fun x => ρ x * (a * u x) ^ (1 / β))
        =
      Finset.sum Finset.univ
        (fun x => a ^ (1 / β) * (ρ x * (u x) ^ (1 / β))) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [Real.mul_rpow ha.le (hu x)]
          ring
    _ = a ^ (1 / β) *
        Finset.sum Finset.univ (fun x => ρ x * (u x) ^ (1 / β)) := by
          rw [Finset.mul_sum]

omit [DecidableEq α] in
/-- The normalization step in the proof of `DPOasRTBT`: once a scalar multiple
`a • u` satisfies the DPO normalization constraint, its inverse-map lottery is
exactly the RTBT normalization of `u`. -/
theorem dpoLotteryFromBTVariable_scaled_eq_RTBT
    {β a : ℝ} {ρ u : α → ℝ}
    (ha : 0 < a) (hu : ∀ x : α, 0 ≤ u x)
    (hnorm : a ^ (1 / β) * dpoBTNormalization β ρ u = 1) :
    dpoLotteryFromBTVariable β ρ (fun x => a * u x) =
      RTBTFromStrength β ρ u := by
  classical
  have hDne : dpoBTNormalization β ρ u ≠ 0 := by
    intro hD
    rw [hD, mul_zero] at hnorm
    norm_num at hnorm
  have hscale :
      a ^ (1 / β) = 1 / dpoBTNormalization β ρ u := by
    calc
      a ^ (1 / β) =
          (a ^ (1 / β) * dpoBTNormalization β ρ u) /
            dpoBTNormalization β ρ u := by
              field_simp [hDne]
      _ = 1 / dpoBTNormalization β ρ u := by
              rw [hnorm]
  funext x
  unfold dpoLotteryFromBTVariable RTBTFromStrength dpoBTNormalization at *
  rw [Real.mul_rpow ha.le (hu x), hscale]
  field_simp [hDne]

omit [DecidableEq α] in
/-- The same normalization step, stated directly with the paper's constraint
`Σ_x ρ_x (a u_x)^(1/β)=1`. -/
theorem dpoLotteryFromBTVariable_scaled_eq_RTBT_of_normalized_sum
    {β a : ℝ} {ρ u : α → ℝ}
    (ha : 0 < a) (hu : ∀ x : α, 0 ≤ u x)
    (hnorm : dpoBTNormalization β ρ (fun x => a * u x) = 1) :
    dpoLotteryFromBTVariable β ρ (fun x => a * u x) =
      RTBTFromStrength β ρ u := by
  refine dpoLotteryFromBTVariable_scaled_eq_RTBT ha hu ?_
  rw [← dpoBTNormalization_scaled ha hu]
  exact hnorm

omit [Fintype α] [DecidableEq α] in
lemma dpoBTNormalization_explicit_scale_root
    {β D : ℝ} (hβ : 0 < β) (hD : 0 < D) :
    (D ^ (-β)) ^ (1 / β) * D = 1 := by
  rw [← Real.rpow_mul hD.le]
  have hexp : -β * (1 / β) = -1 := by
    field_simp [hβ.ne']
  rw [hexp, Real.rpow_neg_one]
  field_simp [hD.ne']

omit [DecidableEq α] in
/-- The explicit scalar used in the appendix proof,
`a = (Σ_x ρ_x u_x^(1/β))^{-β}`, gives the RTBT formula. -/
theorem dpoLotteryFromBTVariable_explicit_scaled_eq_RTBT
    {β : ℝ} (hβ : 0 < β) {ρ u : α → ℝ}
    (hu : ∀ x : α, 0 ≤ u x)
    (hD : 0 < dpoBTNormalization β ρ u) :
    dpoLotteryFromBTVariable β ρ
        (fun x => (dpoBTNormalization β ρ u) ^ (-β) * u x) =
      RTBTFromStrength β ρ u := by
  exact dpoLotteryFromBTVariable_scaled_eq_RTBT
    (Real.rpow_pos_of_pos hD (-β)) hu
    (dpoBTNormalization_explicit_scale_root hβ hD)

/-- Proposition `DPOasRTBT`, with the Ford/Zermelo theorem and the
change-of-variables argument isolated into the `hray` hypothesis.  The
hypothesis says exactly that the DPO argmaxes are the normalized points on the
positive BT-maximizer ray through `u`; the conclusion is the singleton RTBT
lottery. -/
theorem DPOasRTBT_from_BT_ray_argmax
    {β : ℝ} (hβ : 0 < β) {c : α → α → ℝ} {ρ u : α → ℝ}
    (hu : ∀ x : α, 0 ≤ u x)
    (hD : 0 < dpoBTNormalization β ρ u)
    (hray : ∀ π : α → ℝ,
      IsDPOArgmax β c ρ π ↔
        ∃ a : ℝ,
          0 < a ∧
            dpoBTNormalization β ρ (fun x => a * u x) = 1 ∧
              π = dpoLotteryFromBTVariable β ρ (fun x => a * u x)) :
    dpoArgmaxSet β c ρ =
      ({RTBTFromStrength β ρ u} : Set (α → ℝ)) := by
  classical
  ext π
  constructor
  · intro hπ
    rcases (hray π).mp hπ with ⟨a, ha, hnorm, hπray⟩
    have hπrtbt : π = RTBTFromStrength β ρ u := by
      rw [hπray]
      exact dpoLotteryFromBTVariable_scaled_eq_RTBT_of_normalized_sum
        ha hu hnorm
    exact Set.mem_singleton_iff.mpr hπrtbt
  · intro hπ
    let a := (dpoBTNormalization β ρ u) ^ (-β)
    have ha : 0 < a := Real.rpow_pos_of_pos hD (-β)
    have hnorm :
        dpoBTNormalization β ρ (fun x => a * u x) = 1 := by
      rw [dpoBTNormalization_scaled ha hu]
      exact dpoBTNormalization_explicit_scale_root hβ hD
    have hrtbt :
        dpoLotteryFromBTVariable β ρ (fun x => a * u x) =
          RTBTFromStrength β ρ u :=
      dpoLotteryFromBTVariable_explicit_scaled_eq_RTBT hβ hu hD
    refine (hray π).mpr ⟨a, ha, hnorm, ?_⟩
    rw [Set.mem_singleton_iff.mp hπ]
    exact hrtbt.symm

/-- A more paper-facing form of `DPOasRTBT_from_BT_ray_argmax`: positive
reference weights and positive BT strengths imply the required RTBT
normalization denominator is positive. -/
theorem DPOasRTBT_from_positive_BT_ray_argmax
    [Nonempty α] {β : ℝ} (hβ : 0 < β) {c : α → α → ℝ}
    {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hu : ∀ x : α, 0 < u x)
    (hray : ∀ π : α → ℝ,
      IsDPOArgmax β c ρ π ↔
        ∃ a : ℝ,
          0 < a ∧
            dpoBTNormalization β ρ (fun x => a * u x) = 1 ∧
              π = dpoLotteryFromBTVariable β ρ (fun x => a * u x)) :
    dpoArgmaxSet β c ρ =
      ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_BT_ray_argmax hβ
    (fun x => (hu x).le)
    (dpoBTNormalization_pos hρ hu)
    hray

omit [Fintype α] [DecidableEq α] in
/-- The pointwise change-of-variables identity behind Remark `BTRemark`. -/
lemma sigmoid_eq_btFraction_of_dpoBTVariable
    {β : ℝ} {ρ π : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hπ : ∀ x : α, 0 < π x)
    (x y : α) :
    sigmoid
        (β * (Real.log (π x / ρ x) - Real.log (π y / ρ y))) =
      dpoBTVariable β ρ π x /
        (dpoBTVariable β ρ π x + dpoBTVariable β ρ π y) := by
  have hxpos : 0 < π x / ρ x := div_pos (hπ x) (hρ x)
  have hypos : 0 < π y / ρ y := div_pos (hπ y) (hρ y)
  unfold sigmoid dpoBTVariable
  rw [Real.rpow_def_of_pos hxpos, Real.rpow_def_of_pos hypos]
  have harg :
      -(β * (Real.log (π x / ρ x) - Real.log (π y / ρ y))) =
        β * Real.log (π y / ρ y) - β * Real.log (π x / ρ x) := by
    ring
  rw [harg, Real.exp_sub]
  field_simp [Real.exp_ne_zero]

/-- The sum-level form of Remark `BTRemark`: once the pairwise sigmoid terms
are identified with the Bradley--Terry fractions under the change of variables,
the DPO and BT objectives are definitionally equal after summing over pairs. -/
theorem dpoObjective_eq_btObjective_of_pairwise
    {β : ℝ} {c : α → α → ℝ} {ρ π u : α → ℝ}
    (hpair : ∀ x y : α, x ≠ y →
      sigmoid
        (β * (Real.log (π x / ρ x) - Real.log (π y / ρ y))) =
          u x / (u x + u y)) :
    dpoObjective β c ρ π = btObjective c u := by
  classical
  unfold dpoObjective btObjective
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro y hy
  rw [hpair x y (Ne.symm (Finset.mem_erase.mp hy).1)]

/-- Remark `BTRemark`: under the DPO/BT change of variables, the DPO objective
is the Bradley--Terry objective. -/
theorem dpoObjective_eq_btObjective_change_of_variables
    {β : ℝ} {c : α → α → ℝ} {ρ π : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hπ : ∀ x : α, 0 < π x) :
    dpoObjective β c ρ π = btObjective c (dpoBTVariable β ρ π) :=
  dpoObjective_eq_btObjective_of_pairwise
    (fun x y _hxy => sigmoid_eq_btFraction_of_dpoBTVariable hρ hπ x y)

/-- The inverse-map form of Remark `BTRemark`: after setting
`π_x = ρ_x u_x^(1/β)`, the DPO objective is the BT objective in `u`. -/
theorem dpoObjective_eq_btObjective_inverse_change_of_variables
    {β : ℝ} (hβ : 0 < β) {c : α → α → ℝ} {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hu : ∀ x : α, 0 < u x) :
    dpoObjective β c ρ (dpoLotteryFromBTVariable β ρ u) =
      btObjective c u := by
  rw [dpoObjective_eq_btObjective_change_of_variables hρ]
  · rw [dpoBTVariable_dpoLotteryFromBTVariable hβ hρ hu]
  · intro x
    unfold dpoLotteryFromBTVariable
    exact mul_pos (hρ x) (Real.rpow_pos_of_pos (hu x) (1 / β))

/-- The Bradley--Terry objective is unchanged by multiplying all strengths by
the same positive scalar. -/
lemma btObjective_scaled
    {c : α → α → ℝ} {a : ℝ} {u : α → ℝ}
    (ha : 0 < a) (hu : ∀ x : α, 0 < u x) :
    btObjective c (fun x => a * u x) = btObjective c u := by
  classical
  unfold btObjective
  refine Finset.sum_congr rfl ?_
  intro x hx
  refine Finset.sum_congr rfl ?_
  intro y hy
  have hsum : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
  have hfrac :
      (a * u x) / (a * u x + a * u y) = u x / (u x + u y) := by
    field_simp [ha.ne', hsum]
  rw [hfrac]

/-- Normalize a positive Bradley--Terry vector onto Ford's simplex
`Σ_i w_i = 1`. -/
noncomputable def btNormalize (u : α → ℝ) : α → ℝ :=
  fun x => u x / Finset.sum Finset.univ (fun z => u z)

omit [DecidableEq α] in
lemma btNormalize_eq_inv_sum_smul (u : α → ℝ) :
    btNormalize u =
      fun x => (1 / Finset.sum Finset.univ (fun z => u z)) * u x := by
  funext x
  unfold btNormalize
  ring

omit [DecidableEq α] in
lemma btNormalize_den_pos [Nonempty α] {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    0 < Finset.sum Finset.univ (fun z => u z) := by
  obtain ⟨z0⟩ := ‹Nonempty α›
  exact Finset.sum_pos (fun z _hz => hu z) ⟨z0, by simp⟩

omit [DecidableEq α] in
lemma btNormalize_fullSupport [Nonempty α] {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    IsFullSupportLottery (btNormalize u) := by
  have hden_pos := btNormalize_den_pos (α := α) hu
  refine ⟨?_, ?_⟩
  · intro x
    unfold btNormalize
    exact div_pos (hu x) hden_pos
  · unfold btNormalize
    rw [← Finset.sum_div]
    exact div_self hden_pos.ne'

lemma btObjective_btNormalize [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    btObjective c (btNormalize u) = btObjective c u := by
  rw [btNormalize_eq_inv_sum_smul]
  exact btObjective_scaled
    (one_div_pos.mpr (btNormalize_den_pos (α := α) hu)) hu

/-- The positive-maximizer ray conclusion of Proposition `BTProp`, isolated as
a named certificate. -/
def HasBTPositiveMaximizerRay
    (c : α → α → ℝ) (u : α → ℝ) : Prop :=
  (∀ x : α, 0 < u x) ∧
    ∀ v : α → ℝ, (∀ x : α, 0 < v x) →
      ((∀ w : α → ℝ, (∀ x : α, 0 < w x) →
          btObjective c w ≤ btObjective c v) ↔
        ∃ a : ℝ, 0 < a ∧ v = fun x => a * u x)

/-- Ford's theorem is naturally stated on the normalized simplex
`Σ_i w_i = 1`: `u` is a full-support normalized maximizer, and it is the
unique full-support normalized maximizer. -/
def HasFordNormalizedBTMaximizer
    (c : α → α → ℝ) (u : α → ℝ) : Prop :=
  IsFullSupportLottery u ∧
    (∀ v : α → ℝ, IsFullSupportLottery v →
      btObjective c v ≤ btObjective c u) ∧
      ∀ v : α → ℝ, IsFullSupportLottery v →
        (∀ w : α → ℝ, IsFullSupportLottery w →
          btObjective c w ≤ btObjective c v) →
            v = u

/-- Ford-style normalized uniqueness implies the positive-ray maximizer
certificate used by the DPO/RTBT change-of-variables proof.  The only extra
ingredient is Ford's scale invariance: the Bradley--Terry objective is
unchanged by multiplying every strength by the same positive scalar. -/
theorem HasBTPositiveMaximizerRay_of_ford_normalized_maximizer
    [Nonempty α] {c : α → α → ℝ} {u : α → ℝ}
    (hFord : HasFordNormalizedBTMaximizer c u) :
    HasBTPositiveMaximizerRay c u := by
  refine ⟨hFord.1.1, ?_⟩
  intro v hvpos
  constructor
  · intro hvmax
    have hvnorm_full : IsFullSupportLottery (btNormalize v) :=
      btNormalize_fullSupport hvpos
    have hvnorm_max :
        ∀ w : α → ℝ, IsFullSupportLottery w →
          btObjective c w ≤ btObjective c (btNormalize v) := by
      intro w hw
      calc
        btObjective c w ≤ btObjective c v := hvmax w hw.1
        _ = btObjective c (btNormalize v) :=
          (btObjective_btNormalize hvpos).symm
    have hnorm_eq : btNormalize v = u :=
      hFord.2.2 (btNormalize v) hvnorm_full hvnorm_max
    let a : ℝ := Finset.sum Finset.univ (fun x => v x)
    have ha : 0 < a := by
      dsimp [a]
      exact btNormalize_den_pos (α := α) hvpos
    refine ⟨a, ha, ?_⟩
    funext x
    have hx := congrArg (fun f : α → ℝ => f x) hnorm_eq
    dsimp [btNormalize, a] at hx
    calc
      v x = (v x / a) * a := by field_simp [ha.ne']
      _ = u x * a := by rw [hx]
      _ = a * u x := by ring
  · rintro ⟨a, ha, hv⟩
    intro w hwpos
    have hw_norm_full : IsFullSupportLottery (btNormalize w) :=
      btNormalize_fullSupport hwpos
    calc
      btObjective c w =
          btObjective c (btNormalize w) :=
            (btObjective_btNormalize hwpos).symm
      _ ≤ btObjective c u :=
            hFord.2.1 (btNormalize w) hw_norm_full
      _ = btObjective c v := by
            rw [hv]
            exact (btObjective_scaled ha hFord.1.1).symm

/-- Proposition `BTProp`, in the combined form needed by the DPO/RTBT proof:
`u` is the normalized Bradley--Terry strength vector, it is unique among
normalized strength vectors, and the positive maximizers of the BT objective
are exactly the positive ray through `u`. -/
def HasBTPropCertificate
    (w c : α → α → ℝ) (u : α → ℝ) : Prop :=
  IsBTStrength w c u ∧
    HasBTPositiveMaximizerRay c u ∧
      ∀ v : α → ℝ, IsBTStrength w c v → v = u

/-- Ford's theorem in the form closest to the paper proof: displayed
Bradley--Terry equations plus the normalized maximum-likelihood theorem. -/
def HasFordBTPropCertificate
    (w c : α → α → ℝ) (u : α → ℝ) : Prop :=
  IsBTStrength w c u ∧
    HasFordNormalizedBTMaximizer c u ∧
      ∀ v : α → ℝ, IsBTStrength w c v → v = u

/-- Convert Ford's normalized maximum-likelihood theorem into the existing
`BTProp` interface used by the DPO and RTBT modules. -/
theorem HasBTPropCertificate_of_ford_certificate
    [Nonempty α] {w c : α → α → ℝ} {u : α → ℝ}
    (hFord : HasFordBTPropCertificate w c u) :
    HasBTPropCertificate w c u :=
  ⟨hFord.1,
    HasBTPositiveMaximizerRay_of_ford_normalized_maximizer hFord.2.1,
    hFord.2.2⟩

/-- Proposition `DPOasRTBT` from the Ford/Zermelo positive-maximizer ray:
if the positive maximizers of the Bradley--Terry objective are exactly the
positive multiples of `u`, then the DPO argmax set is the singleton RTBT
lottery generated by `u`. -/
theorem DPOasRTBT_from_BT_positive_maximizer_ray
    [Nonempty α] {β : ℝ} (hβ : 0 < β) {c : α → α → ℝ}
    {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hu : ∀ x : α, 0 < u x)
    (hBTmax : ∀ v : α → ℝ, (∀ x : α, 0 < v x) →
      ((∀ w : α → ℝ, (∀ x : α, 0 < w x) →
          btObjective c w ≤ btObjective c v) ↔
        ∃ a : ℝ, 0 < a ∧ v = fun x => a * u x)) :
    dpoArgmaxSet β c ρ =
      ({RTBTFromStrength β ρ u} : Set (α → ℝ)) := by
  classical
  refine DPOasRTBT_from_positive_BT_ray_argmax hβ hρ hu ?_
  intro π
  constructor
  · intro hπ
    let v : α → ℝ := dpoBTVariable β ρ π
    have hπfull : IsFullSupportLottery π := hπ.1
    have hvpos : ∀ x : α, 0 < v x :=
      dpoBTVariable_pos hρ hπfull.1
    have hvmax :
        ∀ w : α → ℝ, (∀ x : α, 0 < w x) →
          btObjective c w ≤ btObjective c v := by
      intro w hw
      let D : ℝ := dpoBTNormalization β ρ w
      have hDpos : 0 < D := by
        dsimp [D]
        exact dpoBTNormalization_pos hρ hw
      let a : ℝ := D ^ (-β)
      have ha : 0 < a := by
        dsimp [a]
        exact Real.rpow_pos_of_pos hDpos (-β)
      have hscaled_pos : ∀ x : α, 0 < a * w x := fun x => mul_pos ha (hw x)
      have hnorm :
          dpoBTNormalization β ρ (fun x => a * w x) = 1 := by
        dsimp [a, D]
        rw [dpoBTNormalization_scaled (Real.rpow_pos_of_pos hDpos (-β))
          (fun x => (hw x).le)]
        exact dpoBTNormalization_explicit_scale_root hβ hDpos
      have hscaled_full :
          IsFullSupportLottery
            (dpoLotteryFromBTVariable β ρ (fun x => a * w x)) :=
        dpoLotteryFromBTVariable_fullSupport hρ hscaled_pos hnorm
      have hcompare := hπ.2
        (dpoLotteryFromBTVariable β ρ (fun x => a * w x)) hscaled_full
      calc
        btObjective c w =
            btObjective c (fun x => a * w x) := by
              exact (btObjective_scaled ha hw).symm
        _ = dpoObjective β c ρ
            (dpoLotteryFromBTVariable β ρ (fun x => a * w x)) := by
              exact (dpoObjective_eq_btObjective_inverse_change_of_variables
                hβ hρ hscaled_pos).symm
        _ ≤ dpoObjective β c ρ π := hcompare
        _ = btObjective c v := by
              dsimp [v]
              exact dpoObjective_eq_btObjective_change_of_variables hρ hπfull.1
    rcases (hBTmax v hvpos).mp hvmax with ⟨a, ha, hv⟩
    have hnorm :
        dpoBTNormalization β ρ (fun x => a * u x) = 1 := by
      have hnormv :
          dpoBTNormalization β ρ v = 1 :=
        dpoBTNormalization_dpoBTVariable_of_fullSupport hβ hρ hπfull
      simpa [hv] using hnormv
    have hπeq :
        π = dpoLotteryFromBTVariable β ρ (fun x => a * u x) := by
      have hinv :
          dpoLotteryFromBTVariable β ρ v = π :=
        dpoLotteryFromBTVariable_dpoBTVariable hβ hρ hπfull.1
      simpa [hv] using hinv.symm
    exact ⟨a, ha, hnorm, hπeq⟩
  · rintro ⟨a, ha, hnorm, hπeq⟩
    have hscaled_pos : ∀ x : α, 0 < a * u x := fun x => mul_pos ha (hu x)
    refine ⟨?_, ?_⟩
    · rw [hπeq]
      exact dpoLotteryFromBTVariable_fullSupport hρ hscaled_pos hnorm
    · intro π' hπ'full
      let v' : α → ℝ := dpoBTVariable β ρ π'
      have hv'pos : ∀ x : α, 0 < v' x :=
        dpoBTVariable_pos hρ hπ'full.1
      have hscaled_max :
          ∀ w : α → ℝ, (∀ x : α, 0 < w x) →
            btObjective c w ≤ btObjective c (fun x => a * u x) :=
        (hBTmax (fun x => a * u x) hscaled_pos).mpr ⟨a, ha, rfl⟩
      calc
        dpoObjective β c ρ π' =
            btObjective c v' := by
              dsimp [v']
              exact dpoObjective_eq_btObjective_change_of_variables hρ hπ'full.1
        _ ≤ btObjective c (fun x => a * u x) := hscaled_max v' hv'pos
        _ = dpoObjective β c ρ π := by
              rw [hπeq]
              exact (dpoObjective_eq_btObjective_inverse_change_of_variables
                hβ hρ hscaled_pos).symm

/-- Proposition `DPOasRTBT`, stated from the named positive-maximizer-ray
certificate. -/
theorem DPOasRTBT_from_BT_positive_maximizer_certificate
    [Nonempty α] {β : ℝ} (hβ : 0 < β) {c : α → α → ℝ}
    {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hBT : HasBTPositiveMaximizerRay c u) :
    dpoArgmaxSet β c ρ =
      ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_BT_positive_maximizer_ray hβ hρ hBT.1 hBT.2

/-- Proposition `DPOasRTBT`, stated directly from the named `BTProp`
certificate.  The pair-weight matrix `w` is part of the BT equations, while
the DPO objective depends on the strict-count matrix `c`. -/
theorem DPOasRTBT_from_BTProp_certificate
    [Nonempty α] {β : ℝ} (hβ : 0 < β)
    {w c : α → α → ℝ} {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hBT : HasBTPropCertificate w c u) :
    dpoArgmaxSet β c ρ =
      ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_BT_positive_maximizer_certificate hβ hρ hBT.2.1

/-- Proposition `DPOasRTBT` from the Ford-style normalized BT certificate.
This is the direct bridge from Ford's simplex statement to the paper's DPO
argmax conclusion. -/
theorem DPOasRTBT_from_ford_BTProp_certificate
    [Nonempty α] {β : ℝ} (hβ : 0 < β)
    {w c : α → α → ℝ} {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hFord : HasFordBTPropCertificate w c u) :
    dpoArgmaxSet β c ρ =
      ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_BTProp_certificate hβ hρ
    (HasBTPropCertificate_of_ford_certificate hFord)

/-- Proposition `DPOasRTBT`, isolated from the Ford theorem: once the
Bradley--Terry theorem and the change of variables identify exactly one DPO
argmax, the argmax set is the singleton RTBT lottery. -/
theorem DPOasRTBT_from_unique_argmax
    {β : ℝ} {c : α → α → ℝ} {ρ rtbt : α → ℝ}
    (hunique : ∀ π : α → ℝ, IsDPOArgmax β c ρ π ↔ π = rtbt) :
    dpoArgmaxSet β c ρ = ({rtbt} : Set (α → ℝ)) := by
  ext π
  constructor
  · intro hπ
    exact Set.mem_singleton_iff.mpr ((hunique π).mp hπ)
  · intro hπ
    exact (hunique π).mpr (Set.mem_singleton_iff.mp hπ)

end PaperFormalization
