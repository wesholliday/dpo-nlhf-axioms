import PaperFormalization.WeakProfileBorda

open scoped BigOperators

namespace PaperFormalization

/-! # Borda-IPO and proportional Borda

The proof follows Proposition `BIPOandPB` in the author's camera-ready
Appendix: a finite sum of squares is zero exactly when all adjusted log
ratios agree; exponentiation and normalization identify the PB lottery.
The generic score-vector proof is then instantiated at the paper's actual
partial-Borda score, including half credit for missing comparisons.
-/

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Minimizers over the full-support lottery domain, with feasibility included. -/
def fullSupportArgminSet (L : (α → ℝ) → ℝ) : Set (α → ℝ) :=
  {π | IsFullSupportLottery π ∧
    ∀ q : α → ℝ, IsFullSupportLottery q → L π ≤ L q}

/-- The Borda-IPO sum of squares, with an arbitrary supplied score vector. -/
noncomputable def bordaIPOLoss (η : ℝ) (ρ B π : α → ℝ) : ℝ :=
  ∑ x : α, ∑ y ∈ Finset.univ.erase x,
    (Real.log (π x / ρ x) - Real.log (π y / ρ y) - η * (B x - B y)) ^ 2

omit [Nonempty α] in
lemma bordaIPOLoss_nonneg (η : ℝ) (ρ B π : α → ℝ) :
    0 ≤ bordaIPOLoss η ρ B π := by
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _

omit [Nonempty α] in
/-- The first step of the English proof, including the trivial diagonal. -/
lemma bordaIPOLoss_eq_zero_iff_log_eq (η : ℝ) (ρ B π : α → ℝ) :
    bordaIPOLoss η ρ B π = 0 ↔
      ∀ x y : α, Real.log (π x / ρ x) - η * B x =
        Real.log (π y / ρ y) - η * B y := by
  constructor
  · intro h x y
    by_cases hxy : x = y
    · subst y; rfl
    have hx : (∑ y ∈ Finset.univ.erase x,
        (Real.log (π x / ρ x) - Real.log (π y / ρ y) - η * (B x - B y)) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => Finset.sum_nonneg (fun y _ => sq_nonneg _))).mp h x (by simp)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y (_ : y ∈ Finset.univ.erase x) =>
        sq_nonneg (Real.log (π x / ρ x) - Real.log (π y / ρ y) - η * (B x - B y)))).mp
      hx y (by simp [Ne.symm hxy])
    have hz := (sq_eq_zero_iff).mp hterm
    nlinarith
  · intro h
    unfold bordaIPOLoss
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    have hxy := h x y
    have hz : Real.log (π x / ρ x) - Real.log (π y / ρ y) - η * (B x - B y) = 0 := by
      nlinarith
    rw [hz, zero_pow (by decide)]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Exponentiating an adjusted log ratio yields the ratio used for normalization. -/
lemma exp_borda_log_ratio {η : ℝ} {ρ B π : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) (hπ : ∀ x, 0 < π x) (x : α) :
    Real.exp (Real.log (π x / ρ x) - η * B x) =
      π x / (ρ x * Real.exp (η * B x)) := by
  rw [Real.exp_sub, Real.exp_log (div_pos (hπ x) (hρ x)), div_div]

lemma log_proportionalBorda_div_ref {η : ℝ} {ρ B : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) (x : α) :
    Real.log (proportionalBorda η ρ B x / ρ x) =
      η * B x - Real.log (tiltDen ρ (fun z => Real.exp (η * B z))) := by
  have hZ := tiltDen_pos hρ (fun z => Real.exp_pos (η * B z))
  have hratio : proportionalBorda η ρ B x / ρ x =
      Real.exp (η * B x) / tiltDen ρ (fun z => Real.exp (η * B z)) := by
    unfold proportionalBorda tilt
    field_simp [ne_of_gt (hρ x), ne_of_gt hZ]
  rw [hratio, Real.log_div (Real.exp_ne_zero _) (ne_of_gt hZ), Real.log_exp]

lemma bordaIPOLoss_proportionalBorda {η : ℝ} {ρ B : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) :
    bordaIPOLoss η ρ B (proportionalBorda η ρ B) = 0 := by
  apply (bordaIPOLoss_eq_zero_iff_log_eq _ _ _ _).mpr
  intro x y
  rw [log_proportionalBorda_div_ref hρ x, log_proportionalBorda_div_ref hρ y]
  ring

/-- The English proof's zero-loss characterization, using its explicit
normalization calculation and no convexity or differentiation argument. -/
theorem bordaIPOLoss_eq_zero_iff {η : ℝ} {ρ B π : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) (hπ : IsFullSupportLottery π) :
    bordaIPOLoss η ρ B π = 0 ↔ π = proportionalBorda η ρ B := by
  constructor
  · intro hzero
    have hlog := (bordaIPOLoss_eq_zero_iff_log_eq _ _ _ _).mp hzero
    have hrat : ∀ x y : α,
        π x / (ρ x * Real.exp (η * B x)) =
          π y / (ρ y * Real.exp (η * B y)) := by
      intro x y
      simpa only [exp_borda_log_ratio hρ hπ.1] using congrArg Real.exp (hlog x y)
    funext x
    have hterms : ∀ z : α, π z =
        (π x / (ρ x * Real.exp (η * B x))) * (ρ z * Real.exp (η * B z)) := by
      intro z
      have hzpos : 0 < ρ z * Real.exp (η * B z) := mul_pos (hρ z) (Real.exp_pos _)
      exact (div_eq_iff (ne_of_gt hzpos)).mp (hrat z x)
    have hnorm : 1 = (π x / (ρ x * Real.exp (η * B x))) *
        tiltDen ρ (fun z => Real.exp (η * B z)) := by
      calc
        1 = ∑ z : α, π z := hπ.2.symm
        _ = ∑ z : α,
            (π x / (ρ x * Real.exp (η * B x))) * (ρ z * Real.exp (η * B z)) :=
          Finset.sum_congr rfl (fun z _ => hterms z)
        _ = _ := by rw [← Finset.mul_sum]; rfl
    have hZ := tiltDen_pos hρ (fun z => Real.exp_pos (η * B z))
    unfold proportionalBorda tilt
    apply (eq_div_iff (ne_of_gt hZ)).mpr
    have hn := hnorm
    field_simp [ne_of_gt (hρ x), Real.exp_ne_zero] at hn
    nlinarith
  · rintro rfl
    exact bordaIPOLoss_proportionalBorda hρ

theorem bordaIPOLoss_argmin {η : ℝ} {ρ B : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) :
    fullSupportArgminSet (bordaIPOLoss η ρ B) =
      ({proportionalBorda η ρ B} : Set (α → ℝ)) := by
  have hp := proportionalBorda_fullSupport (η := η) (B := B) hρ
  have hz := bordaIPOLoss_proportionalBorda (η := η) (B := B) hρ
  ext π
  constructor
  · rintro ⟨hπ, hmin⟩
    have hle := hmin (proportionalBorda η ρ B) hp
    rw [hz] at hle
    have hzero := le_antisymm hle (bordaIPOLoss_nonneg η ρ B π)
    exact Set.mem_singleton_iff.mpr ((bordaIPOLoss_eq_zero_iff hρ hπ).mp hzero)
  · intro hπ
    rw [Set.mem_singleton_iff] at hπ
    subst π
    refine ⟨hp, fun q hq => ?_⟩
    rw [hz]
    exact bordaIPOLoss_nonneg η ρ B q

/-- The profile-level objective in Remark `IPOremark`. -/
noncomputable def bordaIPOObjective {V : Type*} [Fintype V]
    (η : ℝ) (R : V → α → α → Bool) (ρ π : α → ℝ) : ℝ :=
  bordaIPOLoss η ρ (partialBordaScoreP R) π

/-- Proposition `BIPOandPB` for arbitrary relation-valued finite profiles. -/
theorem bordaIPOObjective_argmin_and_zero {V : Type*} [Fintype V]
    {η : ℝ} (_hη : 0 < η) (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (bordaIPOObjective η R ρ) =
        ({proportionalBorda η ρ (partialBordaScoreP R)} : Set (α → ℝ)) ∧
      bordaIPOObjective η R ρ (proportionalBorda η ρ (partialBordaScoreP R)) = 0 :=
  ⟨bordaIPOLoss_argmin hρ.1, bordaIPOLoss_proportionalBorda hρ.1⟩

end PaperFormalization
