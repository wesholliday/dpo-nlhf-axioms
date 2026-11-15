import PaperFormalization.Axioms

open scoped BigOperators

namespace PaperFormalization

/-- The abstract proof core of Proposition `NLHFcomm`. `C` is the cyclic profile,
`L` the linear profile, and `ρ` the uniform reference. -/
theorem not_commutative_from_cycle_and_line
    {Profile : Type*}
    (F : Profile → (Fin 3 → ℝ) → Fin 3 → ℝ)
    (C L : Profile) (ρ : Fin 3 → ℝ)
    (hCρ : F C ρ = ρ)
    (hLρ_ne : F L ρ ≠ ρ)
    (hC_fixed_only : ∀ q : Fin 3 → ℝ, F C q = q → q = ρ) :
    F C (F L ρ) ≠ F L (F C ρ) := by
  intro hcomm
  have hleft : F C (F L ρ) = F L ρ := by
    simpa [hCρ] using hcomm
  exact hLρ_ne (hC_fixed_only (F L ρ) hleft)

noncomputable def uniform3 : Fin 3 → ℝ :=
  fun _ => (1 : ℝ) / 3

noncomputable def cycleMargin3 : Fin 3 → Fin 3 → ℝ
  | 0, 1 => 1 / 3
  | 1, 2 => 1 / 3
  | 2, 0 => 1 / 3
  | 1, 0 => -1 / 3
  | 2, 1 => -1 / 3
  | 0, 2 => -1 / 3
  | _, _ => 0

noncomputable def linearMargin3 : Fin 3 → Fin 3 → ℝ
  | 0, 1 => 1
  | 0, 2 => 1
  | 1, 2 => 1
  | 1, 0 => -1
  | 2, 0 => -1
  | 2, 1 => -1
  | _, _ => 0

lemma cycleMargin3_normalized : IsNormalizedMarginMatrix cycleMargin3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [cycleMargin3]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [cycleMargin3] <;> norm_num
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [cycleMargin3] <;> norm_num

lemma linearMargin3_normalized : IsNormalizedMarginMatrix linearMargin3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [linearMargin3]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [linearMargin3]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [linearMargin3]

noncomputable def expectedMargin3 (M : Fin 3 → Fin 3 → ℝ)
    (q : Fin 3 → ℝ) (x : Fin 3) : ℝ :=
  Finset.sum Finset.univ (fun y => q y * M x y)

lemma expectedMargin3_eq_expectedMargin
    (M : Fin 3 → Fin 3 → ℝ) (q : Fin 3 → ℝ) (x : Fin 3) :
    expectedMargin3 M q x = expectedMargin M q x := by
  rfl

lemma cycle_expected_eq_zero_uniform :
    ∀ x : Fin 3, expectedMargin3 cycleMargin3 uniform3 x = 0 := by
  intro x
  fin_cases x <;>
    simp [expectedMargin3, cycleMargin3, uniform3, Fin.sum_univ_three] <;>
      norm_num

lemma cycle_expected_eq_zero_uniform_core :
    ∀ x : Fin 3, expectedMargin cycleMargin3 uniform3 x = 0 := by
  intro x
  simpa [expectedMargin3_eq_expectedMargin] using cycle_expected_eq_zero_uniform x

lemma linear_expected_uniform_zero :
    expectedMargin3 linearMargin3 uniform3 0 = (2 : ℝ) / 3 := by
  simp [expectedMargin3, linearMargin3, uniform3, Fin.sum_univ_three]
  norm_num

lemma linear_expected_uniform_one :
    expectedMargin3 linearMargin3 uniform3 1 = 0 := by
  simp [expectedMargin3, linearMargin3, uniform3, Fin.sum_univ_three]

lemma linear_expected_uniform_two :
    expectedMargin3 linearMargin3 uniform3 2 = -(2 : ℝ) / 3 := by
  simp [expectedMargin3, linearMargin3, uniform3, Fin.sum_univ_three]
  norm_num

lemma linear_expected_not_constant_uniform :
    ¬ (∀ x y : Fin 3,
      expectedMargin3 linearMargin3 uniform3 x =
        expectedMargin3 linearMargin3 uniform3 y) := by
  intro h
  have h01 := h 0 1
  rw [linear_expected_uniform_zero, linear_expected_uniform_one] at h01
  norm_num at h01

lemma linear_expected_not_constant_uniform_core :
    ¬ (∀ x y : Fin 3,
      expectedMargin linearMargin3 uniform3 x =
        expectedMargin linearMargin3 uniform3 y) := by
  intro h
  exact linear_expected_not_constant_uniform (by
    intro x y
    simpa [expectedMargin3_eq_expectedMargin] using h x y)

lemma cycle_uniform_of_expected_constant
    {q : Fin 3 → ℝ} (hsum : q 0 + q 1 + q 2 = 1)
    (hconst : ∀ x y : Fin 3,
      expectedMargin3 cycleMargin3 q x = expectedMargin3 cycleMargin3 q y) :
    q = uniform3 := by
  have h01 := hconst 0 1
  have h12 := hconst 1 2
  simp [expectedMargin3, cycleMargin3, Fin.sum_univ_three] at h01 h12
  funext x
  fin_cases x <;> simp [uniform3] <;> linarith

lemma uniform3_fullSupport : IsFullSupportLottery uniform3 := by
  constructor
  · intro x
    simp [uniform3]
  · simp [uniform3]

lemma nlhf_fixed_reference_expected_constant
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hfp : IsNLHFFixedPoint τ M ρ ρ) :
    ∀ x y : α, expectedMargin M ρ x = expectedMargin M ρ y := by
  classical
  let Z :=
    Finset.sum Finset.univ
      (fun z => ρ z * Real.exp (expectedMargin M ρ z / (2 * τ)))
  have hρ : IsFullSupportLottery ρ := hfp.2.1
  have hZpos : 0 < Z := by
    exact Finset.sum_pos
      (fun z hz => mul_pos (hρ.1 z) (Real.exp_pos _))
      Finset.univ_nonempty
  have hZ :
      ∀ x : α,
        Real.exp (expectedMargin M ρ x / (2 * τ)) = Z := by
    intro x
    have hx := hfp.2.2.2 x
    change
      ρ x =
        ρ x * Real.exp (expectedMargin M ρ x / (2 * τ)) / Z at hx
    have hxmul :
        ρ x * Z =
          ρ x * Real.exp (expectedMargin M ρ x / (2 * τ)) := by
      calc
        ρ x * Z =
            (ρ x * Real.exp (expectedMargin M ρ x / (2 * τ)) / Z) * Z := by
              exact congrArg (fun t => t * Z) hx
        _ = ρ x * Real.exp (expectedMargin M ρ x / (2 * τ)) := by
              field_simp [hZpos.ne']
    exact (mul_left_cancel₀ (hρ.1 x).ne' hxmul).symm
  intro x y
  have hdiv :
      expectedMargin M ρ x / (2 * τ) =
        expectedMargin M ρ y / (2 * τ) := by
    apply Real.exp_injective
    rw [hZ x, hZ y]
  have hden : (2 * τ) ≠ 0 := by nlinarith [hfp.1]
  exact (div_left_inj' hden).mp hdiv

lemma uniform3_is_cycle_fixed {τ : ℝ} (hτ : 0 < τ) :
    IsNLHFFixedPoint τ cycleMargin3 uniform3 uniform3 := by
  classical
  refine ⟨hτ, uniform3_fullSupport, uniform3_fullSupport, ?_⟩
  intro x
  have hx : expectedMargin cycleMargin3 uniform3 x = 0 :=
    cycle_expected_eq_zero_uniform_core x
  have hden :
      Finset.sum Finset.univ
        (fun z => uniform3 z *
          Real.exp (expectedMargin cycleMargin3 uniform3 z / (2 * τ))) = 1 := by
    calc
      Finset.sum Finset.univ
          (fun z => uniform3 z *
            Real.exp (expectedMargin cycleMargin3 uniform3 z / (2 * τ)))
          = Finset.sum Finset.univ (fun z => uniform3 z) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [cycle_expected_eq_zero_uniform_core z]
            simp
      _ = 1 := uniform3_fullSupport.2
  rw [hx, hden]
  simp

/-- Proposition `NLHFcomm` in the form proved in the paper: for any
positive `τ`, a rule satisfying the NLHF fixed-point characterization is not
commutative. -/
theorem NLHFcomm_from_fixed_point_characterization
    {τ : ℝ} (hτ : 0 < τ)
    (F : (Fin 3 → Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hfixed : ∀ (M : Fin 3 → Fin 3 → ℝ) (ρ : Fin 3 → ℝ),
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ → IsNLHFFixedPoint τ M ρ (F M ρ))
    (hunique : ∀ (M : Fin 3 → Fin 3 → ℝ) (ρ π : Fin 3 → ℝ),
      IsNormalizedMarginMatrix M → IsNLHFFixedPoint τ M ρ π → F M ρ = π) :
    F cycleMargin3 (F linearMargin3 uniform3) ≠
      F linearMargin3 (F cycleMargin3 uniform3) := by
  classical
  let q := F linearMargin3 uniform3
  have hCρ : F cycleMargin3 uniform3 = uniform3 :=
    hunique cycleMargin3 uniform3 uniform3 cycleMargin3_normalized
      (uniform3_is_cycle_fixed hτ)
  have hqfp : IsNLHFFixedPoint τ linearMargin3 uniform3 q :=
    hfixed linearMargin3 uniform3 linearMargin3_normalized uniform3_fullSupport
  have hq_full : IsFullSupportLottery q := hqfp.2.2.1
  have hq_ne : q ≠ uniform3 := by
    intro hqu
    have hfp_uniform : IsNLHFFixedPoint τ linearMargin3 uniform3 uniform3 := by
      simpa [q, hqu] using hqfp
    have hconst := nlhf_fixed_reference_expected_constant hfp_uniform
    exact linear_expected_not_constant_uniform_core hconst
  have hCq_ne : F cycleMargin3 q ≠ q := by
    intro hfix
    have hfpCq : IsNLHFFixedPoint τ cycleMargin3 q q := by
      simpa [hfix] using
        hfixed cycleMargin3 q cycleMargin3_normalized hq_full
    have hconstCore := nlhf_fixed_reference_expected_constant hfpCq
    have hsum : q 0 + q 1 + q 2 = 1 := by
      simpa [Fin.sum_univ_three] using hfpCq.2.1.2
    have hq_uniform : q = uniform3 :=
      cycle_uniform_of_expected_constant hsum (by
        intro x y
        simpa [expectedMargin3_eq_expectedMargin] using hconstCore x y)
    exact hq_ne hq_uniform
  intro hcomm
  have hleft : F cycleMargin3 q = q := by
    simpa [q, hCρ] using hcomm
  exact hCq_ne hleft

/-- Proposition `NLHFcomm`, stated with the project-level commutativity
predicate. -/
theorem NLHFcomm_violation_from_fixed_point_characterization
    {τ : ℝ} (hτ : 0 < τ)
    (F : MatrixRule (Fin 3))
    (hfixed : ∀ (M : Fin 3 → Fin 3 → ℝ) (ρ : Fin 3 → ℝ),
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ → IsNLHFFixedPoint τ M ρ (F M ρ))
    (hunique : ∀ (M : Fin 3 → Fin 3 → ℝ) (ρ π : Fin 3 → ℝ),
      IsNormalizedMarginMatrix M → IsNLHFFixedPoint τ M ρ π → F M ρ = π) :
    ViolatesCommutativity F := by
  intro hcomm
  have hcomm' :
      F cycleMargin3 (F linearMargin3 uniform3) =
        F linearMargin3 (F cycleMargin3 uniform3) :=
    (hcomm cycleMargin3 linearMargin3 uniform3
      cycleMargin3_normalized linearMargin3_normalized uniform3_fullSupport).symm
  exact
    NLHFcomm_from_fixed_point_characterization hτ F hfixed hunique
      hcomm'

end PaperFormalization
