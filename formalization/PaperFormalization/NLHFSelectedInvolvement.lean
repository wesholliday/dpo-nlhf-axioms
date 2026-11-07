import PaperFormalization.NLHFExistence
import PaperFormalization.NLHFInvolvement

open scoped BigOperators

namespace PaperFormalization

/-!
This file connects the fixed-point-certificate proof of Proposition
`InvolveViolNLHF` to the selected NLHF rule obtained from the closed-Sion
existence theorem.
-/

/-- The fixed-point characterization with uniform reference on three
alternatives is exactly the lower three-candidate fixed-point equation used in
the NLHF involvement proof, after the uniform factors cancel. -/
lemma lowerFixedPoint_of_nlhfFixedPoint_uniform3
    {τ : ℝ} (_hτ : 0 < τ) {q : Fin 3 → ℝ}
    (hfp : IsNLHFFixedPoint τ linearMargin3 uniform3 q) :
    IsNLHFLowerFixedPoint (1 / (2 * τ)) q := by
  classical
  refine ⟨hfp.2.2.1, ?_⟩
  intro u
  have hu := hfp.2.2.2 u
  have hden_ne :
      Finset.univ.sum
          (fun z : Fin 3 =>
            Real.exp ((1 / (2 * τ)) * expectedMargin linearMargin3 q z)) ≠
        0 := by
    exact (nlhfLowerZ_pos (1 / (2 * τ)) q).ne'
  calc
    q u =
        uniform3 u * Real.exp (expectedMargin linearMargin3 q u / (2 * τ)) /
          Finset.univ.sum
            (fun z : Fin 3 =>
              uniform3 z *
                Real.exp (expectedMargin linearMargin3 q z / (2 * τ))) := hu
    _ =
        ((1 : ℝ) / 3) *
            Real.exp ((1 / (2 * τ)) * expectedMargin linearMargin3 q u) /
          (((1 : ℝ) / 3) *
            Finset.univ.sum
              (fun z : Fin 3 =>
                Real.exp ((1 / (2 * τ)) *
                  expectedMargin linearMargin3 q z))) := by
        congr 2
        · simp
          ring_nf
        · simp [Fin.sum_univ_three, uniform3]
          ring_nf
    _ =
        Real.exp ((1 / (2 * τ)) * expectedMargin linearMargin3 q u) /
          Finset.univ.sum
            (fun z : Fin 3 =>
              Real.exp ((1 / (2 * τ)) *
                expectedMargin linearMargin3 q z)) := by
        field_simp [hden_ne]
    _ =
        Real.exp ((1 / (2 * τ)) * expectedMargin linearMargin3 q u) /
          nlhfLowerZ (1 / (2 * τ)) q := by
        rfl

/-- At parameter `0`, the lower three-candidate fixed point is the uniform
lottery. -/
lemma uniform3_is_lowerFixedPoint_zero :
    IsNLHFLowerFixedPoint 0 uniform3 := by
  constructor
  · exact uniform3_fullSupport
  · intro u
    have hZ : nlhfLowerZ 0 uniform3 = 3 := by
      simp [nlhfLowerZ]
    rw [hZ]
    fin_cases u <;> norm_num [uniform3]

lemma lowerFixedPoint_zero_unique {q : Fin 3 → ℝ}
    (hfixed : IsNLHFLowerFixedPoint 0 q) :
    q = uniform3 := by
  funext u
  have hZ : nlhfLowerZ 0 q = 3 := by
    simp [nlhfLowerZ]
  have hu := hfixed.2 u
  rw [hZ] at hu
  fin_cases u <;> simpa [uniform3] using hu

/-- Conversely, the lower fixed-point equation with positive parameter is the
uniform-reference NLHF fixed-point equation after setting `θ = 1/(2τ)`. -/
lemma nlhfFixedPoint_uniform3_of_lowerFixedPoint
    {θ τ : ℝ} (hτ : 0 < τ) (hθτ : θ = 1 / (2 * τ))
    {q : Fin 3 → ℝ}
    (hfixed : IsNLHFLowerFixedPoint θ q) :
    IsNLHFFixedPoint τ linearMargin3 uniform3 q := by
  classical
  refine ⟨hτ, uniform3_fullSupport, hfixed.1, ?_⟩
  intro u
  have hu := hfixed.2 u
  have hden_ne : nlhfLowerZ θ q ≠ 0 :=
    (nlhfLowerZ_pos θ q).ne'
  calc
    q u =
        Real.exp (θ * expectedMargin linearMargin3 q u) /
          nlhfLowerZ θ q := hu
    _ =
        ((1 : ℝ) / 3) *
            Real.exp (θ * expectedMargin linearMargin3 q u) /
          (((1 : ℝ) / 3) * nlhfLowerZ θ q) := by
        field_simp [hden_ne]
    _ =
        uniform3 u *
            Real.exp (expectedMargin linearMargin3 q u / (2 * τ)) /
          Finset.univ.sum
            (fun z : Fin 3 =>
              uniform3 z *
                Real.exp (expectedMargin linearMargin3 q z / (2 * τ))) := by
        congr 2
        · simp [hθτ]
          ring_nf
        · rw [hθτ]
          simp [nlhfLowerZ, Fin.sum_univ_three, uniform3]
          ring_nf

/-- The selected closed-Sion rule supplies a lower fixed point for every
nonnegative lower-profile parameter. -/
noncomputable def selectedLowerFixedPointOfClosedSion
    (hsion : SionClosedSaddleExistence (α := Fin 3)) (θ : ℝ) :
    Fin 3 → ℝ :=
  if θ = 0 then
    uniform3
  else
    selectedNLHFOfClosedSion hsion (1 / (2 * θ)) linearMargin3 uniform3

lemma selectedLowerFixedPointOfClosedSion_fixed
    (hsion : SionClosedSaddleExistence (α := Fin 3)) :
    ∀ θ : ℝ, 0 ≤ θ →
      IsNLHFLowerFixedPoint θ (selectedLowerFixedPointOfClosedSion hsion θ) := by
  intro θ hθ_nonneg
  by_cases hθ0 : θ = 0
  · subst θ
    simp [selectedLowerFixedPointOfClosedSion, uniform3_is_lowerFixedPoint_zero]
  · have hθpos : 0 < θ := lt_of_le_of_ne' hθ_nonneg hθ0
    have hτpos : 0 < 1 / (2 * θ) := by positivity
    have hfp :
        IsNLHFFixedPoint (1 / (2 * θ)) linearMargin3 uniform3
          (selectedNLHFOfClosedSion hsion (1 / (2 * θ)) linearMargin3 uniform3) :=
      selectedNLHFOfClosedSion_selection hsion hτpos linearMargin3_normalized
        uniform3_fullSupport
    have hlower :=
      lowerFixedPoint_of_nlhfFixedPoint_uniform3 hτpos hfp
    have hparam : 1 / (2 * (1 / (2 * θ))) = θ := by
      field_simp [hθpos.ne']
    have hparam' : 2 * θ * 2⁻¹ = θ := by ring
    simpa [selectedLowerFixedPointOfClosedSion, hθ0, hparam'] using hlower

lemma selectedLowerFixedPointOfClosedSion_unique
    (hsion : SionClosedSaddleExistence (α := Fin 3)) :
    ∀ θ : ℝ, 0 ≤ θ → ∀ r : Fin 3 → ℝ,
      IsNLHFLowerFixedPoint θ r →
        r = selectedLowerFixedPointOfClosedSion hsion θ := by
  intro θ hθ_nonneg r hfixed
  by_cases hθ0 : θ = 0
  · subst θ
    rw [lowerFixedPoint_zero_unique hfixed]
    simp [selectedLowerFixedPointOfClosedSion]
  · have hθpos : 0 < θ := lt_of_le_of_ne' hθ_nonneg hθ0
    have hτpos : 0 < 1 / (2 * θ) := by positivity
    have hparam : θ = 1 / (2 * (1 / (2 * θ))) := by
      field_simp [hθpos.ne']
    have hrfp :
        IsNLHFFixedPoint (1 / (2 * θ)) linearMargin3 uniform3 r :=
      nlhfFixedPoint_uniform3_of_lowerFixedPoint hτpos hparam hfixed
    have hsel :
        selectedNLHFOfClosedSion hsion (1 / (2 * θ)) linearMargin3 uniform3 = r :=
      selectedNLHFOfClosedSion_isTheNLHF hsion linearMargin3_normalized hrfp
    simpa [selectedLowerFixedPointOfClosedSion, hθ0] using hsel.symm

/-- The selected strict-KL rule supplies a lower fixed point for every
nonnegative lower-profile parameter. -/
noncomputable def selectedLowerFixedPointOfSionStrictKL
    (hexists : SionStrictKLFixedPointExistence (α := Fin 3)) (θ : ℝ) :
    Fin 3 → ℝ :=
  if θ = 0 then
    uniform3
  else
    selectedNLHFOfSionStrictKL hexists (1 / (2 * θ)) linearMargin3 uniform3

lemma selectedLowerFixedPointOfSionStrictKL_fixed
    (hexists : SionStrictKLFixedPointExistence (α := Fin 3)) :
    ∀ θ : ℝ, 0 ≤ θ →
      IsNLHFLowerFixedPoint θ
        (selectedLowerFixedPointOfSionStrictKL hexists θ) := by
  intro θ hθ_nonneg
  by_cases hθ0 : θ = 0
  · subst θ
    simp [selectedLowerFixedPointOfSionStrictKL, uniform3_is_lowerFixedPoint_zero]
  · have hθpos : 0 < θ := lt_of_le_of_ne' hθ_nonneg hθ0
    have hτpos : 0 < 1 / (2 * θ) := by positivity
    have hfp :
        IsNLHFFixedPoint (1 / (2 * θ)) linearMargin3 uniform3
          (selectedNLHFOfSionStrictKL hexists
            (1 / (2 * θ)) linearMargin3 uniform3) :=
      selectedNLHFOfSionStrictKL_selection hexists hτpos
        linearMargin3_normalized uniform3_fullSupport
    have hlower :=
      lowerFixedPoint_of_nlhfFixedPoint_uniform3 hτpos hfp
    have hparam : 1 / (2 * (1 / (2 * θ))) = θ := by
      field_simp [hθpos.ne']
    have hparam' : 2 * θ * 2⁻¹ = θ := by ring
    simpa [selectedLowerFixedPointOfSionStrictKL, hθ0, hparam'] using hlower

lemma selectedLowerFixedPointOfSionStrictKL_unique
    (hexists : SionStrictKLFixedPointExistence (α := Fin 3)) :
    ∀ θ : ℝ, 0 ≤ θ → ∀ r : Fin 3 → ℝ,
      IsNLHFLowerFixedPoint θ r →
        r = selectedLowerFixedPointOfSionStrictKL hexists θ := by
  intro θ hθ_nonneg r hfixed
  by_cases hθ0 : θ = 0
  · subst θ
    rw [lowerFixedPoint_zero_unique hfixed]
    simp [selectedLowerFixedPointOfSionStrictKL]
  · have hθpos : 0 < θ := lt_of_le_of_ne' hθ_nonneg hθ0
    have hτpos : 0 < 1 / (2 * θ) := by positivity
    have hparam : θ = 1 / (2 * (1 / (2 * θ))) := by
      field_simp [hθpos.ne']
    have hrfp :
        IsNLHFFixedPoint (1 / (2 * θ)) linearMargin3 uniform3 r :=
      nlhfFixedPoint_uniform3_of_lowerFixedPoint hτpos hparam hfixed
    have hsel :
        selectedNLHFOfSionStrictKL hexists
            (1 / (2 * θ)) linearMargin3 uniform3 = r :=
      selectedNLHFOfSionStrictKL_isTheNLHF hexists
        linearMargin3_normalized hrfp
    simpa [selectedLowerFixedPointOfSionStrictKL, hθ0] using hsel.symm

/-- The concrete positive-involvement margin witness from the displayed
linear-order profiles in the appendix. -/
def nlhfPositiveLinearAddsTopWitness
    (M M' : Fin 4 → Fin 4 → ℝ) (x : Fin 4) : Prop :=
  M = nlhfPositiveInvolvementMargin 1 ∧
    M' = nlhfPositiveInvolvementMargin ((1 : ℝ) / 3) ∧
      x = 0

/-- The concrete negative-involvement margin witness from the displayed
linear-order profiles in the appendix. -/
def nlhfNegativeLinearAddsBottomWitness
    (M M' : Fin 4 → Fin 4 → ℝ) (x : Fin 4) : Prop :=
  M = nlhfNegativeInvolvementMargin 0 ∧
    M' = nlhfNegativeInvolvementMargin ((1 : ℝ) / 3) ∧
      x = 0

lemma nlhfPositiveLinearAddsTopWitness_here :
    nlhfPositiveLinearAddsTopWitness
      (nlhfPositiveInvolvementMargin 1)
      (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) 0 := by
  exact ⟨rfl, rfl, rfl⟩

lemma nlhfNegativeLinearAddsBottomWitness_here :
    nlhfNegativeLinearAddsBottomWitness
      (nlhfNegativeInvolvementMargin 0)
      (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) 0 := by
  exact ⟨rfl, rfl, rfl⟩

lemma selectedNLHFOfSionStrictKL_positive_p_equation
    (hexists3 : SionStrictKLFixedPointExistence (α := Fin 3))
    (hexists4 : SionStrictKLFixedPointExistence (α := Fin 4))
    {τ s : ℝ} (hτ : 0 < τ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SolvesNLHFPEquation (Real.exp (1 / (2 * τ))) (1 / (2 * τ))
      (fun θ => nlhfLowerZ θ
        (selectedLowerFixedPointOfSionStrictKL hexists3 θ))
      s
      (selectedNLHFOfSionStrictKL hexists4 τ
        (nlhfPositiveInvolvementMargin s) uniform4 0) := by
  let π : Fin 4 → ℝ :=
    selectedNLHFOfSionStrictKL hexists4 τ
      (nlhfPositiveInvolvementMargin s) uniform4
  have hfp :
      IsNLHFFixedPoint τ (nlhfPositiveInvolvementMargin s) uniform4 π :=
    selectedNLHFOfSionStrictKL_selection hexists4 hτ
      (nlhfPositiveInvolvementMargin_normalized hs0 hs1)
      uniform4_fullSupport
  rcases nlhf_positive_scalar_equation_from_fixed hτ hfp with
    ⟨hp0, hp1, heq⟩
  refine ⟨hp0, hp1, ?_⟩
  have hdenpos : 0 < 1 - π 0 :=
    one_sub_pi0_pos_of_fullSupport4 hfp.2.2.1
  have hθ_nonneg :
      0 ≤ (1 / (2 * τ)) * s * (1 - π 0) :=
    mul_nonneg (mul_nonneg (by positivity) hs0) hdenpos.le
  have hcond :
      IsNLHFLowerFixedPoint ((1 / (2 * τ)) * s * (1 - π 0))
        (conditionedNonA nlhfPositiveLowerIndex π) :=
    nlhf_positive_conditioned_lower_fixed hτ hfp
  have hsame :
      conditionedNonA nlhfPositiveLowerIndex π =
        selectedLowerFixedPointOfSionStrictKL hexists3
          ((1 / (2 * τ)) * s * (1 - π 0)) :=
    selectedLowerFixedPointOfSionStrictKL_unique hexists3
      ((1 / (2 * τ)) * s * (1 - π 0)) hθ_nonneg
      (conditionedNonA nlhfPositiveLowerIndex π) hcond
  simpa [π, hsame] using heq

lemma selectedNLHFOfClosedSion_positive_p_equation
    (hsion3 : SionClosedSaddleExistence (α := Fin 3))
    (hsion4 : SionClosedSaddleExistence (α := Fin 4))
    {τ s : ℝ} (hτ : 0 < τ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SolvesNLHFPEquation (Real.exp (1 / (2 * τ))) (1 / (2 * τ))
      (fun θ => nlhfLowerZ θ (selectedLowerFixedPointOfClosedSion hsion3 θ))
      s
      (selectedNLHFOfClosedSion hsion4 τ
        (nlhfPositiveInvolvementMargin s) uniform4 0) := by
  let π : Fin 4 → ℝ :=
    selectedNLHFOfClosedSion hsion4 τ
      (nlhfPositiveInvolvementMargin s) uniform4
  have hfp :
      IsNLHFFixedPoint τ (nlhfPositiveInvolvementMargin s) uniform4 π :=
    selectedNLHFOfClosedSion_selection hsion4 hτ
      (nlhfPositiveInvolvementMargin_normalized hs0 hs1)
      uniform4_fullSupport
  rcases nlhf_positive_scalar_equation_from_fixed hτ hfp with
    ⟨hp0, hp1, heq⟩
  refine ⟨hp0, hp1, ?_⟩
  have hdenpos : 0 < 1 - π 0 :=
    one_sub_pi0_pos_of_fullSupport4 hfp.2.2.1
  have hθ_nonneg :
      0 ≤ (1 / (2 * τ)) * s * (1 - π 0) :=
    mul_nonneg (mul_nonneg (by positivity) hs0) hdenpos.le
  have hcond :
      IsNLHFLowerFixedPoint ((1 / (2 * τ)) * s * (1 - π 0))
        (conditionedNonA nlhfPositiveLowerIndex π) :=
    nlhf_positive_conditioned_lower_fixed hτ hfp
  have hsame :
      conditionedNonA nlhfPositiveLowerIndex π =
        selectedLowerFixedPointOfClosedSion hsion3
          ((1 / (2 * τ)) * s * (1 - π 0)) :=
    selectedLowerFixedPointOfClosedSion_unique hsion3
      ((1 / (2 * τ)) * s * (1 - π 0)) hθ_nonneg
      (conditionedNonA nlhfPositiveLowerIndex π) hcond
  simpa [π, hsame] using heq

lemma selectedNLHFOfSionStrictKL_negative_p_equation
    (hexists3 : SionStrictKLFixedPointExistence (α := Fin 3))
    (hexists4 : SionStrictKLFixedPointExistence (α := Fin 4))
    {τ s : ℝ} (hτ : 0 < τ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SolvesNLHFPEquation (Real.exp (-(1 / (2 * τ)))) (1 / (2 * τ))
      (fun θ => nlhfLowerZ θ
        (selectedLowerFixedPointOfSionStrictKL hexists3 θ))
      s
      (selectedNLHFOfSionStrictKL hexists4 τ
        (nlhfNegativeInvolvementMargin s) uniform4 0) := by
  let π : Fin 4 → ℝ :=
    selectedNLHFOfSionStrictKL hexists4 τ
      (nlhfNegativeInvolvementMargin s) uniform4
  have hfp :
      IsNLHFFixedPoint τ (nlhfNegativeInvolvementMargin s) uniform4 π :=
    selectedNLHFOfSionStrictKL_selection hexists4 hτ
      (nlhfNegativeInvolvementMargin_normalized hs0 hs1)
      uniform4_fullSupport
  rcases nlhf_negative_scalar_equation_from_fixed hτ hfp with
    ⟨hp0, hp1, heq⟩
  refine ⟨hp0, hp1, ?_⟩
  have hdenpos : 0 < 1 - π 0 :=
    one_sub_pi0_pos_of_fullSupport4 hfp.2.2.1
  have hθ_nonneg :
      0 ≤ (1 / (2 * τ)) * s * (1 - π 0) :=
    mul_nonneg (mul_nonneg (by positivity) hs0) hdenpos.le
  have hcond :
      IsNLHFLowerFixedPoint ((1 / (2 * τ)) * s * (1 - π 0))
        (conditionedNonA nlhfNegativeLowerIndex π) :=
    nlhf_negative_conditioned_lower_fixed hτ hfp
  have hsame :
      conditionedNonA nlhfNegativeLowerIndex π =
        selectedLowerFixedPointOfSionStrictKL hexists3
          ((1 / (2 * τ)) * s * (1 - π 0)) :=
    selectedLowerFixedPointOfSionStrictKL_unique hexists3
      ((1 / (2 * τ)) * s * (1 - π 0)) hθ_nonneg
      (conditionedNonA nlhfNegativeLowerIndex π) hcond
  simpa [π, hsame] using heq

lemma selectedNLHFOfClosedSion_negative_p_equation
    (hsion3 : SionClosedSaddleExistence (α := Fin 3))
    (hsion4 : SionClosedSaddleExistence (α := Fin 4))
    {τ s : ℝ} (hτ : 0 < τ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    SolvesNLHFPEquation (Real.exp (-(1 / (2 * τ)))) (1 / (2 * τ))
      (fun θ => nlhfLowerZ θ (selectedLowerFixedPointOfClosedSion hsion3 θ))
      s
      (selectedNLHFOfClosedSion hsion4 τ
        (nlhfNegativeInvolvementMargin s) uniform4 0) := by
  let π : Fin 4 → ℝ :=
    selectedNLHFOfClosedSion hsion4 τ
      (nlhfNegativeInvolvementMargin s) uniform4
  have hfp :
      IsNLHFFixedPoint τ (nlhfNegativeInvolvementMargin s) uniform4 π :=
    selectedNLHFOfClosedSion_selection hsion4 hτ
      (nlhfNegativeInvolvementMargin_normalized hs0 hs1)
      uniform4_fullSupport
  rcases nlhf_negative_scalar_equation_from_fixed hτ hfp with
    ⟨hp0, hp1, heq⟩
  refine ⟨hp0, hp1, ?_⟩
  have hdenpos : 0 < 1 - π 0 :=
    one_sub_pi0_pos_of_fullSupport4 hfp.2.2.1
  have hθ_nonneg :
      0 ≤ (1 / (2 * τ)) * s * (1 - π 0) :=
    mul_nonneg (mul_nonneg (by positivity) hs0) hdenpos.le
  have hcond :
      IsNLHFLowerFixedPoint ((1 / (2 * τ)) * s * (1 - π 0))
        (conditionedNonA nlhfNegativeLowerIndex π) :=
    nlhf_negative_conditioned_lower_fixed hτ hfp
  have hsame :
      conditionedNonA nlhfNegativeLowerIndex π =
        selectedLowerFixedPointOfClosedSion hsion3
          ((1 / (2 * τ)) * s * (1 - π 0)) :=
    selectedLowerFixedPointOfClosedSion_unique hsion3
      ((1 / (2 * τ)) * s * (1 - π 0)) hθ_nonneg
      (conditionedNonA nlhfNegativeLowerIndex π) hcond
  simpa [π, hsame] using heq

/-- Positive involvement violation from scalar equations on the unit interval,
which is the normalized-margin range used by the paper's witness. -/
theorem nlhf_positive_involvement_violation_from_unit_scalar_certificate
    (F : MatrixRule (Fin 4))
    (AddsTop : (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop)
    {A lam : ℝ} {Z pA : ℝ → ℝ}
    (hA : 0 < A) (hlam : 0 < lam)
    (hZpos : PositiveOnNonneg Z)
    (hZdec : StrictlyDecreasingOnNonneg Z)
    (hsolve : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      SolvesNLHFPEquation A lam Z s (pA s))
    (hselect : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      F (nlhfPositiveInvolvementMargin s) uniform4 0 = pA s)
    (hAdds :
      AddsTop (nlhfPositiveInvolvementMargin 1)
        (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) 0) :
    ViolatesPositiveInvolvement F AddsTop := by
  intro hsatisfies
  have hdrop_p :
      pA ((1 : ℝ) / 3) < pA 1 :=
    nlhfP_comparison hA hlam hZpos hZdec
      (by norm_num : 0 ≤ (1 : ℝ) / 3)
      (by norm_num : (1 : ℝ) / 3 < 1)
      (hsolve ((1 : ℝ) / 3) (by norm_num) (by norm_num))
      (hsolve 1 (by norm_num) (by norm_num))
  have hdrop :
      F (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) uniform4 0 <
        F (nlhfPositiveInvolvementMargin 1) uniform4 0 := by
    rw [hselect ((1 : ℝ) / 3) (by norm_num) (by norm_num),
      hselect 1 (by norm_num) (by norm_num)]
    exact hdrop_p
  have hle :=
    hsatisfies (nlhfPositiveInvolvementMargin 1)
      (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) uniform4 0
      (nlhfPositiveInvolvementMargin_normalized (by norm_num) (by norm_num))
      (nlhfPositiveInvolvementMargin_normalized (by norm_num) (by norm_num))
      uniform4_fullSupport hAdds
  linarith

/-- Negative involvement violation from scalar equations on the unit interval,
which is the normalized-margin range used by the paper's witness. -/
theorem nlhf_negative_involvement_violation_from_unit_scalar_certificate
    (F : MatrixRule (Fin 4))
    (AddsBottom : (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop)
    {A lam : ℝ} {Z pA : ℝ → ℝ}
    (hA : 0 < A) (hlam : 0 < lam)
    (hZpos : PositiveOnNonneg Z)
    (hZdec : StrictlyDecreasingOnNonneg Z)
    (hsolve : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      SolvesNLHFPEquation A lam Z s (pA s))
    (hselect : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      F (nlhfNegativeInvolvementMargin s) uniform4 0 = pA s)
    (hAdds :
      AddsBottom (nlhfNegativeInvolvementMargin 0)
        (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) 0) :
    ViolatesNegativeInvolvement F AddsBottom := by
  intro hsatisfies
  have hincrease_p :
      pA 0 < pA ((1 : ℝ) / 3) :=
    nlhfP_comparison hA hlam hZpos hZdec
      (by norm_num : 0 ≤ (0 : ℝ))
      (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)
      (hsolve 0 (by norm_num) (by norm_num))
      (hsolve ((1 : ℝ) / 3) (by norm_num) (by norm_num))
  have hincrease :
      F (nlhfNegativeInvolvementMargin 0) uniform4 0 <
        F (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) uniform4 0 := by
    rw [hselect 0 (by norm_num) (by norm_num),
      hselect ((1 : ℝ) / 3) (by norm_num) (by norm_num)]
    exact hincrease_p
  have hle :=
    hsatisfies (nlhfNegativeInvolvementMargin 0)
      (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) uniform4 0
      (nlhfNegativeInvolvementMargin_normalized (by norm_num) (by norm_num))
      (nlhfNegativeInvolvementMargin_normalized (by norm_num) (by norm_num))
      uniform4_fullSupport hAdds
  linarith

/-- Proposition `InvolveViolNLHF` for the selected strict-KL NLHF rule, in the
concrete four-candidate linear-profile witness form. -/
theorem selectedNLHFOfSionStrictKL_involvement_violation
    (hexists3 : SionStrictKLFixedPointExistence (α := Fin 3))
    (hexists4 : SionStrictKLFixedPointExistence (α := Fin 4))
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesPositiveInvolvement
        ((selectedNLHFOfSionStrictKL hexists4) τ)
        nlhfPositiveLinearAddsTopWitness ∧
      ViolatesNegativeInvolvement
        ((selectedNLHFOfSionStrictKL hexists4) τ)
        nlhfNegativeLinearAddsBottomWitness := by
  let Z : ℝ → ℝ := fun θ =>
    nlhfLowerZ θ (selectedLowerFixedPointOfSionStrictKL hexists3 θ)
  have hZpos : PositiveOnNonneg Z := by
    intro θ _hθ
    exact nlhfLowerZ_pos θ
      (selectedLowerFixedPointOfSionStrictKL hexists3 θ)
  have hZdec : StrictlyDecreasingOnNonneg Z :=
    Z_strictly_decreasing_from_lower_fixed_selection_fin3
      (selectedLowerFixedPointOfSionStrictKL_fixed hexists3)
  constructor
  · exact
      nlhf_positive_involvement_violation_from_unit_scalar_certificate
        ((selectedNLHFOfSionStrictKL hexists4) τ)
        nlhfPositiveLinearAddsTopWitness
        (Real.exp_pos _) (by positivity : 0 < 1 / (2 * τ))
        hZpos hZdec
        (fun s hs0 hs1 =>
          selectedNLHFOfSionStrictKL_positive_p_equation
            hexists3 hexists4 hτ hs0 hs1)
        (fun s _hs0 _hs1 => rfl)
        nlhfPositiveLinearAddsTopWitness_here
  · exact
      nlhf_negative_involvement_violation_from_unit_scalar_certificate
        ((selectedNLHFOfSionStrictKL hexists4) τ)
        nlhfNegativeLinearAddsBottomWitness
        (Real.exp_pos _) (by positivity : 0 < 1 / (2 * τ))
        hZpos hZdec
        (fun s hs0 hs1 =>
          selectedNLHFOfSionStrictKL_negative_p_equation
            hexists3 hexists4 hτ hs0 hs1)
        (fun s _hs0 _hs1 => rfl)
        nlhfNegativeLinearAddsBottomWitness_here

/-- Proposition `InvolveViolNLHF` for the selected NLHF rule, using the proved
Sion specialization. -/
theorem selectedNLHF_involvement_violation
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesPositiveInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        nlhfPositiveLinearAddsTopWitness ∧
      ViolatesNegativeInvolvement
        ((selectedNLHF (α := Fin 4)) τ)
        nlhfNegativeLinearAddsBottomWitness := by
  simpa [selectedNLHF] using
    selectedNLHFOfSionStrictKL_involvement_violation
      (fixedPointExistence_of_closedSion sionClosedSaddleExistence)
      (fixedPointExistence_of_closedSion sionClosedSaddleExistence)
      hτ

/-- Proposition `InvolveViolNLHF` for the selected closed-Sion NLHF rule, in
the concrete four-candidate linear-profile witness form. -/
theorem selectedNLHFOfClosedSion_involvement_violation
    (hsion3 : SionClosedSaddleExistence (α := Fin 3))
    (hsion4 : SionClosedSaddleExistence (α := Fin 4))
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesPositiveInvolvement
        ((selectedNLHFOfClosedSion hsion4) τ)
        nlhfPositiveLinearAddsTopWitness ∧
      ViolatesNegativeInvolvement
        ((selectedNLHFOfClosedSion hsion4) τ)
        nlhfNegativeLinearAddsBottomWitness := by
  let Z : ℝ → ℝ := fun θ =>
    nlhfLowerZ θ (selectedLowerFixedPointOfClosedSion hsion3 θ)
  have hZpos : PositiveOnNonneg Z := by
    intro θ _hθ
    exact nlhfLowerZ_pos θ (selectedLowerFixedPointOfClosedSion hsion3 θ)
  have hZdec : StrictlyDecreasingOnNonneg Z :=
    Z_strictly_decreasing_from_lower_fixed_selection_fin3
      (selectedLowerFixedPointOfClosedSion_fixed hsion3)
  constructor
  · exact
      nlhf_positive_involvement_violation_from_unit_scalar_certificate
        ((selectedNLHFOfClosedSion hsion4) τ)
        nlhfPositiveLinearAddsTopWitness
        (Real.exp_pos _) (by positivity : 0 < 1 / (2 * τ))
        hZpos hZdec
        (fun s hs0 hs1 =>
          selectedNLHFOfClosedSion_positive_p_equation
            hsion3 hsion4 hτ hs0 hs1)
        (fun s _hs0 _hs1 => rfl)
        nlhfPositiveLinearAddsTopWitness_here
  · exact
      nlhf_negative_involvement_violation_from_unit_scalar_certificate
        ((selectedNLHFOfClosedSion hsion4) τ)
        nlhfNegativeLinearAddsBottomWitness
        (Real.exp_pos _) (by positivity : 0 < 1 / (2 * τ))
        hZpos hZdec
        (fun s hs0 hs1 =>
          selectedNLHFOfClosedSion_negative_p_equation
            hsion3 hsion4 hτ hs0 hs1)
        (fun s _hs0 _hs1 => rfl)
        nlhfNegativeLinearAddsBottomWitness_here

/-- Proposition `InvolveViolNLHF` with genuine profile-level witnesses: the
margin matrices are realized by actual linear-order profiles, and the added
voter provably ranks `a` first (resp. last).  Obtained by transporting the
bare-witness violation through the profile-realization lemmas of
`NLHFInvolvement.lean`. -/
theorem selectedNLHF_involvement_violation_profileRealization
    {τ : ℝ} (hτ : 0 < τ) :
    ViolatesPositiveInvolvement ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsTopMargins ∧
      ViolatesNegativeInvolvement ((selectedNLHF (α := Fin 4)) τ)
        LinearOrderAddsBottomMargins := by
  obtain ⟨hpos, hneg⟩ := selectedNLHF_involvement_violation hτ
  refine ⟨violatesPositiveInvolvement_of_subpredicate ?_ hpos,
    violatesNegativeInvolvement_of_subpredicate ?_ hneg⟩
  · rintro M M' x ⟨rfl, rfl, rfl⟩
    exact nlhfLinearAddsTopRealization_witness
  · rintro M M' x ⟨rfl, rfl, rfl⟩
    exact nlhfLinearAddsBottomRealization_witness

end PaperFormalization
