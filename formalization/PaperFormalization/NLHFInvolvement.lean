import PaperFormalization.Core
import PaperFormalization.Involvement
import PaperFormalization.NLHFCommutativity
import PaperFormalization.ProfileBorda
import PaperFormalization.WeakProfileBorda

open scoped BigOperators
open scoped Topology
open Filter Set

namespace PaperFormalization

/-- The monotonicity hypothesis on the normalizing factor `Z` from Lemma
`Z-decreasing`: on the nonnegative half-line, larger arguments give strictly
smaller values. -/
def StrictlyDecreasingOnNonneg (Z : ℝ → ℝ) : Prop :=
  ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ → Z θ₂ < Z θ₁

def PositiveOnNonneg (Z : ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, 0 ≤ θ → 0 < Z θ

/-- The scalar equation used in Lemma `p-comparison`.
Here `lambda` is the inverse-temperature coefficient `1 / (2 * tau)` from
the NLHF fixed-point equation. -/
def SolvesNLHFPEquation (A lambda : ℝ) (Z : ℝ → ℝ) (s p : ℝ) : Prop :=
  0 < p ∧ p < 1 ∧ p / (1 - p) = A / Z (lambda * s * (1 - p))

noncomputable def nlhfLowerZ (θ : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  Finset.sum Finset.univ
    (fun u => Real.exp (θ * expectedMargin linearMargin3 q u))

def IsNLHFLowerFixedPoint (θ : ℝ) (q : Fin 3 → ℝ) : Prop :=
  IsFullSupportLottery q ∧
    ∀ u : Fin 3,
      q u = Real.exp (θ * expectedMargin linearMargin3 q u) / nlhfLowerZ θ q

lemma log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ x - 1 := by
  by_cases hx1 : x = 1
  · subst x
    simp
  · exact (Real.log_lt_sub_one_of_pos hx hx1).le

lemma KL_term_gap_nonneg {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    p - r ≤ p * Real.log (p / r) := by
  have hratio_pos : 0 < r / p := div_pos hr hp
  have hlog_le : Real.log (r / p) ≤ r / p - 1 :=
    log_le_sub_one_of_pos hratio_pos
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

lemma KL_term_gap_pos_of_ne {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hne : p ≠ r) :
    p - r < p * Real.log (p / r) := by
  have hratio_pos : 0 < r / p := div_pos hr hp
  have hratio_ne : r / p ≠ 1 := by
    intro h
    have : r = p := by
      field_simp [hp.ne'] at h
      linarith
    exact hne this.symm
  have hlog_lt : Real.log (r / p) < r / p - 1 :=
    Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
  have hlog_neg : Real.log (p / r) = -Real.log (r / p) := by
    rw [Real.log_div hp.ne' hr.ne', Real.log_div hr.ne' hp.ne']
    ring
  rw [hlog_neg]
  have hmul := mul_lt_mul_of_pos_left hlog_lt hp
  have hmul' : p * Real.log (r / p) < r - p := by
    calc
      p * Real.log (r / p) < p * (r / p - 1) := hmul
      _ = r - p := by
        field_simp [hp.ne']
  nlinarith

lemma KL_nonneg_of_fullSupport_fin3
    {π ρ : Fin 3 → ℝ}
    (hπ : IsFullSupportLottery π) (hρ : IsFullSupportLottery ρ) :
    0 ≤ KL π ρ := by
  have h0 := KL_term_gap_nonneg (hπ.1 0) (hρ.1 0)
  have h1 := KL_term_gap_nonneg (hπ.1 1) (hρ.1 1)
  have h2 := KL_term_gap_nonneg (hπ.1 2) (hρ.1 2)
  have hπsum : π 0 + π 1 + π 2 = 1 := by
    simpa [Fin.sum_univ_three] using hπ.2
  have hρsum : ρ 0 + ρ 1 + ρ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hρ.2
  simp [KL, Fin.sum_univ_three]
  nlinarith

lemma fin3_function_ne_iff_coords
    {π ρ : Fin 3 → ℝ} :
    π ≠ ρ ↔ π 0 ≠ ρ 0 ∨ π 1 ≠ ρ 1 ∨ π 2 ≠ ρ 2 := by
  constructor
  · intro hne
    by_cases h0 : π 0 = ρ 0
    · by_cases h1 : π 1 = ρ 1
      · by_cases h2 : π 2 = ρ 2
        · exfalso
          exact hne (by
            funext x
            fin_cases x <;> assumption)
        · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl h1)
    · exact Or.inl h0
  · intro h heq
    rcases h with h | h | h <;> exact h (congrFun heq _)

lemma KL_pos_of_fullSupport_ne_fin3
    {π ρ : Fin 3 → ℝ}
    (hπ : IsFullSupportLottery π) (hρ : IsFullSupportLottery ρ)
    (hne : π ≠ ρ) :
    0 < KL π ρ := by
  have h0 := KL_term_gap_nonneg (hπ.1 0) (hρ.1 0)
  have h1 := KL_term_gap_nonneg (hπ.1 1) (hρ.1 1)
  have h2 := KL_term_gap_nonneg (hπ.1 2) (hρ.1 2)
  have hπsum : π 0 + π 1 + π 2 = 1 := by
    simpa [Fin.sum_univ_three] using hπ.2
  have hρsum : ρ 0 + ρ 1 + ρ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hρ.2
  rcases (fin3_function_ne_iff_coords.mp hne) with hne0 | hne1 | hne2
  · have hs := KL_term_gap_pos_of_ne (hπ.1 0) (hρ.1 0) hne0
    simp [KL, Fin.sum_univ_three]
    nlinarith
  · have hs := KL_term_gap_pos_of_ne (hπ.1 1) (hρ.1 1) hne1
    simp [KL, Fin.sum_univ_three]
    nlinarith
  · have hs := KL_term_gap_pos_of_ne (hπ.1 2) (hρ.1 2) hne2
    simp [KL, Fin.sum_univ_three]
    nlinarith

lemma nlhfLowerZ_pos (θ : ℝ) (q : Fin 3 → ℝ) :
    0 < nlhfLowerZ θ q := by
  unfold nlhfLowerZ
  exact Finset.sum_pos
    (fun u _hu => Real.exp_pos (θ * expectedMargin linearMargin3 q u))
    Finset.univ_nonempty

lemma lower_log_equation_of_fixed
    {θ : ℝ} {q : Fin 3 → ℝ}
    (hfixed : IsNLHFLowerFixedPoint θ q) :
    ∀ u : Fin 3,
      Real.log (q u) =
        θ * expectedMargin linearMargin3 q u - Real.log (nlhfLowerZ θ q) := by
  intro u
  have hZpos : 0 < nlhfLowerZ θ q := nlhfLowerZ_pos θ q
  have hqu := hfixed.2 u
  rw [hqu]
  rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne']
  rw [Real.log_exp]

lemma linearMargin3_expected_not_constant_of_fullSupport
    {q : Fin 3 → ℝ} (hq : IsFullSupportLottery q) :
    ¬ (∀ x y : Fin 3,
      expectedMargin linearMargin3 q x = expectedMargin linearMargin3 q y) := by
  intro hconst
  have h02 := hconst 0 2
  have hq0 : 0 < q 0 := hq.1 0
  have hq1 : 0 < q 1 := hq.1 1
  have hq2 : 0 < q 2 := hq.1 2
  simp [expectedMargin, linearMargin3, Fin.sum_univ_three] at h02
  nlinarith

lemma lower_fixed_same_solution_impossible
    {θ₁ θ₂ h₁ h₂ : ℝ} {q : Fin 3 → ℝ}
    (hθ : θ₁ < θ₂)
    (hq : IsFullSupportLottery q)
    (hlog₁ : ∀ u : Fin 3,
      Real.log (q u) = θ₁ * expectedMargin linearMargin3 q u - h₁)
    (hlog₂ : ∀ u : Fin 3,
      Real.log (q u) = θ₂ * expectedMargin linearMargin3 q u - h₂) :
    False := by
  have hconst :
      ∀ x y : Fin 3,
        expectedMargin linearMargin3 q x =
          expectedMargin linearMargin3 q y := by
    intro x y
    have hx := hlog₁ x
    have hx₂ := hlog₂ x
    have hy := hlog₁ y
    have hy₂ := hlog₂ y
    have hxrel :
        (θ₂ - θ₁) * expectedMargin linearMargin3 q x = h₂ - h₁ := by
      linarith
    have hyrel :
        (θ₂ - θ₁) * expectedMargin linearMargin3 q y = h₂ - h₁ := by
      linarith
    have hcoef : θ₂ - θ₁ ≠ 0 := by linarith
    exact (mul_left_cancel₀ hcoef (by linarith : (θ₂ - θ₁) *
      expectedMargin linearMargin3 q x =
        (θ₂ - θ₁) * expectedMargin linearMargin3 q y))
  exact linearMargin3_expected_not_constant_of_fullSupport hq hconst

lemma lower_fixed_selection_injective_from_log_equations
    {q : ℝ → Fin 3 → ℝ} {h : ℝ → ℝ}
    (hq : ∀ θ : ℝ, 0 ≤ θ → IsFullSupportLottery (q θ))
    (hlog : ∀ θ : ℝ, 0 ≤ θ → ∀ u : Fin 3,
      Real.log (q θ u) = θ * expectedMargin linearMargin3 (q θ) u - h θ) :
    ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ → q θ₁ ≠ q θ₂ := by
  intro θ₁ θ₂ hθ₁ hlt hsame
  have hθ₂ : 0 ≤ θ₂ := by linarith
  have hq₁ : IsFullSupportLottery (q θ₁) := hq θ₁ hθ₁
  have hlog₁ :
      ∀ u : Fin 3,
        Real.log (q θ₁ u) =
          θ₁ * expectedMargin linearMargin3 (q θ₁) u - h θ₁ :=
    hlog θ₁ hθ₁
  have hlog₂ :
      ∀ u : Fin 3,
        Real.log (q θ₁ u) =
          θ₂ * expectedMargin linearMargin3 (q θ₁) u - h θ₂ := by
    intro u
    simpa [hsame] using hlog θ₂ hθ₂ u
  exact lower_fixed_same_solution_impossible hlt hq₁ hlog₁ hlog₂

lemma lower_fixed_selection_injective
    {q : ℝ → Fin 3 → ℝ}
    (hfixed : ∀ θ : ℝ, 0 ≤ θ → IsNLHFLowerFixedPoint θ (q θ)) :
    ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ → q θ₁ ≠ q θ₂ := by
  refine lower_fixed_selection_injective_from_log_equations
    (h := fun θ => Real.log (nlhfLowerZ θ (q θ))) ?_ ?_
  · intro θ hθ
    exact (hfixed θ hθ).1
  · intro θ hθ u
    exact lower_log_equation_of_fixed (hfixed θ hθ) u

lemma lower_KL_forward_identity_from_log
    {θ₁ θ₂ h₁ h₂ : ℝ} {q₁ q₂ : Fin 3 → ℝ}
    (hq₁ : IsFullSupportLottery q₁)
    (hq₂ : IsFullSupportLottery q₂)
    (hlog₁ : ∀ u : Fin 3,
      Real.log (q₁ u) = θ₁ * expectedMargin linearMargin3 q₁ u - h₁)
    (hlog₂ : ∀ u : Fin 3,
      Real.log (q₂ u) = θ₂ * expectedMargin linearMargin3 q₂ u - h₂) :
    KL q₁ q₂ = θ₂ * marginValue linearMargin3 q₂ q₁ - h₁ + h₂ := by
  have hself₁ : marginValue linearMargin3 q₁ q₁ = 0 := by
    simp [marginValue, linearMargin3, Fin.sum_univ_three]
    ring
  have hsum₁ : q₁ 0 + q₁ 1 + q₁ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hq₁.2
  have hsum₁h₁ : q₁ 0 * h₁ + q₁ 1 * h₁ + q₁ 2 * h₁ = h₁ := by
    calc
      q₁ 0 * h₁ + q₁ 1 * h₁ + q₁ 2 * h₁ =
          (q₁ 0 + q₁ 1 + q₁ 2) * h₁ := by ring
      _ = 1 * h₁ := by rw [hsum₁]
      _ = h₁ := by ring
  have hsum₁h₂ : q₁ 0 * h₂ + q₁ 1 * h₂ + q₁ 2 * h₂ = h₂ := by
    calc
      q₁ 0 * h₂ + q₁ 1 * h₂ + q₁ 2 * h₂ =
          (q₁ 0 + q₁ 1 + q₁ 2) * h₂ := by ring
      _ = 1 * h₂ := by rw [hsum₁]
      _ = h₂ := by ring
  have hq₁0 : q₁ 0 ≠ 0 := (hq₁.1 0).ne'
  have hq₁1 : q₁ 1 ≠ 0 := (hq₁.1 1).ne'
  have hq₁2 : q₁ 2 ≠ 0 := (hq₁.1 2).ne'
  have hq₂0 : q₂ 0 ≠ 0 := (hq₂.1 0).ne'
  have hq₂1 : q₂ 1 ≠ 0 := (hq₂.1 1).ne'
  have hq₂2 : q₂ 2 ≠ 0 := (hq₂.1 2).ne'
  simp [KL, expectedMargin, marginValue, linearMargin3, Fin.sum_univ_three,
    Real.log_div, hq₁0, hq₁1, hq₁2, hq₂0, hq₂1, hq₂2,
    hlog₁, hlog₂] at hself₁ ⊢
  ring_nf at hself₁ hsum₁h₁ hsum₁h₂ ⊢
  nlinarith

lemma lower_KL_reverse_identity_from_log
    {θ₁ θ₂ h₁ h₂ : ℝ} {q₁ q₂ : Fin 3 → ℝ}
    (hq₁ : IsFullSupportLottery q₁)
    (hq₂ : IsFullSupportLottery q₂)
    (hlog₁ : ∀ u : Fin 3,
      Real.log (q₁ u) = θ₁ * expectedMargin linearMargin3 q₁ u - h₁)
    (hlog₂ : ∀ u : Fin 3,
      Real.log (q₂ u) = θ₂ * expectedMargin linearMargin3 q₂ u - h₂) :
    KL q₂ q₁ = h₁ - h₂ - θ₁ * marginValue linearMargin3 q₂ q₁ := by
  have hself₂ : marginValue linearMargin3 q₂ q₂ = 0 := by
    simp [marginValue, linearMargin3, Fin.sum_univ_three]
    ring
  have hsum₂ : q₂ 0 + q₂ 1 + q₂ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hq₂.2
  have hsum₂h₁ : q₂ 0 * h₁ + q₂ 1 * h₁ + q₂ 2 * h₁ = h₁ := by
    calc
      q₂ 0 * h₁ + q₂ 1 * h₁ + q₂ 2 * h₁ =
          (q₂ 0 + q₂ 1 + q₂ 2) * h₁ := by ring
      _ = 1 * h₁ := by rw [hsum₂]
      _ = h₁ := by ring
  have hsum₂h₂ : q₂ 0 * h₂ + q₂ 1 * h₂ + q₂ 2 * h₂ = h₂ := by
    calc
      q₂ 0 * h₂ + q₂ 1 * h₂ + q₂ 2 * h₂ =
          (q₂ 0 + q₂ 1 + q₂ 2) * h₂ := by ring
      _ = 1 * h₂ := by rw [hsum₂]
      _ = h₂ := by ring
  have hq₁0 : q₁ 0 ≠ 0 := (hq₁.1 0).ne'
  have hq₁1 : q₁ 1 ≠ 0 := (hq₁.1 1).ne'
  have hq₁2 : q₁ 2 ≠ 0 := (hq₁.1 2).ne'
  have hq₂0 : q₂ 0 ≠ 0 := (hq₂.1 0).ne'
  have hq₂1 : q₂ 1 ≠ 0 := (hq₂.1 1).ne'
  have hq₂2 : q₂ 2 ≠ 0 := (hq₂.1 2).ne'
  simp [KL, expectedMargin, marginValue, linearMargin3, Fin.sum_univ_three,
    Real.log_div, hq₁0, hq₁1, hq₁2, hq₂0, hq₂1, hq₂2,
    hlog₁, hlog₂] at hself₂ ⊢
  ring_nf at hself₂ hsum₂h₁ hsum₂h₂ ⊢
  nlinarith

/-- The order-theoretic end of Lemma `Z-decreasing`.  The hypotheses are the
two displayed KL identities in the paper plus standard KL
nonnegativity/strictness. -/
theorem Z_strictly_decreasing_from_KL_identities
    {Z h : ℝ → ℝ} {q : ℝ → Fin 3 → ℝ}
    {cross kl12 kl21 : ℝ → ℝ → ℝ}
    (hZexp : ∀ θ : ℝ, Z θ = Real.exp (h θ))
    (hqne : ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ → q θ₁ ≠ q θ₂)
    (hkl12_nonneg : ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ →
      0 ≤ kl12 θ₁ θ₂)
    (hkl21_nonneg : ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ →
      0 ≤ kl21 θ₁ θ₂)
    (hkl21_pos_of_ne : ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ →
      q θ₁ ≠ q θ₂ → 0 < kl21 θ₁ θ₂)
    (hsum : ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ →
      kl12 θ₁ θ₂ + kl21 θ₁ θ₂ = (θ₂ - θ₁) * cross θ₁ θ₂)
    (hkl21 : ∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ < θ₂ →
      kl21 θ₁ θ₂ = h θ₁ - h θ₂ - θ₁ * cross θ₁ θ₂) :
    StrictlyDecreasingOnNonneg Z := by
  intro θ₁ θ₂ hθ₁ hlt
  have hdiff_pos : 0 < θ₂ - θ₁ := by linarith
  have hqdiff : q θ₁ ≠ q θ₂ := hqne θ₁ θ₂ hθ₁ hlt
  have hkl12nn : 0 ≤ kl12 θ₁ θ₂ := hkl12_nonneg θ₁ θ₂ hθ₁ hlt
  have hkl21nn : 0 ≤ kl21 θ₁ θ₂ := hkl21_nonneg θ₁ θ₂ hθ₁ hlt
  have hcross_pos : 0 < cross θ₁ θ₂ := by
    have hsum' := hsum θ₁ θ₂ hθ₁ hlt
    have hsum_pos : 0 < kl12 θ₁ θ₂ + kl21 θ₁ θ₂ := by
      by_cases hkl12zero : kl12 θ₁ θ₂ = 0
      · have hkl21pos := hkl21_pos_of_ne θ₁ θ₂ hθ₁ hlt hqdiff
        nlinarith
      · have hkl12pos : 0 < kl12 θ₁ θ₂ :=
          lt_of_le_of_ne hkl12nn (Ne.symm hkl12zero)
        nlinarith
    nlinarith
  have hhpos : 0 < h θ₁ - h θ₂ := by
    have hkl21eq := hkl21 θ₁ θ₂ hθ₁ hlt
    by_cases hθ₁pos : 0 < θ₁
    · nlinarith
    · have hθ₁zero : θ₁ = 0 := le_antisymm (le_of_not_gt hθ₁pos) hθ₁
      have hkl21pos := hkl21_pos_of_ne θ₁ θ₂ hθ₁ hlt hqdiff
      nlinarith
  have hexp_lt : Real.exp (h θ₂) < Real.exp (h θ₁) :=
    Real.exp_lt_exp.mpr (by linarith)
  simpa [hZexp θ₁, hZexp θ₂] using hexp_lt

/-- Lemma `Z-decreasing` from the appendix, with only the standard
finite-simplex facts about KL divergence left as hypotheses. -/
theorem Z_strictly_decreasing_from_lower_fixed_selection
    {q : ℝ → Fin 3 → ℝ}
    (hfixed : ∀ θ : ℝ, 0 ≤ θ → IsNLHFLowerFixedPoint θ (q θ))
    (hKL_nonneg : ∀ p r : Fin 3 → ℝ,
      IsFullSupportLottery p → IsFullSupportLottery r → 0 ≤ KL p r)
    (hKL_pos_of_ne : ∀ p r : Fin 3 → ℝ,
      IsFullSupportLottery p → IsFullSupportLottery r → p ≠ r → 0 < KL p r) :
    StrictlyDecreasingOnNonneg (fun θ : ℝ => nlhfLowerZ θ (q θ)) := by
  refine Z_strictly_decreasing_from_KL_identities
    (q := q)
    (h := fun θ => Real.log (nlhfLowerZ θ (q θ)))
    (cross := fun θ₁ θ₂ =>
      marginValue linearMargin3 (q θ₂) (q θ₁))
    (kl12 := fun θ₁ θ₂ => KL (q θ₁) (q θ₂))
    (kl21 := fun θ₁ θ₂ => KL (q θ₂) (q θ₁))
    ?hZexp ?hqne ?hkl12nn ?hkl21nn ?hkl21pos ?hsum ?hkl21
  · intro θ
    exact (Real.exp_log (nlhfLowerZ_pos θ (q θ))).symm
  · exact lower_fixed_selection_injective hfixed
  · intro θ₁ θ₂ hθ₁ hlt
    have hθ₂ : 0 ≤ θ₂ := by linarith
    exact hKL_nonneg (q θ₁) (q θ₂) (hfixed θ₁ hθ₁).1 (hfixed θ₂ hθ₂).1
  · intro θ₁ θ₂ hθ₁ hlt
    have hθ₂ : 0 ≤ θ₂ := by linarith
    exact hKL_nonneg (q θ₂) (q θ₁) (hfixed θ₂ hθ₂).1 (hfixed θ₁ hθ₁).1
  · intro θ₁ θ₂ hθ₁ hlt hne
    have hθ₂ : 0 ≤ θ₂ := by linarith
    exact hKL_pos_of_ne (q θ₂) (q θ₁)
      (hfixed θ₂ hθ₂).1 (hfixed θ₁ hθ₁).1 (Ne.symm hne)
  · intro θ₁ θ₂ hθ₁ hlt
    have hθ₂ : 0 ≤ θ₂ := by linarith
    have hlog₁ := lower_log_equation_of_fixed (hfixed θ₁ hθ₁)
    have hlog₂ := lower_log_equation_of_fixed (hfixed θ₂ hθ₂)
    have h12 := lower_KL_forward_identity_from_log
      (θ₁ := θ₁) (θ₂ := θ₂)
      (h₁ := Real.log (nlhfLowerZ θ₁ (q θ₁)))
      (h₂ := Real.log (nlhfLowerZ θ₂ (q θ₂)))
      (q₁ := q θ₁) (q₂ := q θ₂)
      (hfixed θ₁ hθ₁).1 (hfixed θ₂ hθ₂).1 hlog₁ hlog₂
    have h21 := lower_KL_reverse_identity_from_log
      (θ₁ := θ₁) (θ₂ := θ₂)
      (h₁ := Real.log (nlhfLowerZ θ₁ (q θ₁)))
      (h₂ := Real.log (nlhfLowerZ θ₂ (q θ₂)))
      (q₁ := q θ₁) (q₂ := q θ₂)
      (hfixed θ₁ hθ₁).1 (hfixed θ₂ hθ₂).1 hlog₁ hlog₂
    change KL (q θ₁) (q θ₂) + KL (q θ₂) (q θ₁) =
      (θ₂ - θ₁) * marginValue linearMargin3 (q θ₂) (q θ₁)
    rw [h12, h21]
    ring
  · intro θ₁ θ₂ hθ₁ hlt
    have hθ₂ : 0 ≤ θ₂ := by linarith
    exact lower_KL_reverse_identity_from_log
      (θ₁ := θ₁) (θ₂ := θ₂)
      (h₁ := Real.log (nlhfLowerZ θ₁ (q θ₁)))
      (h₂ := Real.log (nlhfLowerZ θ₂ (q θ₂)))
      (q₁ := q θ₁) (q₂ := q θ₂)
      (hfixed θ₁ hθ₁).1 (hfixed θ₂ hθ₂).1
      (lower_log_equation_of_fixed (hfixed θ₁ hθ₁))
      (lower_log_equation_of_fixed (hfixed θ₂ hθ₂))

/-- Fully finite-dimensional version of Lemma `Z-decreasing` for the
three-candidate lower profile used in the NLHF involvement proof. -/
theorem Z_strictly_decreasing_from_lower_fixed_selection_fin3
    {q : ℝ → Fin 3 → ℝ}
    (hfixed : ∀ θ : ℝ, 0 ≤ θ → IsNLHFLowerFixedPoint θ (q θ)) :
    StrictlyDecreasingOnNonneg (fun θ : ℝ => nlhfLowerZ θ (q θ)) :=
  Z_strictly_decreasing_from_lower_fixed_selection hfixed
    (fun _ _ hp hr => KL_nonneg_of_fullSupport_fin3 hp hr)
    (fun _ _ hp hr hne => KL_pos_of_fullSupport_ne_fin3 hp hr hne)

lemma probOdds_strictMono {p q : ℝ}
    (hp1 : p < 1) (hq1 : q < 1) (hpq : p < q) :
    p / (1 - p) < q / (1 - q) := by
  rw [div_lt_div_iff₀ (sub_pos.mpr hp1) (sub_pos.mpr hq1)]
  nlinarith

lemma nlhfG_strictMonoOn_Ioo
    {A lambda : ℝ} {Z : ℝ → ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda)
    (hZpos : PositiveOnNonneg Z)
    (hZdec : StrictlyDecreasingOnNonneg Z)
    {s : ℝ} (hs : 0 ≤ s) :
    StrictMonoOn
      (fun p : ℝ => p / (1 - p) - A / Z (lambda * s * (1 - p)))
      (Ioo (0 : ℝ) 1) := by
  intro p hp q hq hpq
  have hp0 : 0 < p := hp.1
  have hp1 : p < 1 := hp.2
  have hq1 : q < 1 := hq.2
  have hodds : p / (1 - p) < q / (1 - q) :=
    probOdds_strictMono hp1 hq1 hpq
  let tp : ℝ := lambda * s * (1 - p)
  let tq : ℝ := lambda * s * (1 - q)
  have htp_nonneg : 0 ≤ tp := by
    unfold tp
    exact mul_nonneg (mul_nonneg hlambda.le hs) (sub_nonneg.mpr hp1.le)
  have htq_nonneg : 0 ≤ tq := by
    unfold tq
    exact mul_nonneg (mul_nonneg hlambda.le hs) (sub_nonneg.mpr hq1.le)
  have htq_le_tp : tq ≤ tp := by
    unfold tq tp
    have hcoeff : 0 ≤ lambda * s := mul_nonneg hlambda.le hs
    nlinarith [mul_le_mul_of_nonneg_left
      (by linarith : 1 - q ≤ 1 - p) hcoeff]
  have hZle : Z tp ≤ Z tq := by
    by_cases heq : tq = tp
    · rw [heq]
    · have hlt : tq < tp := lt_of_le_of_ne htq_le_tp heq
      exact (hZdec tq tp htq_nonneg hlt).le
  have hterm :
      A / Z tq ≤ A / Z tp := by
    have hZtq : 0 < Z tq := hZpos tq htq_nonneg
    have hZtp : 0 < Z tp := hZpos tp htp_nonneg
    rw [div_le_div_iff₀ hZtq hZtp]
    nlinarith
  dsimp only
  nlinarith

/-- Lemma `p-comparison` from the paper: two scalar solutions are ordered
when their `s` parameters are ordered.  This is the version that avoids proving
existence of scalar zeros from continuity. -/
theorem nlhfP_comparison
    {A lambda : ℝ} {Z : ℝ → ℝ} {s₁ s₂ p₁ p₂ : ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda)
    (hZpos : PositiveOnNonneg Z)
    (hZdec : StrictlyDecreasingOnNonneg Z)
    (hs₁ : 0 ≤ s₁) (hslt : s₁ < s₂)
    (hsolve₁ : SolvesNLHFPEquation A lambda Z s₁ p₁)
    (hsolve₂ : SolvesNLHFPEquation A lambda Z s₂ p₂) :
    p₁ < p₂ := by
  have hs₂ : 0 ≤ s₂ := by linarith
  rcases hsolve₁ with ⟨hp₁0, hp₁1, hp₁eq⟩
  rcases hsolve₂ with ⟨hp₂0, hp₂1, hp₂eq⟩
  let G₂ : ℝ → ℝ :=
    fun p : ℝ => p / (1 - p) - A / Z (lambda * s₂ * (1 - p))
  have hp₁I : p₁ ∈ Ioo (0 : ℝ) 1 := ⟨hp₁0, hp₁1⟩
  have hp₂I : p₂ ∈ Ioo (0 : ℝ) 1 := ⟨hp₂0, hp₂1⟩
  have hGmono : StrictMonoOn G₂ (Ioo (0 : ℝ) 1) :=
    nlhfG_strictMonoOn_Ioo hA hlambda hZpos hZdec hs₂
  have hG₂_zero : G₂ p₂ = 0 := by
    dsimp [G₂]
    rw [hp₂eq]
    ring
  have hG₁_neg : G₂ p₁ < 0 := by
    let t₁ : ℝ := lambda * s₁ * (1 - p₁)
    let t₂ : ℝ := lambda * s₂ * (1 - p₁)
    have ht₁_nonneg : 0 ≤ t₁ := by
      unfold t₁
      exact mul_nonneg (mul_nonneg hlambda.le hs₁) (sub_nonneg.mpr hp₁1.le)
    have ht₂_nonneg : 0 ≤ t₂ := by
      unfold t₂
      exact mul_nonneg (mul_nonneg hlambda.le hs₂) (sub_nonneg.mpr hp₁1.le)
    have htlt : t₁ < t₂ := by
      unfold t₁ t₂
      nlinarith [mul_lt_mul_of_pos_left
        (mul_lt_mul_of_pos_right hslt (sub_pos.mpr hp₁1)) hlambda]
    have hZlt : Z t₂ < Z t₁ := hZdec t₁ t₂ ht₁_nonneg htlt
    have hZt₁ : 0 < Z t₁ := hZpos t₁ ht₁_nonneg
    have hZt₂ : 0 < Z t₂ := hZpos t₂ ht₂_nonneg
    have hdivlt : A / Z t₁ < A / Z t₂ := by
      rw [div_lt_div_iff₀ hZt₁ hZt₂]
      nlinarith
    unfold G₂
    have hp₁eq' : p₁ / (1 - p₁) = A / Z t₁ := by
      simpa [t₁, SolvesNLHFPEquation] using hp₁eq
    rw [hp₁eq']
    exact sub_neg.mpr hdivlt
  by_contra hnot
  have hp₂_le_p₁ : p₂ ≤ p₁ := le_of_not_gt hnot
  have hG_le : G₂ p₂ ≤ G₂ p₁ := by
    by_cases heq : p₂ = p₁
    · rw [heq]
    · have hlt : p₂ < p₁ := lt_of_le_of_ne hp₂_le_p₁ heq
      exact (hGmono hp₂I hp₁I hlt).le
  nlinarith

/-- Global corollary of `p-comparison`: if a scalar solution is available for
every `s ≥ 0`, the resulting `p_A(s)` function is strictly increasing. -/
theorem nlhfP_strictly_increasing
    {A lambda : ℝ} {Z : ℝ → ℝ} {pA : ℝ → ℝ}
    (hA : 0 < A) (hlambda : 0 < lambda)
    (hZpos : PositiveOnNonneg Z)
    (hZdec : StrictlyDecreasingOnNonneg Z)
    (hsolve : ∀ s : ℝ, 0 ≤ s → SolvesNLHFPEquation A lambda Z s (pA s)) :
    ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ < s₂ → pA s₁ < pA s₂ := by
  intro s₁ s₂ hs₁ hslt
  have hs₂ : 0 ≤ s₂ := by linarith
  exact nlhfP_comparison hA hlambda hZpos hZdec hs₁ hslt
    (hsolve s₁ hs₁) (hsolve s₂ hs₂)

/-- Candidate order for the NLHF involvement construction:
`0 = a`, `1 = b`, `2 = c`, `3 = d`. -/
noncomputable def uniform4 : Fin 4 → ℝ :=
  fun _ => (1 : ℝ) / 4

lemma uniform4_fullSupport : IsFullSupportLottery uniform4 := by
  constructor
  · intro x
    simp [uniform4]
  · simp [uniform4]

/-- Positive-involvement margin family from the appendix.  Candidate `a` beats
all other candidates by margin `1`; among `{c,b,d}`, the order is `c > b > d`
with strength `s`. -/
noncomputable def nlhfPositiveInvolvementMargin (s : ℝ) :
    Fin 4 → Fin 4 → ℝ
  | 0, 1 => 1
  | 0, 2 => 1
  | 0, 3 => 1
  | 1, 0 => -1
  | 2, 0 => -1
  | 3, 0 => -1
  | 2, 1 => s
  | 1, 2 => -s
  | 2, 3 => s
  | 3, 2 => -s
  | 1, 3 => s
  | 3, 1 => -s
  | _, _ => 0

/-- Negative-involvement margin family from the appendix.  Candidate `a` loses
to all other candidates by margin `1`; among `{b,c,d}`, the order is `b > c >
d` with strength `s`. -/
noncomputable def nlhfNegativeInvolvementMargin (s : ℝ) :
    Fin 4 → Fin 4 → ℝ
  | 0, 1 => -1
  | 1, 0 => 1
  | 0, 2 => -1
  | 2, 0 => 1
  | 0, 3 => -1
  | 3, 0 => 1
  | 1, 2 => s
  | 2, 1 => -s
  | 1, 3 => s
  | 3, 1 => -s
  | 2, 3 => s
  | 3, 2 => -s
  | _, _ => 0

def prefByRank (rank : Fin 4 → Nat) (x y : Fin 4) : Bool :=
  decide (rank x < rank y)

/-- Ranking `a c b d`. -/
def rankACBD : Fin 4 → Nat
  | 0 => 0
  | 2 => 1
  | 1 => 2
  | 3 => 3

/-- Ranking `a d b c`. -/
def rankADBC : Fin 4 → Nat
  | 0 => 0
  | 3 => 1
  | 1 => 2
  | 2 => 3

/-- Ranking `b c d a`. -/
def rankBCDA : Fin 4 → Nat
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 0 => 3

/-- Ranking `d c b a`. -/
def rankDCBA : Fin 4 → Nat
  | 3 => 0
  | 2 => 1
  | 1 => 2
  | 0 => 3

def prefACBD : Fin 4 → Fin 4 → Bool := prefByRank rankACBD
def prefADBC : Fin 4 → Fin 4 → Bool := prefByRank rankADBC
def prefBCDA : Fin 4 → Fin 4 → Bool := prefByRank rankBCDA
def prefDCBA : Fin 4 → Fin 4 → Bool := prefByRank rankDCBA

def nlhfPositiveProfileR : Fin 2 → Fin 4 → Fin 4 → Bool :=
  fun _ => prefACBD

def nlhfPositiveProfileRPlus : Fin 3 → Fin 4 → Fin 4 → Bool :=
  fun i => if i = 2 then prefADBC else prefACBD

def nlhfNegativeProfileS : Fin 2 → Fin 4 → Fin 4 → Bool :=
  fun i => if i = 0 then prefBCDA else prefDCBA

def nlhfNegativeProfileSPlus : Fin 3 → Fin 4 → Fin 4 → Bool :=
  fun i => if i = 1 then prefDCBA else prefBCDA

def nlhfPositiveLowerIndex : Fin 3 → Fin 4
  | 0 => 2
  | 1 => 1
  | 2 => 3

def nlhfNegativeLowerIndex : Fin 3 → Fin 4
  | 0 => 1
  | 1 => 2
  | 2 => 3

noncomputable def conditionedNonA
    (idx : Fin 3 → Fin 4) (π : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun u => π (idx u) / (1 - π 0)

lemma one_sub_pi0_pos_of_fullSupport4 {π : Fin 4 → ℝ}
    (hπ : IsFullSupportLottery π) :
    0 < 1 - π 0 := by
  have hsum : π 0 + π 1 + π 2 + π 3 = 1 := by
    simpa [Fin.sum_univ_four] using hπ.2
  have h1 : 0 < π 1 := hπ.1 1
  have h2 : 0 < π 2 := hπ.1 2
  have h3 : 0 < π 3 := hπ.1 3
  linarith

lemma conditionedNonA_positive_fullSupport
    {π : Fin 4 → ℝ} (hπ : IsFullSupportLottery π) :
    IsFullSupportLottery (conditionedNonA nlhfPositiveLowerIndex π) := by
  have hdenpos : 0 < 1 - π 0 := one_sub_pi0_pos_of_fullSupport4 hπ
  have hsum : π 0 + π 1 + π 2 + π 3 = 1 := by
    simpa [Fin.sum_univ_four] using hπ.2
  constructor
  · intro u
    fin_cases u <;>
      simp [conditionedNonA, nlhfPositiveLowerIndex,
        div_pos (hπ.1 _) hdenpos]
  · simp [conditionedNonA, nlhfPositiveLowerIndex, Fin.sum_univ_three]
    field_simp [hdenpos.ne']
    linarith

lemma conditionedNonA_negative_fullSupport
    {π : Fin 4 → ℝ} (hπ : IsFullSupportLottery π) :
    IsFullSupportLottery (conditionedNonA nlhfNegativeLowerIndex π) := by
  have hdenpos : 0 < 1 - π 0 := one_sub_pi0_pos_of_fullSupport4 hπ
  have hsum : π 0 + π 1 + π 2 + π 3 = 1 := by
    simpa [Fin.sum_univ_four] using hπ.2
  constructor
  · intro u
    fin_cases u <;>
      simp [conditionedNonA, nlhfNegativeLowerIndex,
        div_pos (hπ.1 _) hdenpos]
  · simp [conditionedNonA, nlhfNegativeLowerIndex, Fin.sum_univ_three]
    field_simp [hdenpos.ne']
    linarith

lemma nlhfPositive_expected_a
    (s : ℝ) {π : Fin 4 → ℝ} (hπsum : Finset.sum Finset.univ π = 1) :
    expectedMargin (nlhfPositiveInvolvementMargin s) π 0 = 1 - π 0 := by
  have hsum : π 0 + π 1 + π 2 + π 3 = 1 := by
    simpa [Fin.sum_univ_four] using hπsum
  simp [expectedMargin, nlhfPositiveInvolvementMargin, Fin.sum_univ_four]
  linarith

lemma nlhfNegative_expected_a
    (s : ℝ) {π : Fin 4 → ℝ} (hπsum : Finset.sum Finset.univ π = 1) :
    expectedMargin (nlhfNegativeInvolvementMargin s) π 0 = -(1 - π 0) := by
  have hsum : π 0 + π 1 + π 2 + π 3 = 1 := by
    simpa [Fin.sum_univ_four] using hπsum
  simp [expectedMargin, nlhfNegativeInvolvementMargin, Fin.sum_univ_four]
  linarith

lemma nlhfPositive_expected_lower
    (s : ℝ) {π : Fin 4 → ℝ} (hden : 1 - π 0 ≠ 0) :
    ∀ u : Fin 3,
      expectedMargin (nlhfPositiveInvolvementMargin s) π
          (nlhfPositiveLowerIndex u) =
        -π 0 + s * (1 - π 0) *
          expectedMargin linearMargin3
            (conditionedNonA nlhfPositiveLowerIndex π) u := by
  intro u
  fin_cases u <;>
    simp [expectedMargin, nlhfPositiveInvolvementMargin,
      nlhfPositiveLowerIndex, conditionedNonA, linearMargin3,
      Fin.sum_univ_three, Fin.sum_univ_four] <;>
      field_simp [hden] <;>
      ring

lemma nlhfNegative_expected_lower
    (s : ℝ) {π : Fin 4 → ℝ} (hden : 1 - π 0 ≠ 0) :
    ∀ u : Fin 3,
      expectedMargin (nlhfNegativeInvolvementMargin s) π
          (nlhfNegativeLowerIndex u) =
        π 0 + s * (1 - π 0) *
          expectedMargin linearMargin3
            (conditionedNonA nlhfNegativeLowerIndex π) u := by
  intro u
  fin_cases u <;>
    simp [expectedMargin, nlhfNegativeInvolvementMargin,
      nlhfNegativeLowerIndex, conditionedNonA, linearMargin3,
      Fin.sum_univ_three, Fin.sum_univ_four] <;>
      field_simp [hden] <;>
      ring

noncomputable def nlhfUniform4Denom
    (τ : ℝ) (M : Fin 4 → Fin 4 → ℝ) (π : Fin 4 → ℝ) : ℝ :=
  Finset.sum Finset.univ
    (fun z => uniform4 z * Real.exp (expectedMargin M π z / (2 * τ)))

lemma nlhfUniform4Denom_pos
    (τ : ℝ) (M : Fin 4 → Fin 4 → ℝ) (π : Fin 4 → ℝ) :
    0 < nlhfUniform4Denom τ M π := by
  unfold nlhfUniform4Denom
  exact Finset.sum_pos
    (fun z _hz => mul_pos (by simp [uniform4]) (Real.exp_pos _))
    Finset.univ_nonempty

lemma nlhf_fixed_uniform4_eq_exp_over_denom
    {τ : ℝ} {M : Fin 4 → Fin 4 → ℝ} {π : Fin 4 → ℝ}
    (hfp : IsNLHFFixedPoint τ M uniform4 π) :
    ∀ x : Fin 4,
      π x =
        (1 / 4 : ℝ) * Real.exp (expectedMargin M π x / (2 * τ)) /
          nlhfUniform4Denom τ M π := by
  intro x
  have hx := hfp.2.2.2 x
  simpa [uniform4, nlhfUniform4Denom] using hx

lemma nlhf_fixed_uniform4_ratio
    {τ : ℝ} {M : Fin 4 → Fin 4 → ℝ} {π : Fin 4 → ℝ}
    (hτ : 0 < τ)
    (hfp : IsNLHFFixedPoint τ M uniform4 π) :
    ∀ x y : Fin 4,
      π x / π y =
        Real.exp ((expectedMargin M π x - expectedMargin M π y) / (2 * τ)) := by
  intro x y
  have hDpos : 0 < nlhfUniform4Denom τ M π :=
    nlhfUniform4Denom_pos τ M π
  have hx := nlhf_fixed_uniform4_eq_exp_over_denom hfp x
  have hy := nlhf_fixed_uniform4_eq_exp_over_denom hfp y
  have hτne : 2 * τ ≠ 0 := by nlinarith
  have harg :
      (expectedMargin M π x - expectedMargin M π y) / (2 * τ) =
        expectedMargin M π x / (2 * τ) - expectedMargin M π y / (2 * τ) := by
    field_simp [hτne]
  rw [hx, hy]
  rw [harg, Real.exp_sub]
  field_simp [hDpos.ne', Real.exp_ne_zero, show (4 : ℝ) ≠ 0 by norm_num]

lemma nlhf_positive_lower_prob_eq
    {τ s : ℝ} {π : Fin 4 → ℝ}
    (hτ : 0 < τ)
    (hfp : IsNLHFFixedPoint τ (nlhfPositiveInvolvementMargin s) uniform4 π) :
    ∀ u : Fin 3,
      π (nlhfPositiveLowerIndex u) =
        π 0 * Real.exp (-(1 / (2 * τ))) *
          Real.exp
            ((s * (1 - π 0) / (2 * τ)) *
              expectedMargin linearMargin3
                (conditionedNonA nlhfPositiveLowerIndex π) u) := by
  intro u
  have hden : 1 - π 0 ≠ 0 :=
    (one_sub_pi0_pos_of_fullSupport4 hfp.2.2.1).ne'
  have hratio := nlhf_fixed_uniform4_ratio hτ hfp (nlhfPositiveLowerIndex u) 0
  have hlow := nlhfPositive_expected_lower s hden u
  have ha := nlhfPositive_expected_a s hfp.2.2.1.2
  have hτne : 2 * τ ≠ 0 := by nlinarith
  have harg :
      (expectedMargin (nlhfPositiveInvolvementMargin s) π
            (nlhfPositiveLowerIndex u) -
          expectedMargin (nlhfPositiveInvolvementMargin s) π 0) / (2 * τ) =
        -(1 / (2 * τ)) +
          (s * (1 - π 0) / (2 * τ)) *
            expectedMargin linearMargin3
              (conditionedNonA nlhfPositiveLowerIndex π) u := by
    rw [hlow, ha]
    field_simp [hτne]
    ring
  have hπ0pos : 0 < π 0 := hfp.2.2.1.1 0
  rw [harg] at hratio
  rw [Real.exp_add] at hratio
  calc
    π (nlhfPositiveLowerIndex u) =
        π 0 * (π (nlhfPositiveLowerIndex u) / π 0) := by
          field_simp [hπ0pos.ne']
    _ = π 0 * (Real.exp (-(1 / (2 * τ))) *
          Real.exp
            ((s * (1 - π 0) / (2 * τ)) *
              expectedMargin linearMargin3
                (conditionedNonA nlhfPositiveLowerIndex π) u)) := by
          rw [hratio]
    _ = π 0 * Real.exp (-(1 / (2 * τ))) *
          Real.exp
            ((s * (1 - π 0) / (2 * τ)) *
              expectedMargin linearMargin3
                (conditionedNonA nlhfPositiveLowerIndex π) u) := by
          ring

theorem nlhf_positive_scalar_equation_from_fixed
    {τ s : ℝ} {π : Fin 4 → ℝ}
    (hτ : 0 < τ)
    (hfp : IsNLHFFixedPoint τ (nlhfPositiveInvolvementMargin s) uniform4 π) :
    SolvesNLHFPEquation (Real.exp (1 / (2 * τ))) (1 / (2 * τ))
      (fun θ => nlhfLowerZ θ (conditionedNonA nlhfPositiveLowerIndex π))
      s (π 0) := by
  have hπfull : IsFullSupportLottery π := hfp.2.2.1
  have hp0 : 0 < π 0 := hπfull.1 0
  have hp1 : π 0 < 1 := by
    have hdenpos := one_sub_pi0_pos_of_fullSupport4 hπfull
    linarith
  refine ⟨hp0, hp1, ?_⟩
  have hlower := nlhf_positive_lower_prob_eq hτ hfp
  have hsum : π 0 + π 1 + π 2 + π 3 = 1 := by
    simpa [Fin.sum_univ_four] using hπfull.2
  have hnonA :
      1 - π 0 = π 2 + π 1 + π 3 := by linarith
  have htheta :
      s * (1 - π 0) / (2 * τ) =
        s * (1 - π 0) / (2 * τ) := rfl
  have hsum_lower :
      π 2 + π 1 + π 3 =
        π 0 * Real.exp (-(1 / (2 * τ))) *
          nlhfLowerZ (s * (1 - π 0) / (2 * τ))
            (conditionedNonA nlhfPositiveLowerIndex π) := by
    have h0 := hlower 0
    have h1 := hlower 1
    have h2 := hlower 2
    simp [nlhfPositiveLowerIndex, nlhfLowerZ, Fin.sum_univ_three] at h0 h1 h2 ⊢
    rw [h0, h1, h2]
    ring
  have hden_eq :
      1 - π 0 =
        π 0 * Real.exp (-(1 / (2 * τ))) *
          nlhfLowerZ (s * (1 - π 0) / (2 * τ))
            (conditionedNonA nlhfPositiveLowerIndex π) := by
    calc
      1 - π 0 = π 2 + π 1 + π 3 := hnonA
      _ = π 0 * Real.exp (-(1 / (2 * τ))) *
          nlhfLowerZ (s * (1 - π 0) / (2 * τ))
            (conditionedNonA nlhfPositiveLowerIndex π) := hsum_lower
  have hπ0ne : π 0 ≠ 0 := hp0.ne'
  have hexpneg : Real.exp (-(1 / (2 * τ))) ≠ 0 := Real.exp_ne_zero _
  have hZne :
      nlhfLowerZ (s * (1 - π 0) / (2 * τ))
          (conditionedNonA nlhfPositiveLowerIndex π) ≠ 0 :=
    (nlhfLowerZ_pos (s * (1 - π 0) / (2 * τ))
      (conditionedNonA nlhfPositiveLowerIndex π)).ne'
  have htheta_eq :
      (1 / (2 * τ)) * s * (1 - π 0) =
        s * (1 - π 0) / (2 * τ) := by
    have hτne : 2 * τ ≠ 0 := by nlinarith
    field_simp [hτne]
  calc
    π 0 / (1 - π 0) =
        π 0 /
          (π 0 * Real.exp (-(1 / (2 * τ))) *
            nlhfLowerZ (s * (1 - π 0) / (2 * τ))
              (conditionedNonA nlhfPositiveLowerIndex π)) := by
          conv_lhs => rw [hden_eq]
    _ = Real.exp (1 / (2 * τ)) /
          nlhfLowerZ (s * (1 - π 0) / (2 * τ))
            (conditionedNonA nlhfPositiveLowerIndex π) := by
          field_simp [hπ0ne, hexpneg, hZne]
          rw [← Real.exp_add]
          have hτne : 2 * τ ≠ 0 := by nlinarith
          field_simp [hτne]
          simp
    _ = Real.exp (1 / (2 * τ)) /
          nlhfLowerZ ((1 / (2 * τ)) * s * (1 - π 0))
            (conditionedNonA nlhfPositiveLowerIndex π) := by
          rw [htheta_eq]

lemma nlhf_negative_lower_prob_eq
    {τ s : ℝ} {π : Fin 4 → ℝ}
    (hτ : 0 < τ)
    (hfp : IsNLHFFixedPoint τ (nlhfNegativeInvolvementMargin s) uniform4 π) :
    ∀ u : Fin 3,
      π (nlhfNegativeLowerIndex u) =
        π 0 * Real.exp (1 / (2 * τ)) *
          Real.exp
            ((s * (1 - π 0) / (2 * τ)) *
              expectedMargin linearMargin3
                (conditionedNonA nlhfNegativeLowerIndex π) u) := by
  intro u
  have hden : 1 - π 0 ≠ 0 :=
    (one_sub_pi0_pos_of_fullSupport4 hfp.2.2.1).ne'
  have hratio := nlhf_fixed_uniform4_ratio hτ hfp (nlhfNegativeLowerIndex u) 0
  have hlow := nlhfNegative_expected_lower s hden u
  have ha := nlhfNegative_expected_a s hfp.2.2.1.2
  have hτne : 2 * τ ≠ 0 := by nlinarith
  have harg :
      (expectedMargin (nlhfNegativeInvolvementMargin s) π
            (nlhfNegativeLowerIndex u) -
          expectedMargin (nlhfNegativeInvolvementMargin s) π 0) / (2 * τ) =
        1 / (2 * τ) +
          (s * (1 - π 0) / (2 * τ)) *
            expectedMargin linearMargin3
              (conditionedNonA nlhfNegativeLowerIndex π) u := by
    rw [hlow, ha]
    field_simp [hτne]
    ring
  have hπ0pos : 0 < π 0 := hfp.2.2.1.1 0
  rw [harg] at hratio
  rw [Real.exp_add] at hratio
  calc
    π (nlhfNegativeLowerIndex u) =
        π 0 * (π (nlhfNegativeLowerIndex u) / π 0) := by
          field_simp [hπ0pos.ne']
    _ = π 0 * (Real.exp (1 / (2 * τ)) *
          Real.exp
            ((s * (1 - π 0) / (2 * τ)) *
              expectedMargin linearMargin3
                (conditionedNonA nlhfNegativeLowerIndex π) u)) := by
          rw [hratio]
    _ = π 0 * Real.exp (1 / (2 * τ)) *
          Real.exp
            ((s * (1 - π 0) / (2 * τ)) *
              expectedMargin linearMargin3
                (conditionedNonA nlhfNegativeLowerIndex π) u) := by
          ring

theorem nlhf_negative_scalar_equation_from_fixed
    {τ s : ℝ} {π : Fin 4 → ℝ}
    (hτ : 0 < τ)
    (hfp : IsNLHFFixedPoint τ (nlhfNegativeInvolvementMargin s) uniform4 π) :
    SolvesNLHFPEquation (Real.exp (-(1 / (2 * τ)))) (1 / (2 * τ))
      (fun θ => nlhfLowerZ θ (conditionedNonA nlhfNegativeLowerIndex π))
      s (π 0) := by
  have hπfull : IsFullSupportLottery π := hfp.2.2.1
  have hp0 : 0 < π 0 := hπfull.1 0
  have hp1 : π 0 < 1 := by
    have hdenpos := one_sub_pi0_pos_of_fullSupport4 hπfull
    linarith
  refine ⟨hp0, hp1, ?_⟩
  have hlower := nlhf_negative_lower_prob_eq hτ hfp
  have hsum : π 0 + π 1 + π 2 + π 3 = 1 := by
    simpa [Fin.sum_univ_four] using hπfull.2
  have hnonA :
      1 - π 0 = π 1 + π 2 + π 3 := by linarith
  have hsum_lower :
      π 1 + π 2 + π 3 =
        π 0 * Real.exp (1 / (2 * τ)) *
          nlhfLowerZ (s * (1 - π 0) / (2 * τ))
            (conditionedNonA nlhfNegativeLowerIndex π) := by
    have h0 := hlower 0
    have h1 := hlower 1
    have h2 := hlower 2
    simp [nlhfNegativeLowerIndex, nlhfLowerZ, Fin.sum_univ_three] at h0 h1 h2 ⊢
    rw [h0, h1, h2]
    ring
  have hden_eq :
      1 - π 0 =
        π 0 * Real.exp (1 / (2 * τ)) *
          nlhfLowerZ (s * (1 - π 0) / (2 * τ))
            (conditionedNonA nlhfNegativeLowerIndex π) := by
    calc
      1 - π 0 = π 1 + π 2 + π 3 := hnonA
      _ = π 0 * Real.exp (1 / (2 * τ)) *
          nlhfLowerZ (s * (1 - π 0) / (2 * τ))
            (conditionedNonA nlhfNegativeLowerIndex π) := hsum_lower
  have hπ0ne : π 0 ≠ 0 := hp0.ne'
  have hexp_pos : Real.exp (1 / (2 * τ)) ≠ 0 := Real.exp_ne_zero _
  have hZne :
      nlhfLowerZ (s * (1 - π 0) / (2 * τ))
          (conditionedNonA nlhfNegativeLowerIndex π) ≠ 0 :=
    (nlhfLowerZ_pos (s * (1 - π 0) / (2 * τ))
      (conditionedNonA nlhfNegativeLowerIndex π)).ne'
  have htheta_eq :
      (1 / (2 * τ)) * s * (1 - π 0) =
        s * (1 - π 0) / (2 * τ) := by
    have hτne : 2 * τ ≠ 0 := by nlinarith
    field_simp [hτne]
  calc
    π 0 / (1 - π 0) =
        π 0 /
          (π 0 * Real.exp (1 / (2 * τ)) *
            nlhfLowerZ (s * (1 - π 0) / (2 * τ))
              (conditionedNonA nlhfNegativeLowerIndex π)) := by
          conv_lhs => rw [hden_eq]
    _ = Real.exp (-(1 / (2 * τ))) /
          nlhfLowerZ (s * (1 - π 0) / (2 * τ))
            (conditionedNonA nlhfNegativeLowerIndex π) := by
          field_simp [hπ0ne, hexp_pos, hZne]
          rw [← Real.exp_add]
          have hτne : 2 * τ ≠ 0 := by nlinarith
          field_simp [hτne]
          simp
    _ = Real.exp (-(1 / (2 * τ))) /
          nlhfLowerZ ((1 / (2 * τ)) * s * (1 - π 0))
            (conditionedNonA nlhfNegativeLowerIndex π) := by
          rw [htheta_eq]

theorem nlhf_positive_conditioned_lower_fixed
    {τ s : ℝ} {π : Fin 4 → ℝ}
    (hτ : 0 < τ)
    (hfp : IsNLHFFixedPoint τ (nlhfPositiveInvolvementMargin s) uniform4 π) :
    IsNLHFLowerFixedPoint ((1 / (2 * τ)) * s * (1 - π 0))
      (conditionedNonA nlhfPositiveLowerIndex π) := by
  constructor
  · exact conditionedNonA_positive_fullSupport hfp.2.2.1
  · intro u
    have hlower := nlhf_positive_lower_prob_eq hτ hfp
    rcases nlhf_positive_scalar_equation_from_fixed hτ hfp with
      ⟨_hp0, _hp1, heq⟩
    let θ : ℝ := (1 / (2 * τ)) * s * (1 - π 0)
    let E : ℝ :=
      expectedMargin linearMargin3
        (conditionedNonA nlhfPositiveLowerIndex π) u
    have hπidx :
        π (nlhfPositiveLowerIndex u) =
          π 0 * Real.exp (-(1 / (2 * τ))) *
            Real.exp (θ * E) := by
      have htheta_eq :
          θ = s * (1 - π 0) / (2 * τ) := by
        dsimp [θ]
        have hτne : 2 * τ ≠ 0 := by nlinarith
        field_simp [hτne]
      simpa [E, htheta_eq] using hlower u
    have hZne :
        nlhfLowerZ θ (conditionedNonA nlhfPositiveLowerIndex π) ≠ 0 :=
      (nlhfLowerZ_pos θ (conditionedNonA nlhfPositiveLowerIndex π)).ne'
    calc
      conditionedNonA nlhfPositiveLowerIndex π u =
          π (nlhfPositiveLowerIndex u) / (1 - π 0) := rfl
      _ = (π 0 / (1 - π 0)) * Real.exp (-(1 / (2 * τ))) *
            Real.exp (θ * E) := by
          rw [hπidx]
          ring
      _ = (Real.exp (1 / (2 * τ)) /
              nlhfLowerZ θ (conditionedNonA nlhfPositiveLowerIndex π)) *
            Real.exp (-(1 / (2 * τ))) * Real.exp (θ * E) := by
          rw [heq]
      _ = Real.exp (θ * E) /
            nlhfLowerZ θ (conditionedNonA nlhfPositiveLowerIndex π) := by
          field_simp [hZne, Real.exp_ne_zero]
          rw [← Real.exp_add]
          have hτne : 2 * τ ≠ 0 := by nlinarith
          field_simp [hτne]
          simp

theorem nlhf_negative_conditioned_lower_fixed
    {τ s : ℝ} {π : Fin 4 → ℝ}
    (hτ : 0 < τ)
    (hfp : IsNLHFFixedPoint τ (nlhfNegativeInvolvementMargin s) uniform4 π) :
    IsNLHFLowerFixedPoint ((1 / (2 * τ)) * s * (1 - π 0))
      (conditionedNonA nlhfNegativeLowerIndex π) := by
  constructor
  · exact conditionedNonA_negative_fullSupport hfp.2.2.1
  · intro u
    have hlower := nlhf_negative_lower_prob_eq hτ hfp
    rcases nlhf_negative_scalar_equation_from_fixed hτ hfp with
      ⟨_hp0, _hp1, heq⟩
    let θ : ℝ := (1 / (2 * τ)) * s * (1 - π 0)
    let E : ℝ :=
      expectedMargin linearMargin3
        (conditionedNonA nlhfNegativeLowerIndex π) u
    have hπidx :
        π (nlhfNegativeLowerIndex u) =
          π 0 * Real.exp (1 / (2 * τ)) *
            Real.exp (θ * E) := by
      have htheta_eq :
          θ = s * (1 - π 0) / (2 * τ) := by
        dsimp [θ]
        have hτne : 2 * τ ≠ 0 := by nlinarith
        field_simp [hτne]
      simpa [E, htheta_eq] using hlower u
    have hZne :
        nlhfLowerZ θ (conditionedNonA nlhfNegativeLowerIndex π) ≠ 0 :=
      (nlhfLowerZ_pos θ (conditionedNonA nlhfNegativeLowerIndex π)).ne'
    calc
      conditionedNonA nlhfNegativeLowerIndex π u =
          π (nlhfNegativeLowerIndex u) / (1 - π 0) := rfl
      _ = (π 0 / (1 - π 0)) * Real.exp (1 / (2 * τ)) *
            Real.exp (θ * E) := by
          rw [hπidx]
          ring
      _ = (Real.exp (-(1 / (2 * τ))) /
              nlhfLowerZ θ (conditionedNonA nlhfNegativeLowerIndex π)) *
            Real.exp (1 / (2 * τ)) * Real.exp (θ * E) := by
          rw [heq]
      _ = Real.exp (θ * E) /
            nlhfLowerZ θ (conditionedNonA nlhfNegativeLowerIndex π) := by
          field_simp [hZne, Real.exp_ne_zero]
          rw [← Real.exp_add]
          have hτne : 2 * τ ≠ 0 := by nlinarith
          field_simp [hτne]
          simp

def strictCount2 (R : Fin 2 → Fin 4 → Fin 4 → Bool)
    (x y : Fin 4) : ℝ :=
  prefIndicator (R 0 x y) + prefIndicator (R 1 x y)

def strictCount3 (R : Fin 3 → Fin 4 → Fin 4 → Bool)
    (x y : Fin 4) : ℝ :=
  prefIndicator (R 0 x y) + prefIndicator (R 1 x y) +
    prefIndicator (R 2 x y)

noncomputable def normalizedStrictMargin2
    (R : Fin 2 → Fin 4 → Fin 4 → Bool) : Fin 4 → Fin 4 → ℝ :=
  fun x y => (strictCount2 R x y - strictCount2 R y x) / 2

noncomputable def normalizedStrictMargin3
    (R : Fin 3 → Fin 4 → Fin 4 → Bool) : Fin 4 → Fin 4 → ℝ :=
  fun x y => (strictCount3 R x y - strictCount3 R y x) / 3

lemma nlhfPositiveProfileR_margin_eq :
    normalizedStrictMargin2 nlhfPositiveProfileR =
      nlhfPositiveInvolvementMargin 1 := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [normalizedStrictMargin2, strictCount2, nlhfPositiveProfileR,
      prefACBD, prefByRank, rankACBD, prefIndicator,
      nlhfPositiveInvolvementMargin]

lemma nlhfPositiveProfileRPlus_margin_eq :
    normalizedStrictMargin3 nlhfPositiveProfileRPlus =
      nlhfPositiveInvolvementMargin ((1 : ℝ) / 3) := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [normalizedStrictMargin3, strictCount3, nlhfPositiveProfileRPlus,
      prefACBD, prefADBC, prefByRank, rankACBD, rankADBC, prefIndicator,
      nlhfPositiveInvolvementMargin] <;>
      norm_num

lemma nlhfNegativeProfileS_margin_eq :
    normalizedStrictMargin2 nlhfNegativeProfileS =
      nlhfNegativeInvolvementMargin 0 := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [normalizedStrictMargin2, strictCount2, nlhfNegativeProfileS,
      prefBCDA, prefDCBA, prefByRank, rankBCDA, rankDCBA, prefIndicator,
      nlhfNegativeInvolvementMargin]

lemma nlhfNegativeProfileSPlus_margin_eq :
    normalizedStrictMargin3 nlhfNegativeProfileSPlus =
      nlhfNegativeInvolvementMargin ((1 : ℝ) / 3) := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [normalizedStrictMargin3, strictCount3, nlhfNegativeProfileSPlus,
      prefBCDA, prefDCBA, prefByRank, rankBCDA, rankDCBA, prefIndicator,
      nlhfNegativeInvolvementMargin] <;>
      norm_num

lemma nlhfPositiveInvolvementMargin_normalized {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsNormalizedMarginMatrix (nlhfPositiveInvolvementMargin s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [nlhfPositiveInvolvementMargin]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [nlhfPositiveInvolvementMargin]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [nlhfPositiveInvolvementMargin, abs_of_nonneg hs0,
        abs_of_nonpos (neg_nonpos.mpr hs0)] <;> linarith

lemma nlhfNegativeInvolvementMargin_normalized {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsNormalizedMarginMatrix (nlhfNegativeInvolvementMargin s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [nlhfNegativeInvolvementMargin]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [nlhfNegativeInvolvementMargin]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [nlhfNegativeInvolvementMargin, abs_of_nonneg hs0,
        abs_of_nonpos (neg_nonpos.mpr hs0)] <;> linarith

/-! ## Profile-level facts for the involvement witnesses

The four `*_margin_eq` lemmas above realize the witness margin families by
actual profiles.  Here we add the linearity certificates, `RanksTop` /
`RanksBottom` facts for the added voters, and the identification of the
`Fin 3` profiles with `addVoterProfile` of the `Fin 2` profiles, so the
paper-facing involvement statements quantify over genuine profile-level
witnesses. -/

lemma isLinearPref_prefByRank {rank : Fin 4 → ℕ}
    (hinj : Function.Injective rank) :
    IsLinearPref (prefByRank rank) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp only [prefByRank, decide_eq_false_iff_not]
    omega
  · intro x y h
    simp only [prefByRank, decide_eq_true_eq] at h
    simp only [prefByRank, decide_eq_false_iff_not]
    omega
  · intro x y hxy
    have hne : rank x ≠ rank y := fun h => hxy (hinj h)
    simp only [prefByRank, decide_eq_true_eq]
    omega
  · intro x y z hxy hyz
    simp only [prefByRank, decide_eq_true_eq] at hxy hyz ⊢
    omega

lemma rankACBD_injective : Function.Injective rankACBD := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rankACBD]

lemma rankADBC_injective : Function.Injective rankADBC := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rankADBC]

lemma rankBCDA_injective : Function.Injective rankBCDA := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rankBCDA]

lemma rankDCBA_injective : Function.Injective rankDCBA := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rankDCBA]

lemma prefACBD_linear : IsLinearPref prefACBD :=
  isLinearPref_prefByRank rankACBD_injective
lemma prefADBC_linear : IsLinearPref prefADBC :=
  isLinearPref_prefByRank rankADBC_injective
lemma prefBCDA_linear : IsLinearPref prefBCDA :=
  isLinearPref_prefByRank rankBCDA_injective
lemma prefDCBA_linear : IsLinearPref prefDCBA :=
  isLinearPref_prefByRank rankDCBA_injective

lemma nlhfPositiveProfileR_linear :
    ∀ i, IsLinearPref (nlhfPositiveProfileR i) := fun _ => prefACBD_linear

lemma nlhfNegativeProfileS_linear :
    ∀ i, IsLinearPref (nlhfNegativeProfileS i) := by
  intro i
  by_cases h : i = 0 <;>
    simp [nlhfNegativeProfileS, h, prefBCDA_linear, prefDCBA_linear]

/-- The added positive-involvement voter `adbc` ranks `a` first. -/
lemma prefADBC_ranksTop_zero : RanksTop prefADBC 0 := by
  intro y hy
  fin_cases y
  · exact absurd rfl hy
  · decide
  · decide
  · decide

/-- The added negative-involvement voter `bcda` ranks `a` last. -/
lemma prefBCDA_ranksBottom_zero : RanksBottom prefBCDA 0 := by
  intro y hy
  fin_cases y
  · exact absurd rfl hy
  · decide
  · decide
  · decide

lemma strictCount_fin2_eq (R : Fin 2 → Fin 4 → Fin 4 → Bool) (x y : Fin 4) :
    strictCount R x y = strictCount2 R x y := by
  simp [strictCount, strictCount2, Fin.sum_univ_two]

lemma normalizedStrictMargin_fin2_eq (R : Fin 2 → Fin 4 → Fin 4 → Bool) :
    normalizedStrictMargin R = normalizedStrictMargin2 R := by
  funext x y
  simp [normalizedStrictMargin, strictMargin, normalizedStrictMargin2,
    strictCount_fin2_eq, Fintype.card_fin]

lemma strictCount3_positiveRPlus_eq_addVoter (x y : Fin 4) :
    strictCount3 nlhfPositiveProfileRPlus x y =
      strictCount2 nlhfPositiveProfileR x y + prefIndicator (prefADBC x y) := by
  simp [strictCount3, strictCount2, nlhfPositiveProfileRPlus,
    nlhfPositiveProfileR, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide]

lemma strictCount3_negativeSPlus_eq_addVoter (x y : Fin 4) :
    strictCount3 nlhfNegativeProfileSPlus x y =
      strictCount2 nlhfNegativeProfileS x y + prefIndicator (prefBCDA x y) := by
  simp [strictCount3, strictCount2, nlhfNegativeProfileSPlus,
    nlhfNegativeProfileS, show (0 : Fin 3) ≠ 1 by decide,
    show (2 : Fin 3) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide]

/-- Profile realization of the positive witness `s = 1`. -/
lemma nlhfPositiveProfileR_normalizedStrictMargin_eq :
    normalizedStrictMargin nlhfPositiveProfileR =
      nlhfPositiveInvolvementMargin 1 :=
  (normalizedStrictMargin_fin2_eq _).trans nlhfPositiveProfileR_margin_eq

/-- Adding the `adbc` voter realizes `s = 1/3`. -/
lemma nlhfPositive_addVoter_normalizedStrictMargin_eq :
    normalizedStrictMargin (addVoterProfile nlhfPositiveProfileR prefADBC) =
      nlhfPositiveInvolvementMargin ((1 : ℝ) / 3) := by
  funext x y
  have h := congrFun (congrFun nlhfPositiveProfileRPlus_margin_eq x) y
  simp only [normalizedStrictMargin3] at h
  rw [strictCount3_positiveRPlus_eq_addVoter,
    strictCount3_positiveRPlus_eq_addVoter] at h
  simp only [normalizedStrictMargin, strictMargin, strictCount_addVoterProfile,
    strictCount_fin2_eq, Fintype.card_option, Fintype.card_fin]
  norm_num at h ⊢
  linarith

/-- Profile realization of the negative witness `s = 0`. -/
lemma nlhfNegativeProfileS_normalizedStrictMargin_eq :
    normalizedStrictMargin nlhfNegativeProfileS =
      nlhfNegativeInvolvementMargin 0 :=
  (normalizedStrictMargin_fin2_eq _).trans nlhfNegativeProfileS_margin_eq

/-- Adding the `bcda` voter realizes `s = 1/3`. -/
lemma nlhfNegative_addVoter_normalizedStrictMargin_eq :
    normalizedStrictMargin (addVoterProfile nlhfNegativeProfileS prefBCDA) =
      nlhfNegativeInvolvementMargin ((1 : ℝ) / 3) := by
  funext x y
  have h := congrFun (congrFun nlhfNegativeProfileSPlus_margin_eq x) y
  simp only [normalizedStrictMargin3] at h
  rw [strictCount3_negativeSPlus_eq_addVoter,
    strictCount3_negativeSPlus_eq_addVoter] at h
  simp only [normalizedStrictMargin, strictMargin, strictCount_addVoterProfile,
    strictCount_fin2_eq, Fintype.card_option, Fintype.card_fin]
  norm_num at h ⊢
  linarith

/-- Pairwise completeness certificate: on the positive witness profile the
paper's `t_{x,y}`-normalized margin agrees with the `|V|`-normalized one. -/
lemma nlhfPositiveProfileR_paperNormalizedMargin_eq :
    paperNormalizedMargin nlhfPositiveProfileR =
      nlhfPositiveInvolvementMargin 1 := by
  rw [paperNormalizedMargin_eq_normalizedStrictMargin_of_linearProfile
    nlhfPositiveProfileR_linear]
  exact nlhfPositiveProfileR_normalizedStrictMargin_eq

/-- Pairwise completeness certificate for the negative witness profile. -/
lemma nlhfNegativeProfileS_paperNormalizedMargin_eq :
    paperNormalizedMargin nlhfNegativeProfileS =
      nlhfNegativeInvolvementMargin 0 := by
  rw [paperNormalizedMargin_eq_normalizedStrictMargin_of_linearProfile
    nlhfNegativeProfileS_linear]
  exact nlhfNegativeProfileS_normalizedStrictMargin_eq

/-- The concrete positive witness realizes the profile-level predicate. -/
lemma nlhfLinearAddsTopRealization_witness :
    LinearOrderAddsTopMargins
      (nlhfPositiveInvolvementMargin 1)
      (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) 0 :=
  ⟨2, nlhfPositiveProfileR, prefADBC,
    nlhfPositiveProfileR_linear, prefADBC_linear, prefADBC_ranksTop_zero,
    nlhfPositiveProfileR_normalizedStrictMargin_eq.symm,
    nlhfPositive_addVoter_normalizedStrictMargin_eq.symm⟩

/-- The concrete negative witness realizes the profile-level predicate. -/
lemma nlhfLinearAddsBottomRealization_witness :
    LinearOrderAddsBottomMargins
      (nlhfNegativeInvolvementMargin 0)
      (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) 0 :=
  ⟨2, nlhfNegativeProfileS, prefBCDA,
    nlhfNegativeProfileS_linear, prefBCDA_linear, prefBCDA_ranksBottom_zero,
    nlhfNegativeProfileS_normalizedStrictMargin_eq.symm,
    nlhfNegative_addVoter_normalizedStrictMargin_eq.symm⟩

/-- Positive-involvement half of Proposition `InvolveViolNLHF`, reduced to the
two scalar lemmas in the appendix.  The hypotheses `hselect` and `hsolve`
encode the calculation that the NLHF fixed point has `a`-coordinate `p_A(s)`
for the margin family above. -/
theorem nlhf_positive_involvement_violation_from_scalar_certificate
    (F : MatrixRule (Fin 4))
    (AddsTop : (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop)
    {A lam : ℝ} {Z pA : ℝ → ℝ}
    (hA : 0 < A) (hlam : 0 < lam)
    (hZpos : PositiveOnNonneg Z)
    (hZdec : StrictlyDecreasingOnNonneg Z)
    (hsolve : ∀ s : ℝ, 0 ≤ s → SolvesNLHFPEquation A lam Z s (pA s))
    (hselect : ∀ s : ℝ, 0 ≤ s →
      F (nlhfPositiveInvolvementMargin s) uniform4 0 = pA s)
    (hAdds :
      AddsTop (nlhfPositiveInvolvementMargin 1)
        (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) 0) :
    ViolatesPositiveInvolvement F AddsTop := by
  intro hsatisfies
  have hdrop_p :
      pA ((1 : ℝ) / 3) < pA 1 :=
    nlhfP_strictly_increasing hA hlam hZpos hZdec hsolve
      ((1 : ℝ) / 3) 1 (by norm_num) (by norm_num)
  have hdrop :
      F (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) uniform4 0 <
        F (nlhfPositiveInvolvementMargin 1) uniform4 0 := by
    rw [hselect ((1 : ℝ) / 3) (by norm_num), hselect 1 (by norm_num)]
    exact hdrop_p
  have hle :=
    hsatisfies (nlhfPositiveInvolvementMargin 1)
      (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) uniform4 0
      (nlhfPositiveInvolvementMargin_normalized (by norm_num) (by norm_num))
      (nlhfPositiveInvolvementMargin_normalized (by norm_num) (by norm_num))
      uniform4_fullSupport hAdds
  linarith

/-- Negative-involvement half of Proposition `InvolveViolNLHF`, reduced to the
same scalar monotonicity lemma. -/
theorem nlhf_negative_involvement_violation_from_scalar_certificate
    (F : MatrixRule (Fin 4))
    (AddsBottom : (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop)
    {A lam : ℝ} {Z pA : ℝ → ℝ}
    (hA : 0 < A) (hlam : 0 < lam)
    (hZpos : PositiveOnNonneg Z)
    (hZdec : StrictlyDecreasingOnNonneg Z)
    (hsolve : ∀ s : ℝ, 0 ≤ s → SolvesNLHFPEquation A lam Z s (pA s))
    (hselect : ∀ s : ℝ, 0 ≤ s →
      F (nlhfNegativeInvolvementMargin s) uniform4 0 = pA s)
    (hAdds :
      AddsBottom (nlhfNegativeInvolvementMargin 0)
        (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) 0) :
    ViolatesNegativeInvolvement F AddsBottom := by
  intro hsatisfies
  have hincrease_p :
      pA 0 < pA ((1 : ℝ) / 3) :=
    nlhfP_strictly_increasing hA hlam hZpos hZdec hsolve
      0 ((1 : ℝ) / 3) (by norm_num) (by norm_num)
  have hincrease :
      F (nlhfNegativeInvolvementMargin 0) uniform4 0 <
        F (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) uniform4 0 := by
    rw [hselect 0 (by norm_num), hselect ((1 : ℝ) / 3) (by norm_num)]
    exact hincrease_p
  have hle :=
    hsatisfies (nlhfNegativeInvolvementMargin 0)
      (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) uniform4 0
      (nlhfNegativeInvolvementMargin_normalized (by norm_num) (by norm_num))
      (nlhfNegativeInvolvementMargin_normalized (by norm_num) (by norm_num))
      uniform4_fullSupport hAdds
  linarith

/-- A compact certificate for the appendix proof of `InvolveViolNLHF`.
The paper supplies this certificate by:

* proving `Z` is strictly decreasing for the one-voter three-candidate lower
  profile;
* deriving the scalar equations with inverse-temperature `lambda = 1 / (2τ)`,
  `A = exp(lambda)` for the positive construction, and
  `A = exp(-lambda)` for the negative construction; and
* checking that the displayed linear-order profiles realize the margin
  parameters `1`, `1/3`, and `0`. -/
def HasNLHFInvolvementScalarCertificate
    (F : MatrixRule (Fin 4)) (τ : ℝ)
    (AddsTop AddsBottom :
      (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop) : Prop :=
  ∃ Z pPos pNeg : ℝ → ℝ,
    PositiveOnNonneg Z ∧
      StrictlyDecreasingOnNonneg Z ∧
        (∀ s : ℝ, 0 ≤ s →
          SolvesNLHFPEquation (Real.exp (1 / (2 * τ))) (1 / (2 * τ)) Z s
            (pPos s)) ∧
        (∀ s : ℝ, 0 ≤ s →
          F (nlhfPositiveInvolvementMargin s) uniform4 0 = pPos s) ∧
        (∀ s : ℝ, 0 ≤ s →
          SolvesNLHFPEquation (Real.exp (-(1 / (2 * τ)))) (1 / (2 * τ)) Z s
            (pNeg s)) ∧
        (∀ s : ℝ, 0 ≤ s →
          F (nlhfNegativeInvolvementMargin s) uniform4 0 = pNeg s) ∧
        AddsTop (nlhfPositiveInvolvementMargin 1)
          (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) 0 ∧
        AddsBottom (nlhfNegativeInvolvementMargin 0)
          (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) 0

/-- A stronger certificate for the new appendix proof, replacing the abstract
`Z`-decreasing assumption by the lower three-candidate NLHF fixed-point
selection used in Lemma `Z-decreasing`. -/
def HasNLHFInvolvementLowerFixedCertificate
    (F : MatrixRule (Fin 4)) (τ : ℝ)
    (AddsTop AddsBottom :
      (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop) : Prop :=
  ∃ q : ℝ → Fin 3 → ℝ,
  ∃ pPos pNeg : ℝ → ℝ,
    (∀ θ : ℝ, 0 ≤ θ → IsNLHFLowerFixedPoint θ (q θ)) ∧
      (∀ s : ℝ, 0 ≤ s →
        SolvesNLHFPEquation (Real.exp (1 / (2 * τ))) (1 / (2 * τ))
          (fun θ => nlhfLowerZ θ (q θ)) s (pPos s)) ∧
      (∀ s : ℝ, 0 ≤ s →
        F (nlhfPositiveInvolvementMargin s) uniform4 0 = pPos s) ∧
      (∀ s : ℝ, 0 ≤ s →
        SolvesNLHFPEquation (Real.exp (-(1 / (2 * τ)))) (1 / (2 * τ))
          (fun θ => nlhfLowerZ θ (q θ)) s (pNeg s)) ∧
      (∀ s : ℝ, 0 ≤ s →
        F (nlhfNegativeInvolvementMargin s) uniform4 0 = pNeg s) ∧
      AddsTop (nlhfPositiveInvolvementMargin 1)
        (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) 0 ∧
      AddsBottom (nlhfNegativeInvolvementMargin 0)
        (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) 0

/-- A fixed-point certificate closer to the text of the appendix proof.  It
assumes the cited uniqueness of the three-candidate lower NLHF fixed point,
plus four-candidate NLHF fixed points for the positive and negative margin
families.  The scalar equations are then derived in Lean. -/
def HasNLHFInvolvementFixedPointCertificate
    (F : MatrixRule (Fin 4)) (τ : ℝ)
    (AddsTop AddsBottom :
      (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop) : Prop :=
  ∃ q : ℝ → Fin 3 → ℝ,
  ∃ πPos πNeg : ℝ → Fin 4 → ℝ,
    (∀ θ : ℝ, 0 ≤ θ → IsNLHFLowerFixedPoint θ (q θ)) ∧
      (∀ θ : ℝ, 0 ≤ θ → ∀ r : Fin 3 → ℝ,
        IsNLHFLowerFixedPoint θ r → r = q θ) ∧
      (∀ s : ℝ, 0 ≤ s →
        IsNLHFFixedPoint τ (nlhfPositiveInvolvementMargin s) uniform4 (πPos s)) ∧
      (∀ s : ℝ, 0 ≤ s →
        F (nlhfPositiveInvolvementMargin s) uniform4 0 = πPos s 0) ∧
      (∀ s : ℝ, 0 ≤ s →
        IsNLHFFixedPoint τ (nlhfNegativeInvolvementMargin s) uniform4 (πNeg s)) ∧
      (∀ s : ℝ, 0 ≤ s →
        F (nlhfNegativeInvolvementMargin s) uniform4 0 = πNeg s 0) ∧
      AddsTop (nlhfPositiveInvolvementMargin 1)
        (nlhfPositiveInvolvementMargin ((1 : ℝ) / 3)) 0 ∧
      AddsBottom (nlhfNegativeInvolvementMargin 0)
        (nlhfNegativeInvolvementMargin ((1 : ℝ) / 3)) 0

/-- The four-candidate fixed-point certificate supplies the lower-fixed-point
certificate.  This formalizes the appendix step identifying the conditional
lottery on the non-`a` candidates with the unique lower-profile solution
`q^theta`. -/
theorem lower_fixed_certificate_of_fixed_point_certificate
    {τ : ℝ} (hτ : 0 < τ)
    {F : MatrixRule (Fin 4)}
    {AddsTop AddsBottom :
      (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop}
    (hcert : HasNLHFInvolvementFixedPointCertificate F τ AddsTop AddsBottom) :
    HasNLHFInvolvementLowerFixedCertificate F τ AddsTop AddsBottom := by
  rcases hcert with
    ⟨q, πPos, πNeg, hlowerFixed, hlowerUnique, hPosFP, hPosSelect,
      hNegFP, hNegSelect, hAddsTop, hAddsBottom⟩
  refine ⟨q, fun s => πPos s 0, fun s => πNeg s 0, hlowerFixed,
    ?_, hPosSelect, ?_, hNegSelect, hAddsTop, hAddsBottom⟩
  · intro s hs
    have hfp := hPosFP s hs
    rcases nlhf_positive_scalar_equation_from_fixed hτ hfp with
      ⟨hp0, hp1, heq⟩
    refine ⟨hp0, hp1, ?_⟩
    have hdenpos : 0 < 1 - πPos s 0 :=
      one_sub_pi0_pos_of_fullSupport4 hfp.2.2.1
    have hθ_nonneg :
        0 ≤ (1 / (2 * τ)) * s * (1 - πPos s 0) :=
      mul_nonneg (mul_nonneg (by positivity) hs) hdenpos.le
    have hcond :
        IsNLHFLowerFixedPoint ((1 / (2 * τ)) * s * (1 - πPos s 0))
          (conditionedNonA nlhfPositiveLowerIndex (πPos s)) :=
      nlhf_positive_conditioned_lower_fixed hτ hfp
    have hsame :
        conditionedNonA nlhfPositiveLowerIndex (πPos s) =
          q ((1 / (2 * τ)) * s * (1 - πPos s 0)) :=
      hlowerUnique ((1 / (2 * τ)) * s * (1 - πPos s 0))
        hθ_nonneg (conditionedNonA nlhfPositiveLowerIndex (πPos s)) hcond
    simpa [hsame] using heq
  · intro s hs
    have hfp := hNegFP s hs
    rcases nlhf_negative_scalar_equation_from_fixed hτ hfp with
      ⟨hp0, hp1, heq⟩
    refine ⟨hp0, hp1, ?_⟩
    have hdenpos : 0 < 1 - πNeg s 0 :=
      one_sub_pi0_pos_of_fullSupport4 hfp.2.2.1
    have hθ_nonneg :
        0 ≤ (1 / (2 * τ)) * s * (1 - πNeg s 0) :=
      mul_nonneg (mul_nonneg (by positivity) hs) hdenpos.le
    have hcond :
        IsNLHFLowerFixedPoint ((1 / (2 * τ)) * s * (1 - πNeg s 0))
          (conditionedNonA nlhfNegativeLowerIndex (πNeg s)) :=
      nlhf_negative_conditioned_lower_fixed hτ hfp
    have hsame :
        conditionedNonA nlhfNegativeLowerIndex (πNeg s) =
          q ((1 / (2 * τ)) * s * (1 - πNeg s 0)) :=
      hlowerUnique ((1 / (2 * τ)) * s * (1 - πNeg s 0))
        hθ_nonneg (conditionedNonA nlhfNegativeLowerIndex (πNeg s)) hcond
    simpa [hsame] using heq

/-- The lower fixed-point certificate supplies the scalar certificate: `Z` is
positive by construction and strictly decreasing by the formalized
`Z-decreasing` lemma. -/
theorem scalar_certificate_of_lower_fixed_certificate
    {τ : ℝ}
    {F : MatrixRule (Fin 4)}
    {AddsTop AddsBottom :
      (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop}
    (hcert : HasNLHFInvolvementLowerFixedCertificate F τ AddsTop AddsBottom) :
    HasNLHFInvolvementScalarCertificate F τ AddsTop AddsBottom := by
  rcases hcert with
    ⟨q, pPos, pNeg, hfixed, hPosSolve, hPosSelect,
      hNegSolve, hNegSelect, hAddsTop, hAddsBottom⟩
  refine ⟨fun θ => nlhfLowerZ θ (q θ), pPos, pNeg, ?_, ?_,
    hPosSolve, hPosSelect, hNegSolve, hNegSelect, hAddsTop, hAddsBottom⟩
  · intro θ _hθ
    exact nlhfLowerZ_pos θ (q θ)
  · exact Z_strictly_decreasing_from_lower_fixed_selection_fin3 hfixed

/-- Proposition `InvolveViolNLHF`, in the scalar-certificate form matching the
new appendix proof. -/
theorem InvolveViolNLHF_from_scalar_certificate
    {τ : ℝ} (hτ : 0 < τ)
    (F : MatrixRule (Fin 4))
    (AddsTop AddsBottom :
      (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop)
    (hcert : HasNLHFInvolvementScalarCertificate F τ AddsTop AddsBottom) :
    ViolatesPositiveInvolvement F AddsTop ∧
      ViolatesNegativeInvolvement F AddsBottom := by
  rcases hcert with
    ⟨Z, pPos, pNeg, hZpos, hZdec, hPosSolve, hPosSelect,
      hNegSolve, hNegSelect, hAddsTop, hAddsBottom⟩
  have hlambda : 0 < 1 / (2 * τ) := by positivity
  constructor
  · exact
      nlhf_positive_involvement_violation_from_scalar_certificate
        F AddsTop (Real.exp_pos _) hlambda hZpos hZdec hPosSolve hPosSelect hAddsTop
  · exact
      nlhf_negative_involvement_violation_from_scalar_certificate
        F AddsBottom (Real.exp_pos _) hlambda hZpos hZdec hNegSolve hNegSelect hAddsBottom

/-- Proposition `InvolveViolNLHF`, starting from the lower-fixed-point
certificate that mirrors Lemma `Z-decreasing` in the paper. -/
theorem InvolveViolNLHF_from_lower_fixed_certificate
    {τ : ℝ} (hτ : 0 < τ)
    (F : MatrixRule (Fin 4))
    (AddsTop AddsBottom :
      (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop)
    (hcert : HasNLHFInvolvementLowerFixedCertificate F τ AddsTop AddsBottom) :
    ViolatesPositiveInvolvement F AddsTop ∧
      ViolatesNegativeInvolvement F AddsBottom :=
  InvolveViolNLHF_from_scalar_certificate hτ F AddsTop AddsBottom
    (scalar_certificate_of_lower_fixed_certificate hcert)

/-- Proposition `InvolveViolNLHF`, in the fixed-point-certificate form closest
to the appendix proof in the paper. -/
theorem InvolveViolNLHF_from_fixed_point_certificate
    {τ : ℝ} (hτ : 0 < τ)
    (F : MatrixRule (Fin 4))
    (AddsTop AddsBottom :
      (Fin 4 → Fin 4 → ℝ) → (Fin 4 → Fin 4 → ℝ) → Fin 4 → Prop)
    (hcert : HasNLHFInvolvementFixedPointCertificate F τ AddsTop AddsBottom) :
    ViolatesPositiveInvolvement F AddsTop ∧
      ViolatesNegativeInvolvement F AddsBottom :=
  InvolveViolNLHF_from_lower_fixed_certificate hτ F AddsTop AddsBottom
    (lower_fixed_certificate_of_fixed_point_certificate hτ hcert)

end PaperFormalization
