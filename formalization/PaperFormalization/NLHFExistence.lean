import PaperFormalization.NLHFBasic
import Mathlib.Topology.Sion

open scoped BigOperators

namespace PaperFormalization

/-!
This module packages the finite NLHF existence/uniqueness input used by the
paper-facing monotonicity formalization.

The source proof is Proposition `prop:unique` in the original NLHF paper.  For
existence, this module specializes `Sion.exists_isSaddlePointOn` from
`Mathlib.Topology.Sion` to the finite lottery simplex.  That Mathlib module is
an Apache-2.0 dependency, is authored by Antoine Chambert-Loir and Anatole
Dedecker, and states that its proof follows Komiya's elementary proof of Sion's
theorem.  We formalize only the saddle theorem needed here, not a general
fixed-point theorem.  Strict-KL uniqueness is then proved from the fixed-point
equations.

Mathematical sources for the minimax step:

* Maurice Sion, "On general minimax theorems", *Pacific Journal of
  Mathematics* 8(1) (1958), 171--176,
  https://doi.org/10.2140/pjm.1958.8.171.
* Hidetoshi Komiya, "Elementary proof for Sion's minimax theorem", *Kodai
  Mathematical Journal* 11(1) (1988), 5--7,
  https://doi.org/10.2996/kmj/1138038812.
-/

/-- The finite lottery simplex is convex. -/
lemma convex_setOf_isLottery
    {α : Type*} [Fintype α] :
    Convex ℝ {p : α → ℝ | IsLottery p} := by
  classical
  intro p hp q hq a b ha hb hab
  constructor
  · intro x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 x)) (mul_nonneg hb (hq.1 x))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    rw [hp.2, hq.2]
    simpa using hab

/-- Finite KL can be written as the sum of the standard nonnegative
`klFun` terms. -/
lemma KL_eq_sum_rho_mul_klFun
    {α : Type*} [Fintype α]
    {π ρ : α → ℝ}
    (hπ : IsFullSupportLottery π)
    (hρ : IsFullSupportLottery ρ) :
    KL π ρ =
      Finset.univ.sum
        (fun x : α => ρ x * InformationTheory.klFun (π x / ρ x)) := by
  classical
  have hterm :
      ∀ x : α,
        ρ x * InformationTheory.klFun (π x / ρ x) =
          π x * Real.log (π x / ρ x) + (ρ x - π x) := by
    intro x
    unfold InformationTheory.klFun
    field_simp [(hρ.1 x).ne']
    ring
  have hsum_extra :
      Finset.univ.sum (fun x : α => ρ x - π x) = 0 := by
    rw [Finset.sum_sub_distrib, hρ.2, hπ.2]
    ring
  have hsum :
      Finset.univ.sum
          (fun x : α => ρ x * InformationTheory.klFun (π x / ρ x)) =
        KL π ρ := by
    calc
      Finset.univ.sum
          (fun x : α => ρ x * InformationTheory.klFun (π x / ρ x))
          =
        Finset.univ.sum
          (fun x : α =>
            π x * Real.log (π x / ρ x) + (ρ x - π x)) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          exact hterm x
      _ =
        Finset.univ.sum (fun x : α => π x * Real.log (π x / ρ x)) +
          Finset.univ.sum (fun x : α => ρ x - π x) := by
          rw [Finset.sum_add_distrib]
      _ = KL π ρ := by
          rw [hsum_extra]
          simp [KL]
  exact hsum.symm

/-- Equality case of finite Gibbs' inequality under full support. -/
lemma KL_eq_zero_iff_of_fullSupport
    {α : Type*} [Fintype α]
    {π ρ : α → ℝ}
    (hπ : IsFullSupportLottery π)
    (hρ : IsFullSupportLottery ρ) :
    KL π ρ = 0 ↔ π = ρ := by
  classical
  constructor
  · intro hzero
    funext x
    have hsumzero :
        Finset.univ.sum
            (fun y : α => ρ y * InformationTheory.klFun (π y / ρ y)) = 0 := by
      rw [← KL_eq_sum_rho_mul_klFun hπ hρ]
      exact hzero
    have hterm_nonneg :
        ∀ y : α, y ∈ (Finset.univ : Finset α) →
          0 ≤ ρ y * InformationTheory.klFun (π y / ρ y) := by
      intro y _hy
      exact mul_nonneg (hρ.1 y).le
        (InformationTheory.klFun_nonneg
          (div_nonneg (hπ.1 y).le (hρ.1 y).le))
    have hxzero :
        ρ x * InformationTheory.klFun (π x / ρ x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsumzero x
        (Finset.mem_univ x)
    have hklzero : InformationTheory.klFun (π x / ρ x) = 0 := by
      rcases mul_eq_zero.mp hxzero with hρzero | hklzero
      · exact False.elim ((hρ.1 x).ne' hρzero)
      · exact hklzero
    have hratio : π x / ρ x = 1 :=
      (InformationTheory.klFun_eq_zero_iff
        (div_nonneg (hπ.1 x).le (hρ.1 x).le)).mp hklzero
    field_simp [(hρ.1 x).ne'] at hratio
    exact hratio
  · intro h
    subst h
    unfold KL
    simp

/-- Finite KL as `klFun` terms for a possibly boundary lottery. -/
lemma KL_eq_sum_rho_mul_klFun_of_lottery
    {α : Type*} [Fintype α]
    {π ρ : α → ℝ}
    (hπ : IsLottery π)
    (hρ : IsFullSupportLottery ρ) :
    KL π ρ =
      Finset.univ.sum
        (fun x : α => ρ x * InformationTheory.klFun (π x / ρ x)) := by
  classical
  have hterm :
      ∀ x : α,
        ρ x * InformationTheory.klFun (π x / ρ x) =
          π x * Real.log (π x / ρ x) + (ρ x - π x) := by
    intro x
    unfold InformationTheory.klFun
    field_simp [(hρ.1 x).ne']
    ring
  have hsum_extra :
      Finset.univ.sum (fun x : α => ρ x - π x) = 0 := by
    rw [Finset.sum_sub_distrib, hρ.2, hπ.2]
    ring
  have hsum :
      Finset.univ.sum
          (fun x : α => ρ x * InformationTheory.klFun (π x / ρ x)) =
        KL π ρ := by
    calc
      Finset.univ.sum
          (fun x : α => ρ x * InformationTheory.klFun (π x / ρ x))
          =
        Finset.univ.sum
          (fun x : α =>
            π x * Real.log (π x / ρ x) + (ρ x - π x)) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          exact hterm x
      _ =
        Finset.univ.sum (fun x : α => π x * Real.log (π x / ρ x)) +
          Finset.univ.sum (fun x : α => ρ x - π x) := by
          rw [Finset.sum_add_distrib]
      _ = KL π ρ := by
          rw [hsum_extra]
          simp [KL]
  exact hsum.symm

/-- On the lottery simplex, finite KL is represented by a globally continuous
sum of Mathlib's `klFun` terms. -/
lemma continuousOn_KL_lottery
    {α : Type*} [Fintype α]
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ContinuousOn (fun p : α → ℝ => KL p ρ)
      {p : α → ℝ | IsLottery p} := by
  classical
  let K : (α → ℝ) → ℝ := fun p =>
    Finset.univ.sum
      (fun x : α => ρ x * InformationTheory.klFun (p x / ρ x))
  have hK : Continuous K := by
    dsimp [K]
    exact continuous_finsetSum Finset.univ fun x _hx =>
      continuous_const.mul
        (InformationTheory.continuous_klFun.comp
          (((continuous_apply x :
              Continuous (fun p : α → ℝ => p x))).div_const (ρ x)))
  refine hK.continuousOn.congr ?_
  intro p hp
  exact KL_eq_sum_rho_mul_klFun_of_lottery hp hρ

/-- Finite KL is convex in its first argument on the lottery simplex. -/
lemma convexOn_KL_lottery
    {α : Type*} [Fintype α]
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ConvexOn ℝ {p : α → ℝ | IsLottery p} (fun p => KL p ρ) := by
  classical
  refine ⟨convex_setOf_isLottery, ?_⟩
  intro p hp q hq a b ha hb hab
  have hpq : IsLottery (a • p + b • q) :=
    convex_setOf_isLottery hp hq ha hb hab
  change KL (a • p + b • q) ρ ≤ a * KL p ρ + b * KL q ρ
  rw [KL_eq_sum_rho_mul_klFun_of_lottery hpq hρ,
    KL_eq_sum_rho_mul_klFun_of_lottery hp hρ,
    KL_eq_sum_rho_mul_klFun_of_lottery hq hρ]
  have hterm : ∀ x : α,
      ρ x * InformationTheory.klFun ((a • p + b • q) x / ρ x) ≤
        a * (ρ x * InformationTheory.klFun (p x / ρ x)) +
          b * (ρ x * InformationTheory.klFun (q x / ρ x)) := by
    intro x
    have hconv := InformationTheory.convexOn_klFun.2
      (show p x / ρ x ∈ Set.Ici (0 : ℝ) from
        div_nonneg (hp.1 x) (hρ.1 x).le)
      (show q x / ρ x ∈ Set.Ici (0 : ℝ) from
        div_nonneg (hq.1 x) (hρ.1 x).le)
      ha hb hab
    have harg :
        (a • p + b • q) x / ρ x =
          a * (p x / ρ x) + b * (q x / ρ x) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [(hρ.1 x).ne']
    rw [harg]
    have hscaled := mul_le_mul_of_nonneg_left hconv (hρ.1 x).le
    calc
      ρ x * InformationTheory.klFun
          (a * (p x / ρ x) + b * (q x / ρ x)) ≤
        ρ x * (a * InformationTheory.klFun (p x / ρ x) +
          b * InformationTheory.klFun (q x / ρ x)) := by
            simpa only [smul_eq_mul] using hscaled
      _ = a * (ρ x * InformationTheory.klFun (p x / ρ x)) +
          b * (ρ x * InformationTheory.klFun (q x / ρ x)) := by ring
  calc
    Finset.univ.sum
        (fun x : α => ρ x * InformationTheory.klFun ((a • p + b • q) x / ρ x))
        ≤ Finset.univ.sum
          (fun x : α =>
            a * (ρ x * InformationTheory.klFun (p x / ρ x)) +
              b * (ρ x * InformationTheory.klFun (q x / ρ x))) :=
      Finset.sum_le_sum fun x _hx => hterm x
    _ = a • Finset.univ.sum
          (fun x : α => ρ x * InformationTheory.klFun (p x / ρ x)) +
        b • Finset.univ.sum
          (fun x : α => ρ x * InformationTheory.klFun (q x / ρ x)) := by
      simp only [Finset.sum_add_distrib, smul_eq_mul]
      simp_rw [← Finset.mul_sum]

/-- Gibbs' inequality for a boundary lottery against a full-support reference. -/
lemma KL_nonneg_of_lottery_fullSupport
    {α : Type*} [Fintype α]
    {π ρ : α → ℝ}
    (hπ : IsLottery π)
    (hρ : IsFullSupportLottery ρ) :
    0 ≤ KL π ρ := by
  rw [KL_eq_sum_rho_mul_klFun_of_lottery hπ hρ]
  exact Finset.sum_nonneg fun x _hx =>
    mul_nonneg (hρ.1 x).le
      (InformationTheory.klFun_nonneg
        (div_nonneg (hπ.1 x) (hρ.1 x).le))

/-- Equality case of finite Gibbs' inequality for a boundary lottery against a
full-support reference. -/
lemma KL_eq_zero_iff_of_lottery_fullSupport
    {α : Type*} [Fintype α]
    {π ρ : α → ℝ}
    (hπ : IsLottery π)
    (hρ : IsFullSupportLottery ρ) :
    KL π ρ = 0 ↔ π = ρ := by
  classical
  constructor
  · intro hzero
    funext x
    have hsumzero :
        Finset.univ.sum
            (fun y : α => ρ y * InformationTheory.klFun (π y / ρ y)) = 0 := by
      rw [← KL_eq_sum_rho_mul_klFun_of_lottery hπ hρ]
      exact hzero
    have hterm_nonneg :
        ∀ y : α, y ∈ (Finset.univ : Finset α) →
          0 ≤ ρ y * InformationTheory.klFun (π y / ρ y) := by
      intro y _hy
      exact mul_nonneg (hρ.1 y).le
        (InformationTheory.klFun_nonneg
          (div_nonneg (hπ.1 y) (hρ.1 y).le))
    have hxzero :
        ρ x * InformationTheory.klFun (π x / ρ x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsumzero x
        (Finset.mem_univ x)
    have hklzero : InformationTheory.klFun (π x / ρ x) = 0 := by
      rcases mul_eq_zero.mp hxzero with hρzero | hklzero
      · exact False.elim ((hρ.1 x).ne' hρzero)
      · exact hklzero
    have hratio : π x / ρ x = 1 :=
      (InformationTheory.klFun_eq_zero_iff
        (div_nonneg (hπ.1 x) (hρ.1 x).le)).mp hklzero
    field_simp [(hρ.1 x).ne'] at hratio
    exact hratio
  · intro h
    subst h
    unfold KL
    simp

/-- Gibbs' inequality, proved from the `klFun` decomposition above. -/
lemma KL_nonneg_of_fullSupport_strictKL
    {α : Type*} [Fintype α]
    {π ρ : α → ℝ}
    (hπ : IsFullSupportLottery π)
    (hρ : IsFullSupportLottery ρ) :
    0 ≤ KL π ρ := by
  rw [KL_eq_sum_rho_mul_klFun hπ hρ]
  exact Finset.sum_nonneg fun x _hx =>
    mul_nonneg (hρ.1 x).le
      (InformationTheory.klFun_nonneg
        (div_nonneg (hπ.1 x).le (hρ.1 x).le))

/-- The bilinear value against a lottery is the lottery-weighted sum of
expected margins.  This local copy keeps the strict-KL uniqueness module
independent of helper-lemma freshness in the long monotonicity file. -/
lemma marginValue_eq_sum_expected_strictKL
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
lemma nlhfFixedPoint_log_reference_strictKL
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
lemma nlhfFixedPoint_weighted_log_reference_sum_strictKL
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
        rw [nlhfFixedPoint_log_reference_strictKL hfp x]
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
        rw [← marginValue_eq_sum_expected_strictKL]
        rw [hν.2]
        ring

/-- The fixed point's KL-to-reference value equals the negative normalizer
log when the margin matrix is skew-symmetric. -/
lemma nlhfFixedPoint_KL_reference_eq_neg_log_denominator_strictKL
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
    nlhfFixedPoint_weighted_log_reference_sum_strictKL
      (ν := π) hfp hfp.2.2.1
  have hself : marginValue M π π = 0 :=
    marginValue_self_eq_zero_of_normalized π hM
  simpa [KL, hself] using hsum

/-- KL decomposition induced by an NLHF fixed point. -/
lemma nlhfFixedPoint_KL_gap_identity_strictKL
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
    simpa [Z] using nlhfFixedPoint_weighted_log_reference_sum_strictKL
      (ν := ν) hfp hν
  have hKLπ :
      KL π ρ = -Real.log Z := by
    simpa [Z] using
      nlhfFixedPoint_KL_reference_eq_neg_log_denominator_strictKL hM hfp
  rw [hdecomp, hsum, hKLπ]
  ring

/-- Strict-KL uniqueness of the NLHF fixed point for normalized finite margin
matrices.  This is the Lean version of the strict-KL part of the original
Sion/Rosen proof: adding the two KL-gap identities cancels the skew margin
terms and forces the symmetric KL divergence to be zero. -/
theorem nlhfFixedPoint_unique_of_normalized
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π σ : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hπ : IsNLHFFixedPoint τ M ρ π)
    (hσ : IsNLHFFixedPoint τ M ρ σ) :
    π = σ := by
  have hgapπ :=
    nlhfFixedPoint_KL_gap_identity_strictKL hM hπ hσ.2.2.1
  have hgapσ :=
    nlhfFixedPoint_KL_gap_identity_strictKL hM hσ hπ.2.2.1
  have hswap :
      marginValue M σ π = -marginValue M π σ :=
    marginValue_swap_eq_neg_of_skew σ π hM.2.1
  have hsumzero : KL σ π + KL π σ = 0 := by
    rw [hgapπ, hgapσ, hswap]
    ring
  have hKLσπ_nonneg : 0 ≤ KL σ π :=
    KL_nonneg_of_fullSupport_strictKL hσ.2.2.1 hπ.2.2.1
  have hKLπσ_nonneg : 0 ≤ KL π σ :=
    KL_nonneg_of_fullSupport_strictKL hπ.2.2.1 hσ.2.2.1
  have hKLσπ_zero : KL σ π = 0 := by
    nlinarith
  exact ((KL_eq_zero_iff_of_fullSupport hσ.2.2.1 hπ.2.2.1).mp
    hKLσπ_zero).symm

/-- The fixed-point existence interface induced by the finite Sion saddle
theorem: it supplies at least one finite fixed point for every positive
temperature, normalized finite margin matrix, and full-support reference
lottery. -/
def SionStrictKLFixedPointExistence
    {α : Type*} [Fintype α] : Prop :=
  NLHFFixedPointExists (α := α)

/-- The Sion/Rosen existence input, paired with the strict-KL uniqueness proof
above, gives the exact finite existence-and-uniqueness theorem needed by the
paper. -/
theorem exists_unique_nlhfFixedPoint_of_sionStrictKL
    {α : Type*} [Fintype α]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ, IsNLHFFixedPoint τ M ρ π := by
  rcases hexists hτ hM hρ with ⟨π, hπ⟩
  refine ⟨π, hπ, ?_⟩
  intro σ hσ
  exact nlhfFixedPoint_unique_of_normalized hM hσ hπ

/-- The finite-dimensional regularized first-player payoff with the second
lottery held fixed. -/
noncomputable def nlhfFirstPayoff
    {α : Type*} [Fintype α]
    (τ : ℝ) (M : α → α → ℝ) (ρ p q : α → ℝ) : ℝ :=
  marginValue M p q - (1 / nlhfLambda τ) * KL p ρ

/-- The zero-sum regularized payoff used in the Sion/Rosen saddle formulation. -/
noncomputable def nlhfSionValue
    {α : Type*} [Fintype α]
    (τ : ℝ) (M : α → α → ℝ) (ρ p q : α → ℝ) : ℝ :=
  marginValue M p q - (1 / nlhfLambda τ) * KL p ρ +
    (1 / nlhfLambda τ) * KL q ρ

/-- `marginValue` is affine in its first lottery argument. -/
lemma marginValue_affine_left
    {α : Type*} [Fintype α]
    (M : α → α → ℝ) (q p r : α → ℝ) (a b : ℝ) :
    marginValue M (a • p + b • r) q =
      a * marginValue M p q + b * marginValue M r q := by
  classical
  unfold marginValue
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    Finset.univ.sum (fun x =>
        Finset.univ.sum (fun y => (a * p x + b * r x) * q y * M x y)) =
      Finset.univ.sum (fun x =>
        Finset.univ.sum (fun y =>
          a * (p x * q y * M x y) + b * (r x * q y * M x y))) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        refine Finset.sum_congr rfl ?_
        intro y _hy
        ring
    _ = a * Finset.univ.sum (fun x =>
          Finset.univ.sum (fun y => p x * q y * M x y)) +
        b * Finset.univ.sum (fun x =>
          Finset.univ.sum (fun y => r x * q y * M x y)) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- `marginValue` is affine in its second lottery argument. -/
lemma marginValue_affine_right
    {α : Type*} [Fintype α]
    (M : α → α → ℝ) (p q r : α → ℝ) (a b : ℝ) :
    marginValue M p (a • q + b • r) =
      a * marginValue M p q + b * marginValue M p r := by
  classical
  unfold marginValue
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    Finset.univ.sum (fun x =>
        Finset.univ.sum (fun y => p x * (a * q y + b * r y) * M x y)) =
      Finset.univ.sum (fun x =>
        Finset.univ.sum (fun y =>
          a * (p x * q y * M x y) + b * (p x * r y * M x y))) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        refine Finset.sum_congr rfl ?_
        intro y _hy
        ring
    _ = a * Finset.univ.sum (fun x =>
          Finset.univ.sum (fun y => p x * q y * M x y)) +
        b * Finset.univ.sum (fun x =>
          Finset.univ.sum (fun y => p x * r y * M x y)) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- A fixed right argument makes `marginValue` concave on the lottery simplex. -/
lemma concaveOn_marginValue_left
    {α : Type*} [Fintype α]
    (M : α → α → ℝ) (q : α → ℝ) :
    ConcaveOn ℝ {p : α → ℝ | IsLottery p} (fun p => marginValue M p q) := by
  refine ⟨convex_setOf_isLottery, ?_⟩
  intro p hp r hr a b ha hb hab
  exact le_of_eq (marginValue_affine_left M q p r a b).symm

/-- A fixed left argument makes `marginValue` convex on the lottery simplex. -/
lemma convexOn_marginValue_right
    {α : Type*} [Fintype α]
    (M : α → α → ℝ) (p : α → ℝ) :
    ConvexOn ℝ {q : α → ℝ | IsLottery q} (fun q => marginValue M p q) := by
  refine ⟨convex_setOf_isLottery, ?_⟩
  intro q hq r hr a b ha hb hab
  exact le_of_eq (marginValue_affine_right M p q r a b)

/-- `marginValue` is continuous in its first lottery argument. -/
lemma continuous_marginValue_left
    {α : Type*} [Fintype α]
    (M : α → α → ℝ) (q : α → ℝ) :
    Continuous (fun p : α → ℝ => marginValue M p q) := by
  classical
  unfold marginValue
  exact continuous_finsetSum Finset.univ fun x _hx =>
    continuous_finsetSum Finset.univ fun y _hy =>
      ((continuous_apply x).mul continuous_const).mul continuous_const

/-- `marginValue` is continuous in its second lottery argument. -/
lemma continuous_marginValue_right
    {α : Type*} [Fintype α]
    (M : α → α → ℝ) (p : α → ℝ) :
    Continuous (fun q : α → ℝ => marginValue M p q) := by
  classical
  unfold marginValue
  exact continuous_finsetSum Finset.univ fun x _hx =>
    continuous_finsetSum Finset.univ fun y _hy =>
      (continuous_const.mul (continuous_apply y)).mul continuous_const

/-- The softmax best response to a fixed opponent lottery. -/
noncomputable def nlhfSoftmaxResponse
    {α : Type*} [Fintype α]
    (τ : ℝ) (M : α → α → ℝ) (ρ q : α → ℝ) : α → ℝ :=
  fun x =>
    ρ x * Real.exp (expectedMargin M q x / (2 * τ)) /
      Finset.univ.sum
        (fun z : α => ρ z * Real.exp (expectedMargin M q z / (2 * τ)))

lemma nlhfSoftmax_den_pos
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ q : α → ℝ}
    (hρ : IsFullSupportLottery ρ) :
    0 <
      Finset.univ.sum
        (fun z : α => ρ z * Real.exp (expectedMargin M q z / (2 * τ))) := by
  classical
  have huniv_nonempty : (Finset.univ : Finset α).Nonempty := by
    by_contra hempty
    have hsum_zero :
        Finset.univ.sum (fun z : α => ρ z) = 0 := by
      exact Finset.sum_eq_zero fun z hz =>
        False.elim (hempty ⟨z, hz⟩)
    linarith [hρ.2]
  exact Finset.sum_pos
    (fun z _hz => mul_pos (hρ.1 z) (Real.exp_pos _))
    huniv_nonempty

/-- The softmax response is a full-support lottery. -/
lemma nlhfSoftmaxResponse_fullSupport
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ q : α → ℝ}
    (hρ : IsFullSupportLottery ρ) :
    IsFullSupportLottery (nlhfSoftmaxResponse τ M ρ q) := by
  classical
  let Z : ℝ := Finset.univ.sum
    (fun z : α => ρ z * Real.exp (expectedMargin M q z / (2 * τ)))
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact nlhfSoftmax_den_pos hρ
  refine ⟨?pos, ?sum⟩
  · intro x
    dsimp [nlhfSoftmaxResponse, Z]
    exact div_pos (mul_pos (hρ.1 x) (Real.exp_pos _)) hZpos
  · calc
      Finset.univ.sum (fun x : α => nlhfSoftmaxResponse τ M ρ q x)
          =
        Finset.univ.sum
          (fun x : α =>
            ρ x * Real.exp (expectedMargin M q x / (2 * τ)) / Z) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rfl
      _ = Z / Z := by
          rw [Finset.sum_div]
      _ = 1 := by
          field_simp [hZpos.ne']

/-- Log-reference form for the softmax response to a fixed opponent lottery. -/
lemma nlhfSoftmaxResponse_log_reference
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ q : α → ℝ}
    (hρ : IsFullSupportLottery ρ) (i : α) :
    Real.log (nlhfSoftmaxResponse τ M ρ q i / ρ i) =
      nlhfLambda τ * expectedMargin M q i -
        Real.log
          (Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M q z / (2 * τ)))) := by
  classical
  let Z : ℝ := Finset.univ.sum
    (fun z : α => ρ z * Real.exp (expectedMargin M q z / (2 * τ)))
  have hρi : 0 < ρ i := hρ.1 i
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact nlhfSoftmax_den_pos hρ
  have hratio :
      nlhfSoftmaxResponse τ M ρ q i / ρ i =
        Real.exp (expectedMargin M q i / (2 * τ)) / Z := by
    dsimp [nlhfSoftmaxResponse, Z]
    field_simp [hρi.ne']
  rw [hratio]
  rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne']
  rw [Real.log_exp]
  dsimp [Z]
  unfold nlhfLambda
  ring

/-- Summed log-reference form for the softmax response. -/
lemma nlhfSoftmaxResponse_weighted_log_reference_sum
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ q ν : α → ℝ}
    (hρ : IsFullSupportLottery ρ)
    (hν : IsFullSupportLottery ν) :
    Finset.univ.sum
        (fun x : α =>
          ν x * Real.log (nlhfSoftmaxResponse τ M ρ q x / ρ x)) =
      nlhfLambda τ * marginValue M ν q -
        Real.log
          (Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M q z / (2 * τ)))) := by
  classical
  let Z : ℝ := Finset.univ.sum
    (fun z : α => ρ z * Real.exp (expectedMargin M q z / (2 * τ)))
  calc
    Finset.univ.sum
        (fun x : α =>
          ν x * Real.log (nlhfSoftmaxResponse τ M ρ q x / ρ x))
        =
      Finset.univ.sum
        (fun x : α =>
          ν x * (nlhfLambda τ * expectedMargin M q x - Real.log Z)) := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        rw [nlhfSoftmaxResponse_log_reference hρ x]
    _ =
      nlhfLambda τ * Finset.univ.sum
        (fun x : α => ν x * expectedMargin M q x) -
          Finset.univ.sum (fun x : α => ν x) * Real.log Z := by
        calc
          Finset.univ.sum
              (fun x : α =>
                ν x * (nlhfLambda τ * expectedMargin M q x - Real.log Z)) =
            Finset.univ.sum
              (fun x : α =>
                nlhfLambda τ * (ν x * expectedMargin M q x) -
                  ν x * Real.log Z) := by
              refine Finset.sum_congr rfl ?_
              intro x _hx
              ring
          _ =
            Finset.univ.sum
              (fun x : α =>
                nlhfLambda τ * (ν x * expectedMargin M q x)) -
              Finset.univ.sum (fun x : α => ν x * Real.log Z) := by
              rw [Finset.sum_sub_distrib]
          _ =
            nlhfLambda τ * Finset.univ.sum
              (fun x : α => ν x * expectedMargin M q x) -
                Finset.univ.sum (fun x : α => ν x) * Real.log Z := by
              rw [← Finset.mul_sum]
              rw [Finset.sum_mul]
    _ = nlhfLambda τ * marginValue M ν q - Real.log Z := by
        rw [← marginValue_eq_sum_expected_strictKL]
        rw [hν.2]
        ring

/-- KL decomposition for the softmax response to a fixed opponent lottery. -/
lemma nlhfSoftmaxResponse_KL_gap_identity
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ q ν : α → ℝ}
    (hρ : IsFullSupportLottery ρ)
    (hν : IsFullSupportLottery ν) :
    KL ν (nlhfSoftmaxResponse τ M ρ q) =
      KL ν ρ - nlhfLambda τ * marginValue M ν q +
        Real.log
          (Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M q z / (2 * τ)))) := by
  classical
  let br : α → ℝ := nlhfSoftmaxResponse τ M ρ q
  have hbr : IsFullSupportLottery br :=
    nlhfSoftmaxResponse_fullSupport hρ
  have hdecomp :
      KL ν br =
        KL ν ρ -
          Finset.univ.sum (fun x : α => ν x * Real.log (br x / ρ x)) := by
    unfold KL
    calc
      Finset.univ.sum (fun x : α => ν x * Real.log (ν x / br x))
          =
        Finset.univ.sum
          (fun x : α =>
            ν x * (Real.log (ν x / ρ x) - Real.log (br x / ρ x))) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [Real.log_div (hν.1 x).ne' (hbr.1 x).ne',
            Real.log_div (hν.1 x).ne' (hρ.1 x).ne',
            Real.log_div (hbr.1 x).ne' (hρ.1 x).ne']
          ring
      _ =
        Finset.univ.sum (fun x : α => ν x * Real.log (ν x / ρ x)) -
          Finset.univ.sum (fun x : α => ν x * Real.log (br x / ρ x)) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
  have hsum :
      Finset.univ.sum (fun x : α => ν x * Real.log (br x / ρ x)) =
        nlhfLambda τ * marginValue M ν q -
          Real.log
            (Finset.univ.sum
              (fun z : α =>
                ρ z * Real.exp (expectedMargin M q z / (2 * τ)))) := by
    simpa [br] using
      nlhfSoftmaxResponse_weighted_log_reference_sum
        (τ := τ) (M := M) (ρ := ρ) (q := q) hρ hν
  rw [hdecomp, hsum]
  ring

/-- KL decomposition for the softmax response, allowing the comparison lottery
to lie on the boundary of the simplex. -/
lemma nlhfSoftmaxResponse_KL_gap_identity_lottery
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ q ν : α → ℝ}
    (hρ : IsFullSupportLottery ρ)
    (hν : IsLottery ν) :
    KL ν (nlhfSoftmaxResponse τ M ρ q) =
      KL ν ρ - nlhfLambda τ * marginValue M ν q +
        Real.log
          (Finset.univ.sum
            (fun z : α =>
              ρ z * Real.exp (expectedMargin M q z / (2 * τ)))) := by
  classical
  let br : α → ℝ := nlhfSoftmaxResponse τ M ρ q
  have hbr : IsFullSupportLottery br :=
    nlhfSoftmaxResponse_fullSupport hρ
  have hdecomp :
      KL ν br =
        KL ν ρ -
          Finset.univ.sum (fun x : α => ν x * Real.log (br x / ρ x)) := by
    unfold KL
    calc
      Finset.univ.sum (fun x : α => ν x * Real.log (ν x / br x))
          =
        Finset.univ.sum
          (fun x : α =>
            ν x * (Real.log (ν x / ρ x) - Real.log (br x / ρ x))) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          by_cases hνx : ν x = 0
          · simp [hνx]
          · have hνxpos : 0 < ν x := lt_of_le_of_ne (hν.1 x) (Ne.symm hνx)
            rw [Real.log_div hνxpos.ne' (hbr.1 x).ne',
              Real.log_div hνxpos.ne' (hρ.1 x).ne',
              Real.log_div (hbr.1 x).ne' (hρ.1 x).ne']
            ring
      _ =
        Finset.univ.sum (fun x : α => ν x * Real.log (ν x / ρ x)) -
          Finset.univ.sum (fun x : α => ν x * Real.log (br x / ρ x)) := by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
  -- The previous displayed sum only uses the weights `ν`, so we can prove it
  -- directly without requiring `ν` to have full support.
  have hsum_lottery :
      Finset.univ.sum (fun x : α => ν x * Real.log (br x / ρ x)) =
        nlhfLambda τ * marginValue M ν q -
          Real.log
            (Finset.univ.sum
              (fun z : α =>
                ρ z * Real.exp (expectedMargin M q z / (2 * τ)))) := by
    classical
    let Z : ℝ := Finset.univ.sum
      (fun z : α => ρ z * Real.exp (expectedMargin M q z / (2 * τ)))
    calc
      Finset.univ.sum (fun x : α => ν x * Real.log (br x / ρ x))
          =
        Finset.univ.sum
          (fun x : α =>
            ν x * (nlhfLambda τ * expectedMargin M q x - Real.log Z)) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [nlhfSoftmaxResponse_log_reference (τ := τ) (M := M)
            (ρ := ρ) (q := q) hρ x]
      _ =
        nlhfLambda τ * Finset.univ.sum
          (fun x : α => ν x * expectedMargin M q x) -
            Finset.univ.sum (fun x : α => ν x) * Real.log Z := by
          calc
            Finset.univ.sum
                (fun x : α =>
                  ν x * (nlhfLambda τ * expectedMargin M q x - Real.log Z)) =
              Finset.univ.sum
                (fun x : α =>
                  nlhfLambda τ * (ν x * expectedMargin M q x) -
                    ν x * Real.log Z) := by
                refine Finset.sum_congr rfl ?_
                intro x _hx
                ring
            _ =
              Finset.univ.sum
                (fun x : α =>
                  nlhfLambda τ * (ν x * expectedMargin M q x)) -
              Finset.univ.sum (fun x : α => ν x * Real.log Z) := by
                rw [Finset.sum_sub_distrib]
            _ =
              nlhfLambda τ * Finset.univ.sum
                (fun x : α => ν x * expectedMargin M q x) -
                  Finset.univ.sum (fun x : α => ν x) * Real.log Z := by
                rw [← Finset.mul_sum]
                rw [Finset.sum_mul]
      _ =
        nlhfLambda τ * marginValue M ν q - Real.log Z := by
          rw [← marginValue_eq_sum_expected_strictKL]
          rw [hν.2]
          ring
  rw [hdecomp, hsum_lottery]
  ring

/-- The softmax response gives an exact payoff gap: every full-support
comparison lottery loses by its KL divergence from the response. -/
lemma nlhfFirstPayoff_softmax_gap
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ q ν : α → ℝ}
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hν : IsFullSupportLottery ν) :
    nlhfFirstPayoff τ M ρ ν q =
      nlhfFirstPayoff τ M ρ (nlhfSoftmaxResponse τ M ρ q) q -
        (1 / nlhfLambda τ) *
          KL ν (nlhfSoftmaxResponse τ M ρ q) := by
  classical
  let br : α → ℝ := nlhfSoftmaxResponse τ M ρ q
  let Z : ℝ := Finset.univ.sum
    (fun z : α => ρ z * Real.exp (expectedMargin M q z / (2 * τ)))
  have hbr : IsFullSupportLottery br :=
    nlhfSoftmaxResponse_fullSupport hρ
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hgap :
      KL ν br =
        KL ν ρ - nlhfLambda τ * marginValue M ν q + Real.log Z := by
    simpa [br, Z] using
      nlhfSoftmaxResponse_KL_gap_identity
        (τ := τ) (M := M) (ρ := ρ) (q := q) hρ hν
  have hbrKL :
      KL br ρ =
        nlhfLambda τ * marginValue M br q - Real.log Z := by
    have hsum :=
      nlhfSoftmaxResponse_weighted_log_reference_sum
        (τ := τ) (M := M) (ρ := ρ) (q := q) (ν := br) hρ hbr
    simpa [KL, br, Z] using hsum
  unfold nlhfFirstPayoff
  rw [hgap, hbrKL]
  field_simp [hlam.ne']
  ring

/-- Softmax payoff gap for a comparison lottery on the closed simplex. -/
lemma nlhfFirstPayoff_softmax_gap_lottery
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ q ν : α → ℝ}
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hν : IsLottery ν) :
    nlhfFirstPayoff τ M ρ ν q =
      nlhfFirstPayoff τ M ρ (nlhfSoftmaxResponse τ M ρ q) q -
        (1 / nlhfLambda τ) *
          KL ν (nlhfSoftmaxResponse τ M ρ q) := by
  classical
  let br : α → ℝ := nlhfSoftmaxResponse τ M ρ q
  let Z : ℝ := Finset.univ.sum
    (fun z : α => ρ z * Real.exp (expectedMargin M q z / (2 * τ)))
  have hbr : IsFullSupportLottery br :=
    nlhfSoftmaxResponse_fullSupport hρ
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hgap :
      KL ν br =
        KL ν ρ - nlhfLambda τ * marginValue M ν q + Real.log Z := by
    simpa [br, Z] using
      nlhfSoftmaxResponse_KL_gap_identity_lottery
        (τ := τ) (M := M) (ρ := ρ) (q := q) hρ hν
  have hbrKL :
      KL br ρ =
        nlhfLambda τ * marginValue M br q - Real.log Z := by
    have hsum :=
      nlhfSoftmaxResponse_weighted_log_reference_sum
        (τ := τ) (M := M) (ρ := ρ) (q := q) (ν := br) hρ hbr
    simpa [KL, br, Z] using hsum
  unfold nlhfFirstPayoff
  rw [hgap, hbrKL]
  field_simp [hlam.ne']
  ring

/-- A full-support maximizer of the regularized first-player payoff is the
softmax response. -/
theorem nlhfFirstPayoff_eq_softmaxResponse_of_max
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hp : IsFullSupportLottery p)
    (hmax : ∀ ν : α → ℝ,
      IsFullSupportLottery ν →
        nlhfFirstPayoff τ M ρ ν q ≤ nlhfFirstPayoff τ M ρ p q) :
    p = nlhfSoftmaxResponse τ M ρ q := by
  classical
  let br : α → ℝ := nlhfSoftmaxResponse τ M ρ q
  have hbr : IsFullSupportLottery br :=
    nlhfSoftmaxResponse_fullSupport hρ
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hcoeff : 0 < (1 / nlhfLambda τ) := one_div_pos.mpr hlam
  have hgap :
      nlhfFirstPayoff τ M ρ p q =
        nlhfFirstPayoff τ M ρ br q - (1 / nlhfLambda τ) * KL p br := by
    simpa [br] using
      nlhfFirstPayoff_softmax_gap
        (τ := τ) (M := M) (ρ := ρ) (q := q) (ν := p) hτ hρ hp
  have hKLnonneg : 0 ≤ KL p br :=
    KL_nonneg_of_fullSupport_strictKL hp hbr
  have hp_le_br :
      nlhfFirstPayoff τ M ρ p q ≤ nlhfFirstPayoff τ M ρ br q := by
    rw [hgap]
    nlinarith [mul_nonneg hcoeff.le hKLnonneg]
  have hbr_le_p :
      nlhfFirstPayoff τ M ρ br q ≤ nlhfFirstPayoff τ M ρ p q :=
    hmax br hbr
  have heq :
      nlhfFirstPayoff τ M ρ p q =
        nlhfFirstPayoff τ M ρ br q :=
    le_antisymm hp_le_br hbr_le_p
  have hKLzero : KL p br = 0 := by
    nlinarith [hgap, heq, hcoeff]
  exact (KL_eq_zero_iff_of_fullSupport hp hbr).mp hKLzero

/-- A closed-simplex maximizer of the regularized first-player payoff is the
softmax response, hence automatically has full support. -/
theorem nlhfFirstPayoff_eq_softmaxResponse_of_lottery_max
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hp : IsLottery p)
    (hmax : ∀ ν : α → ℝ,
      IsLottery ν →
        nlhfFirstPayoff τ M ρ ν q ≤ nlhfFirstPayoff τ M ρ p q) :
    p = nlhfSoftmaxResponse τ M ρ q := by
  classical
  let br : α → ℝ := nlhfSoftmaxResponse τ M ρ q
  have hbr : IsFullSupportLottery br :=
    nlhfSoftmaxResponse_fullSupport hρ
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hcoeff : 0 < (1 / nlhfLambda τ) := one_div_pos.mpr hlam
  have hgap :
      nlhfFirstPayoff τ M ρ p q =
        nlhfFirstPayoff τ M ρ br q - (1 / nlhfLambda τ) * KL p br := by
    simpa [br] using
      nlhfFirstPayoff_softmax_gap_lottery
        (τ := τ) (M := M) (ρ := ρ) (q := q) (ν := p) hτ hρ hp
  have hKLnonneg : 0 ≤ KL p br :=
    KL_nonneg_of_lottery_fullSupport hp hbr
  have hp_le_br :
      nlhfFirstPayoff τ M ρ p q ≤ nlhfFirstPayoff τ M ρ br q := by
    rw [hgap]
    nlinarith [mul_nonneg hcoeff.le hKLnonneg]
  have hbr_le_p :
      nlhfFirstPayoff τ M ρ br q ≤ nlhfFirstPayoff τ M ρ p q :=
    hmax br hbr.toLottery
  have heq :
      nlhfFirstPayoff τ M ρ p q =
        nlhfFirstPayoff τ M ρ br q :=
    le_antisymm hp_le_br hbr_le_p
  have hKLzero : KL p br = 0 := by
    nlinarith [hgap, heq, hcoeff]
  exact (KL_eq_zero_iff_of_lottery_fullSupport hp hbr).mp hKLzero

/-- Turning a softmax fixed point into the paper's fixed-point predicate. -/
theorem isNLHFFixedPoint_of_eq_softmaxResponse
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hτ : 0 < τ)
    (hρ : IsFullSupportLottery ρ)
    (hπ : IsFullSupportLottery π)
    (heq : π = nlhfSoftmaxResponse τ M ρ π) :
    IsNLHFFixedPoint τ M ρ π := by
  refine ⟨hτ, hρ, hπ, ?_⟩
  intro x
  simpa [nlhfSoftmaxResponse] using congr_fun heq x

/-- A full-support saddle point of the regularized Sion/Rosen game. -/
def IsNLHFRegularizedSaddle
    {α : Type*} [Fintype α]
    (τ : ℝ) (M : α → α → ℝ) (ρ p q : α → ℝ) : Prop :=
  IsFullSupportLottery p ∧ IsFullSupportLottery q ∧
    (∀ r : α → ℝ,
      IsFullSupportLottery r →
        nlhfSionValue τ M ρ r q ≤ nlhfSionValue τ M ρ p q) ∧
    (∀ s : α → ℝ,
      IsFullSupportLottery s →
        nlhfSionValue τ M ρ p q ≤ nlhfSionValue τ M ρ p s)

/-- A saddle point of the same finite regularized game on the closed simplex.
Sion's minimax theorem naturally gives this closed-simplex statement. -/
def IsNLHFRegularizedClosedSaddle
    {α : Type*} [Fintype α]
    (τ : ℝ) (M : α → α → ℝ) (ρ p q : α → ℝ) : Prop :=
  IsLottery p ∧ IsLottery q ∧
    (∀ r : α → ℝ,
      IsLottery r →
        nlhfSionValue τ M ρ r q ≤ nlhfSionValue τ M ρ p q) ∧
    (∀ s : α → ℝ,
      IsLottery s →
        nlhfSionValue τ M ρ p q ≤ nlhfSionValue τ M ρ p s)

/-- The KL-regularized closed-simplex saddle is automatically an interior
saddle: each coordinate is forced to equal a softmax best response. -/
theorem regularizedSaddle_of_closedSaddle
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hsaddle : IsNLHFRegularizedClosedSaddle τ M ρ p q) :
    IsNLHFRegularizedSaddle τ M ρ p q := by
  classical
  rcases hsaddle with ⟨hp, hq, hleft, hright⟩
  have hmaxp :
      ∀ r : α → ℝ,
        IsLottery r →
          nlhfFirstPayoff τ M ρ r q ≤ nlhfFirstPayoff τ M ρ p q := by
    intro r hr
    have h := hleft r hr
    unfold nlhfSionValue at h
    unfold nlhfFirstPayoff
    linarith
  have hp_soft :
      p = nlhfSoftmaxResponse τ M ρ q :=
    nlhfFirstPayoff_eq_softmaxResponse_of_lottery_max
      hτ hρ hp hmaxp
  have hp_full : IsFullSupportLottery p := by
    rw [hp_soft]
    exact nlhfSoftmaxResponse_fullSupport hρ
  have hmaxq :
      ∀ s : α → ℝ,
        IsLottery s →
          nlhfFirstPayoff τ M ρ s p ≤ nlhfFirstPayoff τ M ρ q p := by
    intro s hs
    have h := hright s hs
    unfold nlhfSionValue at h
    unfold nlhfFirstPayoff
    have hpq : marginValue M p q = -marginValue M q p :=
      marginValue_swap_eq_neg_of_skew p q hM.2.1
    have hps : marginValue M p s = -marginValue M s p :=
      marginValue_swap_eq_neg_of_skew p s hM.2.1
    rw [hpq, hps] at h
    linarith
  have hq_soft :
      q = nlhfSoftmaxResponse τ M ρ p :=
    nlhfFirstPayoff_eq_softmaxResponse_of_lottery_max
      hτ hρ hq hmaxq
  have hq_full : IsFullSupportLottery q := by
    rw [hq_soft]
    exact nlhfSoftmaxResponse_fullSupport hρ
  exact ⟨hp_full, hq_full,
    (fun r hr => hleft r hr.toLottery),
    (fun s hs => hright s hs.toLottery)⟩

/-- A normalized NLHF fixed point is a diagonal full-support saddle point of
the regularized zero-sum game.  This is the converse direction to
`nlhfFixedPoint_of_regularizedSaddle`, and lets paper-facing saddle-pair
existence be reduced to the fixed-point existence interface. -/
theorem regularizedSaddle_of_fixedPoint
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hπ : IsNLHFFixedPoint τ M ρ π) :
    IsNLHFRegularizedSaddle τ M ρ π π := by
  classical
  rcases hπ with ⟨hτ, hρ, hπfull, hfixed⟩
  have hsoft : nlhfSoftmaxResponse τ M ρ π = π := by
    funext x
    exact (hfixed x).symm
  have hself : marginValue M π π = 0 :=
    marginValue_self_eq_zero_of_normalized π hM
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hcoeff_nonneg : 0 ≤ (1 / nlhfLambda τ) :=
    (one_div_pos.mpr hlam).le
  refine ⟨hπfull, hπfull, ?_, ?_⟩
  · intro r hr
    have hgap :
        nlhfFirstPayoff τ M ρ r π =
          nlhfFirstPayoff τ M ρ π π -
            (1 / nlhfLambda τ) * KL r π := by
      simpa [hsoft] using
        nlhfFirstPayoff_softmax_gap
          (τ := τ) (M := M) (ρ := ρ) (q := π) (ν := r)
          hτ hρ hr
    have hKLnonneg : 0 ≤ KL r π :=
      KL_nonneg_of_fullSupport_strictKL hr hπfull
    have hpay :
        nlhfFirstPayoff τ M ρ r π ≤ nlhfFirstPayoff τ M ρ π π := by
      rw [hgap]
      nlinarith [mul_nonneg hcoeff_nonneg hKLnonneg]
    unfold nlhfFirstPayoff at hpay
    unfold nlhfSionValue
    nlinarith
  · intro s hs
    have hgap :
        nlhfFirstPayoff τ M ρ s π =
          nlhfFirstPayoff τ M ρ π π -
            (1 / nlhfLambda τ) * KL s π := by
      simpa [hsoft] using
        nlhfFirstPayoff_softmax_gap
          (τ := τ) (M := M) (ρ := ρ) (q := π) (ν := s)
          hτ hρ hs
    have hKLnonneg : 0 ≤ KL s π :=
      KL_nonneg_of_fullSupport_strictKL hs hπfull
    have hpay :
        nlhfFirstPayoff τ M ρ s π ≤ nlhfFirstPayoff τ M ρ π π := by
      rw [hgap]
      nlinarith [mul_nonneg hcoeff_nonneg hKLnonneg]
    have hswap : marginValue M π s = -marginValue M s π :=
      marginValue_swap_eq_neg_of_skew π s hM.2.1
    unfold nlhfFirstPayoff at hpay
    unfold nlhfSionValue
    rw [hself] at hpay
    rw [hself, hswap]
    nlinarith

/-- A normalized NLHF fixed point is also a diagonal saddle point on the
closed lottery simplex.  The closed-simplex inequalities use the lottery
version of the softmax payoff gap, so fixed-point existence is enough for the
paper's closed-saddle existence statement. -/
theorem regularizedClosedSaddle_of_fixedPoint
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hπ : IsNLHFFixedPoint τ M ρ π) :
    IsNLHFRegularizedClosedSaddle τ M ρ π π := by
  classical
  rcases hπ with ⟨hτ, hρ, hπfull, hfixed⟩
  have hπlot : IsLottery π := hπfull.toLottery
  have hsoft : nlhfSoftmaxResponse τ M ρ π = π := by
    funext x
    exact (hfixed x).symm
  have hself : marginValue M π π = 0 :=
    marginValue_self_eq_zero_of_normalized π hM
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hcoeff_nonneg : 0 ≤ (1 / nlhfLambda τ) :=
    (one_div_pos.mpr hlam).le
  refine ⟨hπlot, hπlot, ?_, ?_⟩
  · intro r hr
    have hgap :
        nlhfFirstPayoff τ M ρ r π =
          nlhfFirstPayoff τ M ρ π π -
            (1 / nlhfLambda τ) * KL r π := by
      simpa [hsoft] using
        nlhfFirstPayoff_softmax_gap_lottery
          (τ := τ) (M := M) (ρ := ρ) (q := π) (ν := r)
          hτ hρ hr
    have hKLnonneg : 0 ≤ KL r π :=
      KL_nonneg_of_lottery_fullSupport hr hπfull
    have hpay :
        nlhfFirstPayoff τ M ρ r π ≤ nlhfFirstPayoff τ M ρ π π := by
      rw [hgap]
      nlinarith [mul_nonneg hcoeff_nonneg hKLnonneg]
    unfold nlhfFirstPayoff at hpay
    unfold nlhfSionValue
    nlinarith
  · intro s hs
    have hgap :
        nlhfFirstPayoff τ M ρ s π =
          nlhfFirstPayoff τ M ρ π π -
            (1 / nlhfLambda τ) * KL s π := by
      simpa [hsoft] using
        nlhfFirstPayoff_softmax_gap_lottery
          (τ := τ) (M := M) (ρ := ρ) (q := π) (ν := s)
          hτ hρ hs
    have hKLnonneg : 0 ≤ KL s π :=
      KL_nonneg_of_lottery_fullSupport hs hπfull
    have hpay :
        nlhfFirstPayoff τ M ρ s π ≤ nlhfFirstPayoff τ M ρ π π := by
      rw [hgap]
      nlinarith [mul_nonneg hcoeff_nonneg hKLnonneg]
    have hswap : marginValue M π s = -marginValue M s π :=
      marginValue_swap_eq_neg_of_skew π s hM.2.1
    unfold nlhfFirstPayoff at hpay
    unfold nlhfSionValue
    rw [hself] at hpay
    rw [hself, hswap]
    nlinarith

/-- The finite Sion/Rosen saddle-existence input, stated at the game level
rather than directly as fixed-point existence.  This is the theorem that Sion
3.4 supplies in the finite compact convex setting, with the strict KL term
placing the saddle in full support. -/
def SionStrictKLSaddleExistence
    {α : Type*} [Fintype α] : Prop :=
  ∀ {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ},
    0 < τ →
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ →
          ∃ p q : α → ℝ, IsNLHFRegularizedSaddle τ M ρ p q

/-- Fixed-point existence is already enough to obtain the paper-facing
regularized saddle-pair existence statement: the fixed point is a diagonal
saddle by `regularizedSaddle_of_fixedPoint`. -/
theorem sionStrictKLSaddleExistence_of_fixedPointExistence
    {α : Type*} [Fintype α]
    (hexists : SionStrictKLFixedPointExistence (α := α)) :
    SionStrictKLSaddleExistence (α := α) := by
  intro τ M ρ hτ hM hρ
  rcases hexists hτ hM hρ with ⟨π, hπ⟩
  exact ⟨π, π, regularizedSaddle_of_fixedPoint hM hπ⟩

/-- Closed-simplex saddle existence, the direct finite-dimensional corollary
of Sion's minimax theorem needed here.  The interior/full-support conclusion
is proved separately in `regularizedSaddle_of_closedSaddle`. -/
def SionClosedSaddleExistence
    {α : Type*} [Fintype α] : Prop :=
  ∀ {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ},
    0 < τ →
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ →
          ∃ p q : α → ℝ, IsNLHFRegularizedClosedSaddle τ M ρ p q

/-- The exact closed-simplex saddle-existence theorem needed by finite NLHF.

This applies `Sion.exists_isSaddlePointOn` with the minimizing variable equal
to the second lottery and the maximizing variable equal to the first lottery.
The required compact convex set is the finite lottery simplex.  Continuity at
its boundary and convexity of KL are supplied through Mathlib's continuous,
convex `InformationTheory.klFun`.  Mathlib's Sion proof follows Komiya (1988);
see the module-level citations above. -/
theorem sionClosedSaddleExistence
    {α : Type*} [Fintype α] :
    SionClosedSaddleExistence (α := α) := by
  intro τ M ρ hτ hM hρ
  let L : Set (α → ℝ) := {p : α → ℝ | IsLottery p}
  let f : (α → ℝ) → (α → ℝ) → ℝ :=
    fun q p => nlhfSionValue τ M ρ p q
  have hLne : L.Nonempty := ⟨ρ, hρ.toLottery⟩
  have hLconv : Convex ℝ L := convex_setOf_isLottery
  have hLcompact : IsCompact L := isCompact_setOf_isLottery
  have hlam : 0 < nlhfLambda τ := by
    unfold nlhfLambda
    positivity
  have hc : 0 ≤ (1 / nlhfLambda τ) := (one_div_pos.mpr hlam).le
  have hKLcont : ContinuousOn (fun p : α → ℝ => KL p ρ) L := by
    simpa [L] using continuousOn_KL_lottery hρ
  have hKLconv : ConvexOn ℝ L (fun p : α → ℝ => KL p ρ) := by
    simpa [L] using convexOn_KL_lottery hρ
  have hfy : ∀ p ∈ L,
      LowerSemicontinuousOn (fun q : α → ℝ => f q p) L := by
    intro p hp
    have hcont : ContinuousOn (fun q : α → ℝ => f q p) L := by
      have hm : ContinuousOn (fun q : α → ℝ => marginValue M p q) L :=
        (continuous_marginValue_right M p).continuousOn
      have hk : ContinuousOn
          (fun q : α → ℝ => (1 / nlhfLambda τ) * KL q ρ) L :=
        hKLcont.const_mul (1 / nlhfLambda τ)
      simpa [f, nlhfSionValue] using
        (hm.add continuousOn_const).add hk
    exact hcont.lowerSemicontinuousOn
  have hfy' : ∀ p ∈ L,
      QuasiconvexOn ℝ L (fun q : α → ℝ => f q p) := by
    intro p hp
    have hm := convexOn_marginValue_right M p
    have hk := hKLconv.smul hc
    have hconv : ConvexOn ℝ L (fun q : α → ℝ => f q p) := by
      simpa [f, nlhfSionValue, smul_eq_mul] using
        (hm.add (convexOn_const _ hLconv)).add hk
    exact hconv.quasiconvexOn
  have hfx : ∀ q ∈ L,
      UpperSemicontinuousOn (fun p : α → ℝ => f q p) L := by
    intro q hq
    have hcont : ContinuousOn (fun p : α → ℝ => f q p) L := by
      have hm : ContinuousOn (fun p : α → ℝ => marginValue M p q) L :=
        (continuous_marginValue_left M q).continuousOn
      have hk : ContinuousOn
          (fun p : α → ℝ => (1 / nlhfLambda τ) * KL p ρ) L :=
        hKLcont.const_mul (1 / nlhfLambda τ)
      simpa [f, nlhfSionValue] using
        (hm.sub hk).add continuousOn_const
    exact hcont.upperSemicontinuousOn
  have hfx' : ∀ q ∈ L,
      QuasiconcaveOn ℝ L (fun p : α → ℝ => f q p) := by
    intro q hq
    have hm := concaveOn_marginValue_left M q
    have hk := hKLconv.smul hc
    have hconc : ConcaveOn ℝ L (fun p : α → ℝ => f q p) := by
      simpa [f, nlhfSionValue, smul_eq_mul] using
        (hm.sub hk).add (concaveOn_const _ hLconv)
    exact hconc.quasiconcaveOn
  rcases Sion.exists_isSaddlePointOn hLne hLconv hLcompact
      hfy hfy' hLconv hLne hLcompact hfx hfx' with
    ⟨q, hq, p, hp, hsaddle⟩
  refine ⟨p, q, hp, hq, ?_, ?_⟩
  · intro r hr
    exact hsaddle q hq r hr
  · intro s hs
    exact hsaddle s hs p hp

/-- The closed-simplex Sion theorem yields the full-support saddle interface
used by the fixed-point construction. -/
theorem sionStrictKLSaddleExistence_of_closedSion
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α)) :
    SionStrictKLSaddleExistence (α := α) := by
  intro τ M ρ hτ hM hρ
  rcases hsion hτ hM hρ with ⟨p, q, hsaddle⟩
  exact ⟨p, q, regularizedSaddle_of_closedSaddle hτ hM hρ hsaddle⟩

/-- A Sion/Rosen saddle point gives an NLHF fixed point. -/
theorem nlhfFixedPoint_of_regularizedSaddle
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hsaddle : IsNLHFRegularizedSaddle τ M ρ p q) :
    IsNLHFFixedPoint τ M ρ q := by
  classical
  rcases hsaddle with ⟨hp, hq, hleft, hright⟩
  have hpq_nonneg :
      0 ≤ nlhfSionValue τ M ρ p q := by
    have h := hleft q hq
    have hqq : nlhfSionValue τ M ρ q q = 0 := by
      unfold nlhfSionValue
      rw [marginValue_self_eq_zero_of_normalized q hM]
      ring
    linarith
  have hpq_nonpos :
      nlhfSionValue τ M ρ p q ≤ 0 := by
    have h := hright p hp
    have hpp : nlhfSionValue τ M ρ p p = 0 := by
      unfold nlhfSionValue
      rw [marginValue_self_eq_zero_of_normalized p hM]
      ring
    linarith
  have hpq_zero :
      nlhfSionValue τ M ρ p q = 0 :=
    le_antisymm hpq_nonpos hpq_nonneg
  have hqq_zero : nlhfSionValue τ M ρ q q = 0 := by
    unfold nlhfSionValue
    rw [marginValue_self_eq_zero_of_normalized q hM]
    ring
  have hmax_q :
      ∀ r : α → ℝ,
        IsFullSupportLottery r →
          nlhfFirstPayoff τ M ρ r q ≤ nlhfFirstPayoff τ M ρ q q := by
    intro r hr
    have hval : nlhfSionValue τ M ρ r q ≤ nlhfSionValue τ M ρ q q := by
      have h := hleft r hr
      linarith
    unfold nlhfSionValue at hval
    unfold nlhfFirstPayoff
    linarith
  have hq_soft :
      q = nlhfSoftmaxResponse τ M ρ q :=
    nlhfFirstPayoff_eq_softmaxResponse_of_max
      hτ hρ hq hmax_q
  exact isNLHFFixedPoint_of_eq_softmaxResponse hτ hρ hq hq_soft

/-- In any full-support regularized saddle pair, the two players' lotteries
coincide.  This is the paper's `π_τ = π'_τ` conclusion in Proposition
`nlhf-existence`, proved by combining the saddle optimality of the first
coordinate with the fixed-point equation for the second coordinate. -/
theorem regularizedSaddle_left_eq_right
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hsaddle : IsNLHFRegularizedSaddle τ M ρ p q) :
    p = q := by
  classical
  rcases hsaddle with ⟨hp, hq, hleft, hright⟩
  have hqfp :
      IsNLHFFixedPoint τ M ρ q :=
    nlhfFixedPoint_of_regularizedSaddle hτ hM hρ
      ⟨hp, hq, hleft, hright⟩
  have hmaxp :
      ∀ r : α → ℝ,
        IsFullSupportLottery r →
          nlhfFirstPayoff τ M ρ r q ≤ nlhfFirstPayoff τ M ρ p q := by
    intro r hr
    have h := hleft r hr
    unfold nlhfSionValue at h
    unfold nlhfFirstPayoff
    linarith
  have hp_soft :
      p = nlhfSoftmaxResponse τ M ρ q :=
    nlhfFirstPayoff_eq_softmaxResponse_of_max hτ hρ hp hmaxp
  have hq_soft :
      q = nlhfSoftmaxResponse τ M ρ q := by
    funext x
    exact hqfp.2.2.2 x
  exact hp_soft.trans hq_soft.symm

/-- A full-support regularized saddle pair is exactly a diagonal pair whose
common coordinate is the NLHF fixed point. -/
theorem regularizedSaddle_diagonal_fixedPoint
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hsaddle : IsNLHFRegularizedSaddle τ M ρ p q) :
    p = q ∧ IsNLHFFixedPoint τ M ρ q := by
  exact ⟨regularizedSaddle_left_eq_right hτ hM hρ hsaddle,
    nlhfFixedPoint_of_regularizedSaddle hτ hM hρ hsaddle⟩

/-- A closed-simplex regularized saddle pair is diagonal.  The KL regularizer
forces the closed-saddle coordinates into full support first, so this is the
closed-simplex version of the paper's `π_τ = π'_τ` conclusion. -/
theorem regularizedClosedSaddle_left_eq_right
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hsaddle : IsNLHFRegularizedClosedSaddle τ M ρ p q) :
    p = q :=
  regularizedSaddle_left_eq_right hτ hM hρ
    (regularizedSaddle_of_closedSaddle hτ hM hρ hsaddle)

/-- A closed-simplex regularized saddle pair is exactly a diagonal pair whose
common coordinate is the NLHF fixed point. -/
theorem regularizedClosedSaddle_diagonal_fixedPoint
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ p q : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hsaddle : IsNLHFRegularizedClosedSaddle τ M ρ p q) :
    p = q ∧ IsNLHFFixedPoint τ M ρ q :=
  regularizedSaddle_diagonal_fixedPoint hτ hM hρ
    (regularizedSaddle_of_closedSaddle hτ hM hρ hsaddle)

/-- The finite Sion/Rosen saddle theorem supplies the fixed-point existence
interface used by the rest of the project. -/
theorem fixedPointExistence_of_sionStrictKLSaddle
    {α : Type*} [Fintype α]
    (hsion : SionStrictKLSaddleExistence (α := α)) :
    SionStrictKLFixedPointExistence (α := α) := by
  intro τ M ρ hτ hM hρ
  rcases hsion hτ hM hρ with ⟨p, q, hsaddle⟩
  exact ⟨q, nlhfFixedPoint_of_regularizedSaddle hτ hM hρ hsaddle⟩

/-- The direct closed-simplex Sion input supplies finite NLHF fixed-point
existence. -/
theorem fixedPointExistence_of_closedSion
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α)) :
    SionStrictKLFixedPointExistence (α := α) :=
  fixedPointExistence_of_sionStrictKLSaddle
    (sionStrictKLSaddleExistence_of_closedSion hsion)

/-- Closed-simplex Sion existence plus strict-KL uniqueness gives the exact
existence-and-uniqueness theorem for NLHF fixed points. -/
theorem exists_unique_nlhfFixedPoint_of_closedSion
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ, IsNLHFFixedPoint τ M ρ π :=
  exists_unique_nlhfFixedPoint_of_sionStrictKL
    (fixedPointExistence_of_closedSion hsion) hτ hM hρ

/-- Proposition `nlhf-existence`, in the paper's saddle-pair form, conditional
on the full-support Sion/Rosen saddle-existence interface.  The proof is
existence from the interface plus uniqueness from diagonalization and strict-KL
fixed-point uniqueness. -/
theorem exists_unique_nlhfRegularizedSaddlePair_of_sionStrictKLSaddle
    {α : Type*} [Fintype α]
    (hsion : SionStrictKLSaddleExistence (α := α))
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedSaddle τ M ρ pq.1 pq.2 := by
  rcases hsion hτ hM hρ with ⟨p, q, hsaddle⟩
  refine ⟨(p, q), hsaddle, ?_⟩
  intro pq hpq
  rcases pq with ⟨p', q'⟩
  rcases regularizedSaddle_diagonal_fixedPoint hτ hM hρ hsaddle with
    ⟨hp_eq_q, hqfp⟩
  rcases regularizedSaddle_diagonal_fixedPoint hτ hM hρ hpq with
    ⟨hp'_eq_q', hq'fp⟩
  have hq'eq : q' = q :=
    nlhfFixedPoint_unique_of_normalized hM hq'fp hqfp
  have hp'_eq_q'_plain : p' = q' := by
    simpa using hp'_eq_q'
  have hp'eq : p' = p := by
    rw [hp'_eq_q'_plain, hq'eq, ← hp_eq_q]
  simp [hp'eq, hq'eq]

/-- Fixed-point existence plus strict-KL uniqueness gives the paper-facing
unique regularized saddle pair by placing the fixed point on the diagonal. -/
theorem exists_unique_nlhfRegularizedSaddlePair_of_sionStrictKLFixedPoint
    {α : Type*} [Fintype α]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedSaddle τ M ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedSaddlePair_of_sionStrictKLSaddle
    (sionStrictKLSaddleExistence_of_fixedPointExistence hexists) hτ hM hρ

/-- Proposition `nlhf-existence`, in the paper's saddle-pair form, conditional
on the closed-simplex Sion existence input: there is a unique regularized
saddle pair, and by `regularizedSaddle_left_eq_right` its two coordinates
coincide. -/
theorem exists_unique_nlhfRegularizedSaddlePair_of_closedSion
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedSaddle τ M ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedSaddlePair_of_sionStrictKLSaddle
    (sionStrictKLSaddleExistence_of_closedSion hsion) hτ hM hρ

/-- Proposition `nlhf-existence`, in the paper's closed-simplex saddle-pair
form: the closed-simplex saddle pair supplied by Sion is unique.  The diagonal
conclusion is `regularizedClosedSaddle_left_eq_right`. -/
theorem exists_unique_nlhfRegularizedClosedSaddlePair_of_closedSion
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedClosedSaddle τ M ρ pq.1 pq.2 := by
  rcases hsion hτ hM hρ with ⟨p, q, hsaddle⟩
  refine ⟨(p, q), hsaddle, ?_⟩
  intro pq hpq
  rcases pq with ⟨p', q'⟩
  rcases regularizedClosedSaddle_diagonal_fixedPoint hτ hM hρ hsaddle with
    ⟨hp_eq_q, hqfp⟩
  rcases regularizedClosedSaddle_diagonal_fixedPoint hτ hM hρ hpq with
    ⟨hp'_eq_q', hq'fp⟩
  have hq'eq : q' = q :=
    nlhfFixedPoint_unique_of_normalized hM hq'fp hqfp
  have hp'_eq_q'_plain : p' = q' := by
    simpa using hp'_eq_q'
  have hp'eq : p' = p := by
    rw [hp'_eq_q'_plain, hq'eq, ← hp_eq_q]
  simp [hp'eq, hq'eq]

/-- A concrete selected NLHF rule obtained by choosing the fixed point supplied
by the Sion/Rosen existence theorem.  On invalid inputs the fallback value is
irrelevant; all paper-facing theorems use the valid-input selection theorem
below. -/
noncomputable def selectedNLHFOfSionStrictKL
    {α : Type*} [Fintype α]
    (hexists : SionStrictKLFixedPointExistence (α := α)) :
    ℝ → MatrixRule α := by
  classical
  exact fun τ M ρ =>
    if hτ : 0 < τ then
      if hM : IsNormalizedMarginMatrix M then
        if hρ : IsFullSupportLottery ρ then
          Classical.choose (hexists hτ hM hρ)
        else
          ρ
      else
        ρ
    else
      ρ

/-- The chosen Sion/Rosen fixed point is a fixed-point selection in the
interface used by the monotonicity formalization. -/
theorem selectedNLHFOfSionStrictKL_selection
    {α : Type*} [Fintype α]
    (hexists : SionStrictKLFixedPointExistence (α := α)) :
    IsNLHFFixedPointSelection (selectedNLHFOfSionStrictKL hexists) := by
  intro τ M ρ hτ hM hρ
  unfold selectedNLHFOfSionStrictKL
  rw [dif_pos hτ, dif_pos hM, dif_pos hρ]
  exact Classical.choose_spec (hexists hτ hM hρ)

/-- The chosen Sion/Rosen fixed point is the unique normalized fixed point. -/
theorem selectedNLHFOfSionStrictKL_eq_of_fixedPoint
    {α : Type*} [Fintype α]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hπ : IsNLHFFixedPoint τ M ρ π) :
    selectedNLHFOfSionStrictKL hexists τ M ρ = π := by
  have hsel :
      IsNLHFFixedPoint τ M ρ
        (selectedNLHFOfSionStrictKL hexists τ M ρ) :=
    selectedNLHFOfSionStrictKL_selection hexists hπ.1 hM hπ.2.1
  exact nlhfFixedPoint_unique_of_normalized hM hsel hπ

/-- The selected Sion/Rosen fixed-point rule is the NLHF selector on the
paper's normalized-margin domain. -/
theorem selectedNLHFOfSionStrictKL_isTheNLHF
    {α : Type*} [Fintype α]
    (hexists : SionStrictKLFixedPointExistence (α := α)) :
    IsTheNLHF (selectedNLHFOfSionStrictKL hexists) := by
  intro τ M ρ π hM hπ
  exact selectedNLHFOfSionStrictKL_eq_of_fixedPoint hexists hM hπ

/-- The paper-facing selected NLHF rule, obtained from the proved
closed-simplex Sion saddle theorem. -/
noncomputable def selectedNLHF
    {α : Type*} [Fintype α] : ℝ → MatrixRule α :=
  selectedNLHFOfSionStrictKL
    (fixedPointExistence_of_closedSion sionClosedSaddleExistence)

/-- The selected NLHF rule satisfies the fixed-point selection interface. -/
theorem selectedNLHF_selection
    {α : Type*} [Fintype α] :
    IsNLHFFixedPointSelection (selectedNLHF (α := α)) :=
  selectedNLHFOfSionStrictKL_selection
    (fixedPointExistence_of_closedSion sionClosedSaddleExistence)

/-- The selected NLHF rule is the unique normalized fixed point. -/
theorem selectedNLHF_eq_of_fixedPoint
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hπ : IsNLHFFixedPoint τ M ρ π) :
    selectedNLHF (α := α) τ M ρ = π :=
  selectedNLHFOfSionStrictKL_eq_of_fixedPoint
    (fixedPointExistence_of_closedSion sionClosedSaddleExistence) hM hπ

/-- The selected NLHF rule is the NLHF selector on normalized margin
functions. -/
theorem selectedNLHF_isTheNLHF
    {α : Type*} [Fintype α] :
    IsTheNLHF (selectedNLHF (α := α)) :=
  selectedNLHFOfSionStrictKL_isTheNLHF
    (fixedPointExistence_of_closedSion sionClosedSaddleExistence)

/-- Existence and uniqueness of the finite NLHF fixed point, from the proved
closed-simplex Sion saddle theorem. -/
theorem exists_unique_nlhfFixedPoint
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ, IsNLHFFixedPoint τ M ρ π :=
  exists_unique_nlhfFixedPoint_of_closedSion
    sionClosedSaddleExistence hτ hM hρ

/-- Existence and uniqueness of the full-support regularized NLHF saddle pair,
from the proved closed-simplex Sion saddle theorem. -/
theorem exists_unique_nlhfRegularizedSaddlePair
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedSaddle τ M ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedSaddlePair_of_closedSion
    sionClosedSaddleExistence hτ hM hρ

/-- Existence and uniqueness of the closed-simplex regularized NLHF saddle
pair, from the proved closed-simplex Sion saddle theorem. -/
theorem exists_unique_nlhfRegularizedClosedSaddlePair
    {α : Type*} [Fintype α]
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedClosedSaddle τ M ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedClosedSaddlePair_of_closedSion
    sionClosedSaddleExistence hτ hM hρ

/-- The selected NLHF rule obtained directly from the closed-simplex Sion
saddle-existence theorem. -/
noncomputable def selectedNLHFOfClosedSion
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α)) :
    ℝ → MatrixRule α :=
  selectedNLHFOfSionStrictKL (fixedPointExistence_of_closedSion hsion)

/-- The closed-Sion selected NLHF rule satisfies the fixed-point selection
interface. -/
theorem selectedNLHFOfClosedSion_selection
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α)) :
    IsNLHFFixedPointSelection (selectedNLHFOfClosedSion hsion) :=
  selectedNLHFOfSionStrictKL_selection (fixedPointExistence_of_closedSion hsion)

/-- The closed-Sion selected NLHF rule is the unique normalized fixed point. -/
theorem selectedNLHFOfClosedSion_eq_of_fixedPoint
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hπ : IsNLHFFixedPoint τ M ρ π) :
    selectedNLHFOfClosedSion hsion τ M ρ = π :=
  selectedNLHFOfSionStrictKL_eq_of_fixedPoint
    (fixedPointExistence_of_closedSion hsion) hM hπ

/-- The closed-Sion selected NLHF rule is the NLHF selector on normalized
margin functions. -/
theorem selectedNLHFOfClosedSion_isTheNLHF
    {α : Type*} [Fintype α]
    (hsion : SionClosedSaddleExistence (α := α)) :
    IsTheNLHF (selectedNLHFOfClosedSion hsion) :=
  selectedNLHFOfSionStrictKL_isTheNLHF
    (fixedPointExistence_of_closedSion hsion)

end PaperFormalization
