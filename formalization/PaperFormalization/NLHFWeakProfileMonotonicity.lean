import PaperFormalization.WeakProfileMargin
import PaperFormalization.NLHFSelectedMonotonicity

open scoped BigOperators Topology
open Filter

namespace PaperFormalization

/-! # The all-profiles clause of Theorem `NLHFmono`, at the profile level

`SelectedNLHFAllProfileMonotonicity` states the `3/8` clause over normalized
margin *matrices*.  The predicate below states it over *actual finite
profiles* of reflexive binary relations, read through the paper's
pair-normalized margin `m̄` and improved in the paper's exact sense
(conditions (i)–(iii) of the probabilistic-monotonicity definition).

The positive direction is Lemma `profile-margin-reduction`
(`paperNormalizedMargin_improvement_of_weakProfileImprovement`) composed with
the matrix-level theorem, whose proof already performs the paper's
decomposition of a margin improvement into one-pair improvements. -/

/-- Probabilistic monotonicity of selected NLHF over all finite profiles of
reflexive binary relations, with the paper's pair-normalized margins and the
paper's improvement conditions (i)–(iii). -/
def SelectedNLHFWeakProfileAllMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Fintype α] [DecidableEq α],
    ∀ (R R' : V → α → α → Bool) (ρ : α → ℝ) (x : α),
      IsFullSupportLottery ρ →
        IsWeakProfileImprovement R R' x →
          selectedNLHF (α := α) τ (paperNormalizedMargin R) ρ x ≤
            selectedNLHF (α := α) τ (paperNormalizedMargin R') ρ x

/-- Pointwise profile-level `3/8` monotonicity for selected NLHF. -/
theorem selectedNLHF_weakProfile_largeTau_monotone
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {τ : ℝ} (hτge : (3 : ℝ) / 8 ≤ τ)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (h : IsWeakProfileImprovement R R' x) :
    selectedNLHF (α := α) τ (paperNormalizedMargin R) ρ x ≤
      selectedNLHF (α := α) τ (paperNormalizedMargin R') ρ x :=
  (selectedNLHF_largeTau_monotone (α := α)) τ hτge
    (paperNormalizedMargin R) (paperNormalizedMargin R') ρ x
    (paperNormalizedMargin_isNormalizedMarginMatrix R)
    (paperNormalizedMargin_isNormalizedMarginMatrix R')
    hρ (paperNormalizedMargin_improvement_of_weakProfileImprovement h)

/-- The positive half of the profile-level `3/8` clause. -/
theorem selectedNLHF_weakProfileAllMonotone_of_tau_ge_three_eighths
    {τ : ℝ} (hτge : (3 : ℝ) / 8 ≤ τ) :
    SelectedNLHFWeakProfileAllMonotonicity τ := by
  intro V α _fintypeV _fintypeα _decidableα R R' ρ x hρ h
  exact selectedNLHF_weakProfile_largeTau_monotone hτge hρ h


/-! ## The paper's transitive-profile sharpness construction

`paper/main.tex` realizes the all-profiles counterexample matrix by an
electorate that is partitioned into three pair-groups: `K` voters compare only
`x` and `y`, `K` voters compare only `x` and `z` (all ranking `z` above `x`),
and `K` voters compare only `y` and `z` (all ranking `y` above `z`).  Every
voter's relation is reflexive and transitive, but no voter compares all three
candidates, so the pair-specific normalization `t_{x,y}` allows the
cyclic-margin expression `m(x,y) + m(y,z) - m(x,z)` to exceed the weak-order
bound of `1`.

Improving `x` moves one `x`-versus-`y` voter from `y ≻ x` to `x ≻ y`, which is
exactly a change of the threshold `j` to `j + 1` below. -/

/-- Ballot expressing only `x ≻ y` (candidates `x = 0`, `y = 1`, `z = 2`). -/
def ballotXY : Fin 3 → Fin 3 → Bool := fun a b => (a == b) || (a == 0 && b == 1)

/-- Ballot expressing only `y ≻ x`. -/
def ballotYX : Fin 3 → Fin 3 → Bool := fun a b => (a == b) || (a == 1 && b == 0)

/-- Ballot expressing only `z ≻ x`. -/
def ballotZX : Fin 3 → Fin 3 → Bool := fun a b => (a == b) || (a == 2 && b == 0)

/-- Ballot expressing only `y ≻ z`. -/
def ballotYZ : Fin 3 → Fin 3 → Bool := fun a b => (a == b) || (a == 1 && b == 2)

/-- Ballotwise form of the paper's improvement conditions (i)–(iii) at
`x = 0`. -/
def BallotImproves (p p' : Fin 3 → Fin 3 → Bool) : Prop :=
  (∀ y : Fin 3, y ≠ 0 → p 0 y = true → p' 0 y = true) ∧
    (∀ y : Fin 3, y ≠ 0 → p y 0 = false → p' y 0 = false) ∧
      ∀ y z : Fin 3, y ≠ 0 → z ≠ 0 → p' y z = p y z

lemma weakProfileImprovement_of_ballotwise {V : Type*}
    {R R' : V → Fin 3 → Fin 3 → Bool}
    (h : ∀ i, BallotImproves (R i) (R' i)) :
    IsWeakProfileImprovement R R' (0 : Fin 3) :=
  ⟨fun i y hy => (h i).1 y hy, fun i y hy => (h i).2.1 y hy,
    fun i y z hy hz => (h i).2.2 y z hy hz⟩

lemma ballotXY_improves_self : BallotImproves ballotXY ballotXY := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

lemma ballotYX_improves_self : BallotImproves ballotYX ballotYX := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

lemma ballotZX_improves_self : BallotImproves ballotZX ballotZX := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

lemma ballotYZ_improves_self : BallotImproves ballotYZ ballotYZ := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Moving one voter from the ballot `y ≻ x` to the ballot `x ≻ y` is exactly
an improvement of `x` in the paper's sense. -/
lemma ballotYX_improves_ballotXY : BallotImproves ballotYX ballotXY := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The paper's transitive electorate: `K` voters per pair-group, of which the
first `j` in the `x`-versus-`y` group rank `x` above `y`. -/
def nlhfSharpAllWeakProfile3 (K j : ℕ) :
    Sum (Fin K) (Sum (Fin K) (Fin K)) → Fin 3 → Fin 3 → Bool
  | Sum.inl u => if (u : ℕ) < j then ballotXY else ballotYX
  | Sum.inr (Sum.inl _) => ballotZX
  | Sum.inr (Sum.inr _) => ballotYZ

lemma nlhfSharpAllWeakProfile3_reflexive (K j : ℕ) :
    IsReflexiveProfile (nlhfSharpAllWeakProfile3 K j) := by
  rintro (u | u | u) a
  · by_cases h : (u : ℕ) < j
    · simp only [nlhfSharpAllWeakProfile3, if_pos h]
      revert a
      decide
    · simp only [nlhfSharpAllWeakProfile3, if_neg h]
      revert a
      decide
  · simp only [nlhfSharpAllWeakProfile3]
    revert a
    decide
  · simp only [nlhfSharpAllWeakProfile3]
    revert a
    decide

lemma nlhfSharpAllWeakProfile3_transitive (K j : ℕ) :
    IsTransitiveProfile (nlhfSharpAllWeakProfile3 K j) := by
  rintro (u | u | u) a b c
  · by_cases h : (u : ℕ) < j
    · simp only [nlhfSharpAllWeakProfile3, if_pos h]
      revert a b c
      decide
    · simp only [nlhfSharpAllWeakProfile3, if_neg h]
      revert a b c
      decide
  · simp only [nlhfSharpAllWeakProfile3]
    revert a b c
    decide
  · simp only [nlhfSharpAllWeakProfile3]
    revert a b c
    decide

/-- Raising the threshold by one flips exactly one `y ≻ x` voter to `x ≻ y`,
which satisfies the paper's improvement conditions (i)–(iii) for `x = 0`. -/
lemma nlhfSharpAllWeakProfile3_improvement (K j : ℕ) :
    IsWeakProfileImprovement (nlhfSharpAllWeakProfile3 K j)
      (nlhfSharpAllWeakProfile3 K (j + 1)) (0 : Fin 3) := by
  refine weakProfileImprovement_of_ballotwise ?_
  rintro (u | u | u)
  · by_cases h1 : (u : ℕ) < j
    · have h2 : (u : ℕ) < j + 1 := by omega
      simp only [nlhfSharpAllWeakProfile3, if_pos h1, if_pos h2]
      exact ballotXY_improves_self
    · by_cases h2 : (u : ℕ) < j + 1
      · simp only [nlhfSharpAllWeakProfile3, if_neg h1, if_pos h2]
        exact ballotYX_improves_ballotXY
      · simp only [nlhfSharpAllWeakProfile3, if_neg h1, if_neg h2]
        exact ballotYX_improves_self
  · simp only [nlhfSharpAllWeakProfile3]
    exact ballotZX_improves_self
  · simp only [nlhfSharpAllWeakProfile3]
    exact ballotYZ_improves_self

/-! ### Counting -/

lemma card_filter_fin_lt (K j : ℕ) (hj : j ≤ K) :
    (Finset.univ.filter (fun u : Fin K => (u : ℕ) < j)).card = j := by
  classical
  have himg :
      Finset.image (fun u : Fin K => (u : ℕ))
          (Finset.univ.filter (fun u : Fin K => (u : ℕ) < j)) =
        Finset.range j := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨u, hu, rfl⟩
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hu).2
    · intro hn
      have hn' : n < j := Finset.mem_range.mp hn
      refine Finset.mem_image.mpr ⟨⟨n, lt_of_lt_of_le hn' hj⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn'⟩
  have hinj :
      Set.InjOn (fun u : Fin K => (u : ℕ))
        ↑(Finset.univ.filter (fun u : Fin K => (u : ℕ) < j)) := by
    intro a _ha b _hb hab
    exact Fin.val_injective hab
  rw [← Finset.card_image_of_injOn hinj, himg, Finset.card_range]

lemma sum_fin_ite_lt (K j : ℕ) (hj : j ≤ K) (A B : ℝ) :
    Finset.univ.sum (fun u : Fin K => if (u : ℕ) < j then A else B) =
      (j : ℝ) * A + ((K : ℝ) - (j : ℝ)) * B := by
  classical
  have hrw : ∀ u : Fin K,
      (if (u : ℕ) < j then A else B) =
        B + (if (u : ℕ) < j then A - B else 0) := by
    intro u
    by_cases h : (u : ℕ) < j <;> simp [h]
  rw [Finset.sum_congr rfl (fun u _ => hrw u), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_filter, Finset.sum_const, card_filter_fin_lt K j hj,
    nsmul_eq_mul]
  ring

/-- Every voterwise quantity on the paper's transitive electorate splits into
the four ballot blocks. -/
lemma nlhfSharpAllWeakProfile3_sum (K j : ℕ) (hj : j ≤ K)
    (f : (Fin 3 → Fin 3 → Bool) → ℝ) :
    Finset.univ.sum (fun u : Sum (Fin K) (Sum (Fin K) (Fin K)) =>
        f (nlhfSharpAllWeakProfile3 K j u)) =
      ((j : ℝ) * f ballotXY + ((K : ℝ) - (j : ℝ)) * f ballotYX) +
        ((K : ℝ) * f ballotZX + (K : ℝ) * f ballotYZ) := by
  classical
  have hleft :
      Finset.univ.sum (fun u : Fin K =>
          f (nlhfSharpAllWeakProfile3 K j (Sum.inl u))) =
        (j : ℝ) * f ballotXY + ((K : ℝ) - (j : ℝ)) * f ballotYX := by
    have hstep : ∀ u : Fin K,
        f (nlhfSharpAllWeakProfile3 K j (Sum.inl u)) =
          if (u : ℕ) < j then f ballotXY else f ballotYX := by
      intro u
      by_cases h : (u : ℕ) < j
      · simp only [nlhfSharpAllWeakProfile3, if_pos h]
      · simp only [nlhfSharpAllWeakProfile3, if_neg h]
    rw [Finset.sum_congr rfl (fun u _ => hstep u), sum_fin_ite_lt K j hj]
  have hmid :
      Finset.univ.sum (fun u : Fin K =>
          f (nlhfSharpAllWeakProfile3 K j (Sum.inr (Sum.inl u)))) =
        (K : ℝ) * f ballotZX := by
    simp only [nlhfSharpAllWeakProfile3, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hright :
      Finset.univ.sum (fun u : Fin K =>
          f (nlhfSharpAllWeakProfile3 K j (Sum.inr (Sum.inr u)))) =
        (K : ℝ) * f ballotYZ := by
    simp only [nlhfSharpAllWeakProfile3, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, hleft, hmid, hright]

lemma nlhfSharpAllWeakProfile3_strictPrefCount (K j : ℕ) (hj : j ≤ K)
    (a b : Fin 3) :
    strictPrefCount (nlhfSharpAllWeakProfile3 K j) a b =
      ((j : ℝ) * prefIndicator (strictPrefRel ballotXY a b) +
          ((K : ℝ) - (j : ℝ)) * prefIndicator (strictPrefRel ballotYX a b)) +
        ((K : ℝ) * prefIndicator (strictPrefRel ballotZX a b) +
          (K : ℝ) * prefIndicator (strictPrefRel ballotYZ a b)) := by
  unfold strictPrefCount
  exact nlhfSharpAllWeakProfile3_sum K j hj
    (fun p => prefIndicator (strictPrefRel p a b))

lemma nlhfSharpAllWeakProfile3_indiffCount (K j : ℕ) (hj : j ≤ K)
    (a b : Fin 3) :
    indiffCount (nlhfSharpAllWeakProfile3 K j) a b =
      ((j : ℝ) * prefIndicator (indiffRel ballotXY a b) +
          ((K : ℝ) - (j : ℝ)) * prefIndicator (indiffRel ballotYX a b)) +
        ((K : ℝ) * prefIndicator (indiffRel ballotZX a b) +
          (K : ℝ) * prefIndicator (indiffRel ballotYZ a b)) := by
  unfold indiffCount
  exact nlhfSharpAllWeakProfile3_sum K j hj
    (fun p => prefIndicator (indiffRel p a b))

/-! ### The nine margin entries -/

lemma indiffRel_ballotXY_ne (a b : Fin 3) (hab : a ≠ b) :
    indiffRel ballotXY a b = false := by
  revert a b
  decide

lemma indiffRel_ballotYX_ne (a b : Fin 3) (hab : a ≠ b) :
    indiffRel ballotYX a b = false := by
  revert a b
  decide

lemma indiffRel_ballotZX_ne (a b : Fin 3) (hab : a ≠ b) :
    indiffRel ballotZX a b = false := by
  revert a b
  decide

lemma indiffRel_ballotYZ_ne (a b : Fin 3) (hab : a ≠ b) :
    indiffRel ballotYZ a b = false := by
  revert a b
  decide

/-- No voter in the paper's transitive electorate expresses indifference. -/
lemma sharpAllWeak_indiffCount_eq_zero (K j : ℕ) (hj : j ≤ K) {a b : Fin 3}
    (hab : a ≠ b) :
    indiffCount (nlhfSharpAllWeakProfile3 K j) a b = 0 := by
  rw [nlhfSharpAllWeakProfile3_indiffCount K j hj,
    indiffRel_ballotXY_ne a b hab, indiffRel_ballotYX_ne a b hab,
    indiffRel_ballotZX_ne a b hab, indiffRel_ballotYZ_ne a b hab]
  simp [prefIndicator]

lemma sharpAllWeak_strict_01 (K j : ℕ) (hj : j ≤ K) :
    strictPrefCount (nlhfSharpAllWeakProfile3 K j) 0 1 = (j : ℝ) := by
  rw [nlhfSharpAllWeakProfile3_strictPrefCount K j hj,
    show strictPrefRel ballotXY 0 1 = true from by decide,
    show strictPrefRel ballotYX 0 1 = false from by decide,
    show strictPrefRel ballotZX 0 1 = false from by decide,
    show strictPrefRel ballotYZ 0 1 = false from by decide]
  simp [prefIndicator]

lemma sharpAllWeak_strict_10 (K j : ℕ) (hj : j ≤ K) :
    strictPrefCount (nlhfSharpAllWeakProfile3 K j) 1 0 =
      (K : ℝ) - (j : ℝ) := by
  rw [nlhfSharpAllWeakProfile3_strictPrefCount K j hj,
    show strictPrefRel ballotXY 1 0 = false from by decide,
    show strictPrefRel ballotYX 1 0 = true from by decide,
    show strictPrefRel ballotZX 1 0 = false from by decide,
    show strictPrefRel ballotYZ 1 0 = false from by decide]
  simp [prefIndicator]

lemma sharpAllWeak_strict_02 (K j : ℕ) (hj : j ≤ K) :
    strictPrefCount (nlhfSharpAllWeakProfile3 K j) 0 2 = 0 := by
  rw [nlhfSharpAllWeakProfile3_strictPrefCount K j hj,
    show strictPrefRel ballotXY 0 2 = false from by decide,
    show strictPrefRel ballotYX 0 2 = false from by decide,
    show strictPrefRel ballotZX 0 2 = false from by decide,
    show strictPrefRel ballotYZ 0 2 = false from by decide]
  simp [prefIndicator]

lemma sharpAllWeak_strict_20 (K j : ℕ) (hj : j ≤ K) :
    strictPrefCount (nlhfSharpAllWeakProfile3 K j) 2 0 = (K : ℝ) := by
  rw [nlhfSharpAllWeakProfile3_strictPrefCount K j hj,
    show strictPrefRel ballotXY 2 0 = false from by decide,
    show strictPrefRel ballotYX 2 0 = false from by decide,
    show strictPrefRel ballotZX 2 0 = true from by decide,
    show strictPrefRel ballotYZ 2 0 = false from by decide]
  simp [prefIndicator]

lemma sharpAllWeak_strict_12 (K j : ℕ) (hj : j ≤ K) :
    strictPrefCount (nlhfSharpAllWeakProfile3 K j) 1 2 = (K : ℝ) := by
  rw [nlhfSharpAllWeakProfile3_strictPrefCount K j hj,
    show strictPrefRel ballotXY 1 2 = false from by decide,
    show strictPrefRel ballotYX 1 2 = false from by decide,
    show strictPrefRel ballotZX 1 2 = false from by decide,
    show strictPrefRel ballotYZ 1 2 = true from by decide]
  simp [prefIndicator]

lemma sharpAllWeak_strict_21 (K j : ℕ) (hj : j ≤ K) :
    strictPrefCount (nlhfSharpAllWeakProfile3 K j) 2 1 = 0 := by
  rw [nlhfSharpAllWeakProfile3_strictPrefCount K j hj,
    show strictPrefRel ballotXY 2 1 = false from by decide,
    show strictPrefRel ballotYX 2 1 = false from by decide,
    show strictPrefRel ballotZX 2 1 = false from by decide,
    show strictPrefRel ballotYZ 2 1 = false from by decide]
  simp [prefIndicator]

/-- Every distinct pair is compared by exactly the `K` voters of its group, so
the pair-specific normalizer is `t = K` throughout. -/
lemma sharpAllWeak_compared (K j : ℕ) (hj : j ≤ K) {a b : Fin 3} (hab : a ≠ b)
    (hs : strictPrefCount (nlhfSharpAllWeakProfile3 K j) a b +
      strictPrefCount (nlhfSharpAllWeakProfile3 K j) b a = (K : ℝ)) :
    comparedCount (nlhfSharpAllWeakProfile3 K j) a b = (K : ℝ) := by
  unfold comparedCount strictComparedCount
  rw [sharpAllWeak_indiffCount_eq_zero K j hj hab, hs]
  ring

lemma paperNormalizedMargin_eq_of_compared {V : Type*} [Fintype V]
    (R : V → Fin 3 → Fin 3 → Bool) (a b : Fin 3) {t : ℝ} (ht : t ≠ 0)
    (hcomp : comparedCount R a b = t) :
    paperNormalizedMargin R a b =
      (strictPrefCount R a b - strictPrefCount R b a) / t := by
  unfold paperNormalizedMargin
  rw [hcomp, if_neg ht]

/-- The paper's transitive electorate realizes the all-profiles sharpness
matrix, with parameter `η = 2 (K - j) / K`. -/
lemma paperNormalizedMargin_nlhfSharpAllWeakProfile3 (K j : ℕ) (hj : j ≤ K)
    (hK : 0 < K) :
    paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR
  have hdiag := (paperNormalizedMargin_isNormalizedMarginMatrix
    (nlhfSharpAllWeakProfile3 K j)).1
  have e00 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 0 0 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 0 0 := by
    rw [hdiag 0]
    simp [nlhfSharpAllMargin3]
  have e11 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 1 1 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 1 1 := by
    rw [hdiag 1]
    simp [nlhfSharpAllMargin3]
  have e22 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 2 2 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 2 2 := by
    rw [hdiag 2]
    simp [nlhfSharpAllMargin3]
  have e01 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 0 1 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 0 1 := by
    rw [paperNormalizedMargin_eq_of_compared _ 0 1 hKne
      (sharpAllWeak_compared K j hj (by decide) (by
        rw [sharpAllWeak_strict_01 K j hj, sharpAllWeak_strict_10 K j hj]
        ring)),
      sharpAllWeak_strict_01 K j hj, sharpAllWeak_strict_10 K j hj]
    show ((j : ℝ) - ((K : ℝ) - (j : ℝ))) / (K : ℝ) =
      1 - 2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)
    field_simp
    ring
  have e10 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 1 0 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 1 0 := by
    rw [paperNormalizedMargin_eq_of_compared _ 1 0 hKne
      (sharpAllWeak_compared K j hj (by decide) (by
        rw [sharpAllWeak_strict_01 K j hj, sharpAllWeak_strict_10 K j hj]
        ring)),
      sharpAllWeak_strict_01 K j hj, sharpAllWeak_strict_10 K j hj]
    show (((K : ℝ) - (j : ℝ)) - (j : ℝ)) / (K : ℝ) =
      -(1 - 2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ))
    field_simp
    ring
  have e02 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 0 2 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 0 2 := by
    rw [paperNormalizedMargin_eq_of_compared _ 0 2 hKne
      (sharpAllWeak_compared K j hj (by decide) (by
        rw [sharpAllWeak_strict_02 K j hj, sharpAllWeak_strict_20 K j hj]
        ring)),
      sharpAllWeak_strict_02 K j hj, sharpAllWeak_strict_20 K j hj]
    show ((0 : ℝ) - (K : ℝ)) / (K : ℝ) = -1
    field_simp
    ring
  have e20 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 2 0 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 2 0 := by
    rw [paperNormalizedMargin_eq_of_compared _ 2 0 hKne
      (sharpAllWeak_compared K j hj (by decide) (by
        rw [sharpAllWeak_strict_02 K j hj, sharpAllWeak_strict_20 K j hj]
        ring)),
      sharpAllWeak_strict_02 K j hj, sharpAllWeak_strict_20 K j hj]
    show ((K : ℝ) - 0) / (K : ℝ) = 1
    field_simp
    ring
  have e12 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 1 2 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 1 2 := by
    rw [paperNormalizedMargin_eq_of_compared _ 1 2 hKne
      (sharpAllWeak_compared K j hj (by decide) (by
        rw [sharpAllWeak_strict_12 K j hj, sharpAllWeak_strict_21 K j hj]
        ring)),
      sharpAllWeak_strict_12 K j hj, sharpAllWeak_strict_21 K j hj]
    show ((K : ℝ) - 0) / (K : ℝ) = 1
    field_simp
    ring
  have e21 : paperNormalizedMargin (nlhfSharpAllWeakProfile3 K j) 2 1 =
      nlhfSharpAllMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 2 1 := by
    rw [paperNormalizedMargin_eq_of_compared _ 2 1 hKne
      (sharpAllWeak_compared K j hj (by decide) (by
        rw [sharpAllWeak_strict_12 K j hj, sharpAllWeak_strict_21 K j hj]
        ring)),
      sharpAllWeak_strict_12 K j hj, sharpAllWeak_strict_21 K j hj]
    show ((0 : ℝ) - (K : ℝ)) / (K : ℝ) = -1
    field_simp
    ring
  funext a b
  fin_cases a <;> fin_cases b <;> assumption

/-- A one-pair improvement of the sharpness matrix is again a sharpness
matrix with a smaller parameter. -/
lemma improvePairMargin_nlhfSharpAllMargin3 (η δ : ℝ) :
    improvePairMargin (nlhfSharpAllMargin3 η) 0 1 δ =
      nlhfSharpAllMargin3 (η - δ) := by
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp [improvePairMargin, nlhfSharpAllMargin3] <;> ring

/-! ### The low-temperature converse on actual transitive profiles

Below the threshold the paper improves `x` by moving a single voter of the
`x`-versus-`y` group from `y ≻ x` to `x ≻ y`.  Replicating the electorate
`m + 1` times makes the resulting margin change equal to the `m`-th term of
the vanishing sequence supplied by the secant argument, so the abstract
matrix-level drop is realized by an actual pair of finite profiles of
reflexive transitive relations. -/

theorem nlhfSharpAllWeak_lowTempProfileDrop_fin3
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F) :
    ∀ τ : ℝ, 0 < τ → τ < (3 : ℝ) / 8 →
      ∃ N m : ℕ, ∃ b : ℝ,
        0 < N ∧ 0 < b ∧ b < 1 ∧
        IsReflexiveProfile
          (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))) ∧
        IsReflexiveProfile
          (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1)) ∧
        IsTransitiveProfile
          (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))) ∧
        IsTransitiveProfile
          (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1)) ∧
        IsWeakProfileImprovement
          (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1)))
          (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1))
          (0 : Fin 3) ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (paperNormalizedMargin
              (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
            (nlhfSharpSymLottery3 b)) ∧
        F τ
            (paperNormalizedMargin
              (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1)))
            (nlhfBacksolvedReference τ
              (paperNormalizedMargin
                (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
              (nlhfSharpSymLottery3 b)) 0 <
          F τ
            (paperNormalizedMargin
              (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
            (nlhfBacksolvedReference τ
              (paperNormalizedMargin
                (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
              (nlhfSharpSymLottery3 b)) 0 := by
  intro τ hτ hτlt
  rcases exists_threeCandidateFiniteEtaSharpnessScalar_of_tau_lt_three_eighths
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
  rcases exists_nlhfSharpAll_secant_drop_index_of_small_sequence
      F hselect hunique hτ hb0 hb1 hη0 hη1 ha hd ha0 hd0 hlimitneg
      hspos hsle hstendsto with
    ⟨m, _hsmpos, _hsmle, hdrop⟩
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
  have hmne : ((m : ℝ) + 1) ≠ 0 := ne_of_gt hmpos
  have hsplit : N * (m + 1) = (N - 1) * (m + 1) + (m + 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hn : n + 1 - 1 = n := by omega
    rw [hn]
    ring
  have hj : (N - 1) * (m + 1) ≤ N * (m + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le N 1)
  have hj1 : (N - 1) * (m + 1) + 1 ≤ N * (m + 1) := by
    rw [hsplit]
    exact Nat.add_le_add_left (by omega : 1 ≤ m + 1) _
  have hKpos : 0 < N * (m + 1) := Nat.mul_pos hN (Nat.succ_pos m)
  have hcastsplit : ((N * (m + 1) : ℕ) : ℝ) =
      (((N - 1) * (m + 1) : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  have hmcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hKj : ((N * (m + 1) : ℕ) : ℝ) - (((N - 1) * (m + 1) : ℕ) : ℝ) =
      (m : ℝ) + 1 := by
    rw [hmcast] at hcastsplit
    linarith
  have hKj1 : ((N * (m + 1) : ℕ) : ℝ) -
      (((N - 1) * (m + 1) + 1 : ℕ) : ℝ) = (m : ℝ) := by
    have hstep : (((N - 1) * (m + 1) + 1 : ℕ) : ℝ) =
        (((N - 1) * (m + 1) : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hstep]
    linarith
  have hKR : ((N * (m + 1) : ℕ) : ℝ) = (N : ℝ) * ((m : ℝ) + 1) := by
    push_cast
    ring
  have hold :
      paperNormalizedMargin
          (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))) =
        nlhfSharpAllMargin3 η := by
    rw [paperNormalizedMargin_nlhfSharpAllWeakProfile3 _ _ hj hKpos]
    congr 1
    rw [hKj, hKR, hηeq]
    field_simp
  have hnew :
      paperNormalizedMargin
          (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1)) =
        improvePairMargin (nlhfSharpAllMargin3 η) 0 1 (sseq m) := by
    rw [improvePairMargin_nlhfSharpAllMargin3,
      paperNormalizedMargin_nlhfSharpAllWeakProfile3 _ _ hj1 hKpos]
    congr 1
    rw [hKj1, hKR]
    dsimp [sseq]
    rw [hηeq]
    field_simp
    ring
  have hρ :
      IsFullSupportLottery
        (nlhfBacksolvedReference τ
          (paperNormalizedMargin
            (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
          (nlhfSharpSymLottery3 b)) :=
    nlhfBacksolvedReference_fullSupport
      (nlhfSharpSymLottery3_fullSupport hb0 hb1)
  refine ⟨N, m, b, hN, hb0, hb1,
    nlhfSharpAllWeakProfile3_reflexive _ _,
    nlhfSharpAllWeakProfile3_reflexive _ _,
    nlhfSharpAllWeakProfile3_transitive _ _,
    nlhfSharpAllWeakProfile3_transitive _ _,
    nlhfSharpAllWeakProfile3_improvement _ _, hρ, ?_⟩
  rw [hold, hnew]
  exact hdrop

/-- Below `3/8` the paper's transitive-profile witness refutes profile-level
probabilistic monotonicity of selected NLHF. -/
theorem not_selectedNLHF_weakProfileAllMonotone_of_tau_lt_three_eighths
    {τ : ℝ} (hτpos : 0 < τ) (hτlt : τ < (3 : ℝ) / 8) :
    ¬ SelectedNLHFWeakProfileAllMonotonicity τ := by
  intro hmono
  rcases nlhfSharpAllWeak_lowTempProfileDrop_fin3
      (selectedNLHF (α := Fin 3))
      (selectedNLHF_selection (α := Fin 3))
      (selectedNLHF_isTheNLHF (α := Fin 3)) τ hτpos hτlt with
    ⟨N, m, b, _hN, _hb0, _hb1, _hrefl, _hrefl', _htrans, _htrans',
      himp, hρ, hdrop⟩
  have hle := hmono
    (V := Sum (Fin (N * (m + 1)))
      (Sum (Fin (N * (m + 1))) (Fin (N * (m + 1)))))
    (α := Fin 3)
    (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1)))
    (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1) + 1))
    (nlhfBacksolvedReference τ
      (paperNormalizedMargin
        (nlhfSharpAllWeakProfile3 (N * (m + 1)) ((N - 1) * (m + 1))))
      (nlhfSharpSymLottery3 b))
    0 hρ himp
  exact not_lt_of_ge hle hdrop

/-- The `3/8` clause of Theorem `NLHFmono`, stated over actual finite profiles
of reflexive binary relations with the paper's pair-normalized margins and the
paper's improvement conditions (i)–(iii). -/
theorem NLHFmono_weak_profile_all {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFWeakProfileAllMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    by_contra hnot
    exact not_selectedNLHF_weakProfileAllMonotone_of_tau_lt_three_eighths
      hτ (lt_of_not_ge hnot) hmono
  · intro hτge
    exact selectedNLHF_weakProfileAllMonotone_of_tau_ge_three_eighths hτge

end PaperFormalization
