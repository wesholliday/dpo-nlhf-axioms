import PaperFormalization.Multiplicative

open scoped BigOperators

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Multiplicative proportional-Borda update, abstracted over a supplied score. -/
noncomputable def proportionalBorda (η : ℝ) (ρ B : α → ℝ) : α → ℝ :=
  tilt ρ (fun x => Real.exp (η * B x))

lemma proportionalBorda_fullSupport {η : ℝ} {ρ B : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) :
    IsFullSupportLottery (proportionalBorda η ρ B) :=
  ⟨tilt_pos hρ (fun _ => Real.exp_pos _) ,
    tilt_sum_one hρ (fun _ => Real.exp_pos _)⟩

omit [Nonempty α] in
lemma proportionalBorda_eq_inv_one_add {η : ℝ} {ρ B : α → ℝ} {x : α}
    (hρx : 0 < ρ x) :
    proportionalBorda η ρ B x =
      (1 /
        (1 + Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * Real.exp (η * (B z - B x))))) := by
  classical
  have hxden : ρ x * Real.exp (η * B x) ≠ 0 := by positivity
  have hsplit :
      tiltDen ρ (fun y => Real.exp (η * B y)) =
        ρ x * Real.exp (η * B x) +
          Finset.sum (Finset.univ.erase x) (fun z => ρ z * Real.exp (η * B z)) := by
    unfold tiltDen
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun z => ρ z * Real.exp (η * B z)) (by simp)]
  unfold proportionalBorda tilt
  rw [hsplit]
  have hterm :
      ∀ z ∈ Finset.univ.erase x,
        ρ z * Real.exp (η * B z) =
          (ρ x * Real.exp (η * B x)) *
            ((ρ z / ρ x) * Real.exp (η * (B z - B x))) := by
    intro z hz
    have hρxne : ρ x ≠ 0 := hρx.ne'
    have hexpne : Real.exp (η * B x) ≠ 0 := Real.exp_ne_zero (η * B x)
    have harg : η * (B z - B x) = η * B z - η * B x := by ring
    rw [harg, Real.exp_sub]
    field_simp [hρxne, hexpne]
  have hsum :
      Finset.sum (Finset.univ.erase x) (fun z => ρ z * Real.exp (η * B z)) =
        (ρ x * Real.exp (η * B x)) *
          Finset.sum (Finset.univ.erase x)
            (fun z => (ρ z / ρ x) * Real.exp (η * (B z - B x))) := by
    calc
      Finset.sum (Finset.univ.erase x) (fun z => ρ z * Real.exp (η * B z))
          =
        Finset.sum (Finset.univ.erase x)
          (fun z =>
            (ρ x * Real.exp (η * B x)) *
              ((ρ z / ρ x) * Real.exp (η * (B z - B x)))) := by
            exact Finset.sum_congr rfl hterm
      _ =
        (ρ x * Real.exp (η * B x)) *
          Finset.sum (Finset.univ.erase x)
            (fun z => (ρ z / ρ x) * Real.exp (η * (B z - B x))) := by
          rw [← Finset.mul_sum]
  have hden :
      ρ x * Real.exp (η * B x) +
          Finset.sum (Finset.univ.erase x) (fun z => ρ z * Real.exp (η * B z)) =
        (ρ x * Real.exp (η * B x)) *
          (1 + Finset.sum (Finset.univ.erase x)
            (fun z => (ρ z / ρ x) * Real.exp (η * (B z - B x)))) := by
    rw [hsum, mul_add, mul_one]
  calc
    (ρ x * Real.exp (η * B x)) /
        (ρ x * Real.exp (η * B x) +
          Finset.sum (Finset.univ.erase x) (fun z => ρ z * Real.exp (η * B z)))
        =
      (ρ x * Real.exp (η * B x)) /
        ((ρ x * Real.exp (η * B x)) *
          (1 + Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * Real.exp (η * (B z - B x))))
        ) := by
          rw [hden]
    _ =
      1 /
        (1 + Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * Real.exp (η * (B z - B x)))) := by
          field_simp [hxden]

omit [Nonempty α] in
/-- Proposition `PBPM`, reduced to the score-difference inequality proved in
the paper text. -/
theorem PBPM_from_score_differences {η : ℝ} {ρ B B' : α → ℝ} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hdiff : ∀ z : α, z ≠ x → B' z - B' x ≤ B z - B x) :
    proportionalBorda η ρ B x ≤ proportionalBorda η ρ B' x := by
  classical
  rw [proportionalBorda_eq_inv_one_add (η := η) (ρ := ρ) (B := B) hρx,
    proportionalBorda_eq_inv_one_add (η := η) (ρ := ρ) (B := B') hρx]
  let oldDen :=
    1 + Finset.sum (Finset.univ.erase x)
      (fun z => (ρ z / ρ x) * Real.exp (η * (B z - B x)))
  let newDen :=
    1 + Finset.sum (Finset.univ.erase x)
      (fun z => (ρ z / ρ x) * Real.exp (η * (B' z - B' x)))
  have hterm_nonneg_new :
      ∀ z ∈ Finset.univ.erase x, 0 ≤ (ρ z / ρ x) * Real.exp (η * (B' z - B' x)) := by
    intro z hz
    exact mul_nonneg (div_nonneg (hρnonneg z) hρx.le) (Real.exp_pos _).le
  have hnewpos : 0 < newDen := by
    dsimp [newDen]
    nlinarith [Finset.sum_nonneg hterm_nonneg_new]
  have hsum_le :
      Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * Real.exp (η * (B' z - B' x))) ≤
        Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * Real.exp (η * (B z - B x))) := by
    refine Finset.sum_le_sum ?_
    intro z hz
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    have harg : η * (B' z - B' x) ≤ η * (B z - B x) :=
      mul_le_mul_of_nonneg_left (hdiff z hzx) hη
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone harg)
      (div_nonneg (hρnonneg z) hρx.le)
  have hden_le : newDen ≤ oldDen := by
    dsimp [oldDen, newDen]
    linarith
  exact one_div_le_one_div_of_le hnewpos hden_le

omit [DecidableEq α] [Nonempty α] in
lemma PBPPI_score_difference_drop {B B' : α → ℝ} {x z : α}
    (hcard : 2 ≤ Fintype.card α)
    (hx : B' x = B x + ((Fintype.card α : ℝ) - 1))
    (hz : B' z ≤ B z + ((Fintype.card α : ℝ) - 2)) :
    B' z - B' x ≤ B z - B x - 1 := by
  rw [hx]
  have hcard' : (1 : ℝ) ≤ (Fintype.card α : ℝ) - 1 := by
    have hcardR : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by
      exact_mod_cast hcard
    linarith
  linarith

omit [Nonempty α] in
/-- Proposition `PBPPI`, positive-involvement part, reduced to the paper's
partial-Borda score bounds. -/
theorem PBPPI_from_score_bounds {η : ℝ} {ρ B B' : α → ℝ} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hcard : 2 ≤ Fintype.card α)
    (hx : B' x = B x + ((Fintype.card α : ℝ) - 1))
    (hothers : ∀ z : α, z ≠ x →
      B' z ≤ B z + ((Fintype.card α : ℝ) - 2)) :
    proportionalBorda η ρ B x ≤ proportionalBorda η ρ B' x := by
  refine PBPM_from_score_differences hη hρnonneg hρx ?_
  intro z hzx
  have hdrop := PBPPI_score_difference_drop hcard hx (hothers z hzx)
  linarith

omit [Nonempty α] in
/-- Proposition `PBPPI`, negative-involvement part, reduced to the paper's
partial-Borda score bounds. -/
theorem PBPNI_from_score_bounds {η : ℝ} {ρ B B' : α → ℝ} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hx : B' x = B x)
    (hothers : ∀ z : α, z ≠ x → B' z ≥ B z + 1) :
    proportionalBorda η ρ B' x ≤ proportionalBorda η ρ B x := by
  refine PBPM_from_score_differences (B := B') (B' := B) hη hρnonneg hρx ?_
  intro z hzx
  have hz := hothers z hzx
  rw [hx]
  linarith

/-! ## The paper's trivial `ρ(x) = 0` case

The proofs of Propositions `PBPM` and `PBPPI` in `paper/main.tex` begin by
disposing of the case `ρ(x) = 0`: "If `ρ(x) = 0`, then it is immediate that
`PB_η(R⁺,ρ)(x) ≥ PB_η(R,ρ)(x)`, so assume `ρ(x) > 0`."  The reason is that
proportional Borda multiplies the reference probability, so a candidate with
zero reference probability keeps probability `0` under every score vector.
The primed theorems below therefore drop the `0 < ρ x` hypothesis entirely,
matching the paper's quantification over all `ρ ∈ Δ`. -/

omit [Nonempty α] in
/-- If the reference lottery gives `x` no probability, proportional Borda
gives `x` no probability either, whatever the scores.  (No hypothesis on `ρ`
is needed: in Lean `0 * c / d = 0` even when `d = 0`.) -/
lemma proportionalBorda_eq_zero_of_ref_zero {η : ℝ} {ρ B : α → ℝ} {x : α}
    (hρx : ρ x = 0) : proportionalBorda η ρ B x = 0 := by
  simp [proportionalBorda, tilt, hρx]

omit [Nonempty α] in
/-- Proposition `PBPM` over the paper's full reference domain `ρ ∈ Δ`: the
`0 < ρ x` hypothesis of `PBPM_from_score_differences` is unnecessary. -/
theorem PBPM_from_score_differences' {η : ℝ} {ρ B B' : α → ℝ} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hdiff : ∀ z : α, z ≠ x → B' z - B' x ≤ B z - B x) :
    proportionalBorda η ρ B x ≤ proportionalBorda η ρ B' x := by
  rcases (hρnonneg x).eq_or_lt with hzero | hpos
  · have h0 : ρ x = 0 := hzero.symm
    have hL : proportionalBorda η ρ B x = 0 :=
      proportionalBorda_eq_zero_of_ref_zero h0
    have hR : proportionalBorda η ρ B' x = 0 :=
      proportionalBorda_eq_zero_of_ref_zero h0
    linarith
  · exact PBPM_from_score_differences hη hρnonneg hpos hdiff

omit [Nonempty α] in
/-- Positive-involvement half of Proposition `PBPPI` over the paper's full
reference domain `ρ ∈ Δ`. -/
theorem PBPPI_from_score_bounds' {η : ℝ} {ρ B B' : α → ℝ} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hcard : 2 ≤ Fintype.card α)
    (hx : B' x = B x + ((Fintype.card α : ℝ) - 1))
    (hothers : ∀ z : α, z ≠ x →
      B' z ≤ B z + ((Fintype.card α : ℝ) - 2)) :
    proportionalBorda η ρ B x ≤ proportionalBorda η ρ B' x := by
  refine PBPM_from_score_differences' hη hρnonneg ?_
  intro z hzx
  have hdrop := PBPPI_score_difference_drop hcard hx (hothers z hzx)
  linarith

omit [Nonempty α] in
/-- Negative-involvement half of Proposition `PBPPI` over the paper's full
reference domain `ρ ∈ Δ`. -/
theorem PBPNI_from_score_bounds' {η : ℝ} {ρ B B' : α → ℝ} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hx : B' x = B x)
    (hothers : ∀ z : α, z ≠ x → B' z ≥ B z + 1) :
    proportionalBorda η ρ B' x ≤ proportionalBorda η ρ B x := by
  refine PBPM_from_score_differences' (B := B') (B' := B) hη hρnonneg ?_
  intro z hzx
  have hz := hothers z hzx
  rw [hx]
  linarith

theorem proportionalBorda_commutative {η : ℝ} {ρ B₁ B₂ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) :
    proportionalBorda η (proportionalBorda η ρ B₁) B₂ =
      proportionalBorda η (proportionalBorda η ρ B₂) B₁ := by
  unfold proportionalBorda
  apply tilt_commutative hρ
  · intro x; positivity
  · intro x; positivity

/-- Proposition `RTBTorder`, proportional-Borda half: any rule obtained by
tilting the reference by `exp(η * B_M(x))` is commutative.  The profile-specific
score assignment `B` is an explicit input. -/
theorem proportionalBordaMatrixRule_commutative
    (η : ℝ) (B : (α → α → ℝ) → α → ℝ) :
    SatisfiesCommutativity (fun M ρ => proportionalBorda η ρ (B M)) := by
  intro M N ρ _hM _hN hρ
  exact proportionalBorda_commutative (η := η) hρ.1

end PaperFormalization
