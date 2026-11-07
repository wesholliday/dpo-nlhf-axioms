import PaperFormalization.Axioms

open scoped BigOperators

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Denominator for multiplicative reference updates. -/
noncomputable def tiltDen (ρ ℓ : α → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun x => ρ x * ℓ x)

/-- The probability-kinematics update `ρ ↦ normalize(ρ * ℓ)`. -/
noncomputable def tilt (ρ ℓ : α → ℝ) : α → ℝ :=
  fun x => ρ x * ℓ x / tiltDen ρ ℓ

lemma tiltDen_pos {ρ ℓ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hℓ : ∀ x : α, 0 < ℓ x) :
    0 < tiltDen ρ ℓ := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty α›
  have hterm : 0 < ρ x0 * ℓ x0 := mul_pos (hρ x0) (hℓ x0)
  have hrest : 0 ≤ Finset.sum (Finset.univ.erase x0) (fun x => ρ x * ℓ x) := by
    refine Finset.sum_nonneg ?_
    intro x hx
    exact (mul_pos (hρ x) (hℓ x)).le
  have hsplit :
      tiltDen ρ ℓ =
        ρ x0 * ℓ x0 + Finset.sum (Finset.univ.erase x0) (fun x => ρ x * ℓ x) := by
    unfold tiltDen
    rw [← Finset.add_sum_erase (s := Finset.univ) (f := fun x => ρ x * ℓ x) (by simp)]
  linarith

lemma tilt_pos {ρ ℓ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hℓ : ∀ x : α, 0 < ℓ x) (x : α) :
    0 < tilt ρ ℓ x := by
  unfold tilt
  exact div_pos (mul_pos (hρ x) (hℓ x)) (tiltDen_pos hρ hℓ)

lemma tilt_sum_one {ρ ℓ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hℓ : ∀ x : α, 0 < ℓ x) :
    Finset.sum Finset.univ (fun x => tilt ρ ℓ x) = 1 := by
  have hden : tiltDen ρ ℓ ≠ 0 := (tiltDen_pos hρ hℓ).ne'
  calc
    Finset.sum Finset.univ (fun x => tilt ρ ℓ x)
        = Finset.sum Finset.univ (fun x => ρ x * ℓ x) / tiltDen ρ ℓ := by
            simp [tilt, Finset.sum_div]
    _ = 1 := by
          change tiltDen ρ ℓ / tiltDen ρ ℓ = 1
          exact div_self hden

lemma tilt_fullSupport {ρ ℓ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hℓ : ∀ x : α, 0 < ℓ x) :
    IsFullSupportLottery (tilt ρ ℓ) :=
  ⟨tilt_pos hρ hℓ, tilt_sum_one hρ hℓ⟩

lemma tiltDen_tilt {ρ ℓ₁ ℓ₂ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hℓ₁ : ∀ x : α, 0 < ℓ₁ x) :
    tiltDen (tilt ρ ℓ₁) ℓ₂ =
      tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x) / tiltDen ρ ℓ₁ := by
  have hden : tiltDen ρ ℓ₁ ≠ 0 := (tiltDen_pos hρ hℓ₁).ne'
  have hsum : (Finset.sum Finset.univ (fun x => ρ x * ℓ₁ x)) ≠ 0 := by
    simpa [tiltDen] using hden
  calc
    tiltDen (tilt ρ ℓ₁) ℓ₂
        = Finset.sum Finset.univ
            (fun x => (ρ x * (ℓ₁ x * ℓ₂ x)) / tiltDen ρ ℓ₁) := by
              unfold tiltDen tilt
              refine Finset.sum_congr rfl ?_
              intro x hx
              field_simp [hsum]
              simp [tiltDen]
              ring
    _ = tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x) / tiltDen ρ ℓ₁ := by
          simp [tiltDen, Finset.sum_div]

omit [Nonempty α] in
lemma tilt_eq_inv_one_add {ρ ℓ : α → ℝ} {x : α}
    (hρx : 0 < ρ x) (hℓx : 0 < ℓ x) :
    tilt ρ ℓ x =
      (1 /
        (1 + Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * (ℓ z / ℓ x)))) := by
  classical
  have hxden : ρ x * ℓ x ≠ 0 := by positivity
  have hsplit :
      tiltDen ρ ℓ =
        ρ x * ℓ x + Finset.sum (Finset.univ.erase x) (fun z => ρ z * ℓ z) := by
    unfold tiltDen
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun z => ρ z * ℓ z) (by simp)]
  unfold tilt
  rw [hsplit]
  have hterm :
      ∀ z ∈ Finset.univ.erase x,
        ρ z * ℓ z =
          (ρ x * ℓ x) * ((ρ z / ρ x) * (ℓ z / ℓ x)) := by
    intro z hz
    field_simp [hρx.ne', hℓx.ne']
  have hsum :
      Finset.sum (Finset.univ.erase x) (fun z => ρ z * ℓ z) =
        (ρ x * ℓ x) *
          Finset.sum (Finset.univ.erase x)
            (fun z => (ρ z / ρ x) * (ℓ z / ℓ x)) := by
    calc
      Finset.sum (Finset.univ.erase x) (fun z => ρ z * ℓ z)
          =
        Finset.sum (Finset.univ.erase x)
          (fun z => (ρ x * ℓ x) * ((ρ z / ρ x) * (ℓ z / ℓ x))) := by
            exact Finset.sum_congr rfl hterm
      _ =
        (ρ x * ℓ x) *
          Finset.sum (Finset.univ.erase x)
            (fun z => (ρ z / ρ x) * (ℓ z / ℓ x)) := by
          rw [← Finset.mul_sum]
  have hden :
      ρ x * ℓ x + Finset.sum (Finset.univ.erase x) (fun z => ρ z * ℓ z) =
        (ρ x * ℓ x) *
          (1 + Finset.sum (Finset.univ.erase x)
            (fun z => (ρ z / ρ x) * (ℓ z / ℓ x))) := by
    rw [hsum, mul_add, mul_one]
  calc
    ρ x * ℓ x /
        (ρ x * ℓ x + Finset.sum (Finset.univ.erase x) (fun z => ρ z * ℓ z))
        =
      ρ x * ℓ x /
        ((ρ x * ℓ x) *
          (1 + Finset.sum (Finset.univ.erase x)
            (fun z => (ρ z / ρ x) * (ℓ z / ℓ x)))) := by
          rw [hden]
    _ =
      1 /
        (1 + Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * (ℓ z / ℓ x))) := by
          field_simp [hxden]

omit [Nonempty α] in
/-- If all likelihood ratios against `x` weakly decrease, the multiplicative
tilt gives `x` weakly more probability. This is the denominator argument used
for RTBT monotonicity. -/
theorem tilt_le_of_likelihood_ratio_le {ρ ℓ ℓ' : α → ℝ} {x : α}
    (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hℓpos : ∀ z : α, 0 < ℓ z) (hℓ'pos : ∀ z : α, 0 < ℓ' z)
    (hratio : ∀ z : α, z ≠ x → ℓ' z / ℓ' x ≤ ℓ z / ℓ x) :
    tilt ρ ℓ x ≤ tilt ρ ℓ' x := by
  classical
  rw [tilt_eq_inv_one_add hρx (hℓpos x),
    tilt_eq_inv_one_add hρx (hℓ'pos x)]
  let oldDen :=
    1 + Finset.sum (Finset.univ.erase x)
      (fun z => (ρ z / ρ x) * (ℓ z / ℓ x))
  let newDen :=
    1 + Finset.sum (Finset.univ.erase x)
      (fun z => (ρ z / ρ x) * (ℓ' z / ℓ' x))
  have hterm_nonneg_new :
      ∀ z ∈ Finset.univ.erase x, 0 ≤ (ρ z / ρ x) * (ℓ' z / ℓ' x) := by
    intro z hz
    exact mul_nonneg (div_nonneg (hρnonneg z) hρx.le)
      (div_nonneg (hℓ'pos z).le (hℓ'pos x).le)
  have hnewpos : 0 < newDen := by
    dsimp [newDen]
    nlinarith [Finset.sum_nonneg hterm_nonneg_new]
  have hsum_le :
      Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * (ℓ' z / ℓ' x)) ≤
        Finset.sum (Finset.univ.erase x)
          (fun z => (ρ z / ρ x) * (ℓ z / ℓ x)) := by
    refine Finset.sum_le_sum ?_
    intro z hz
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    exact mul_le_mul_of_nonneg_left (hratio z hzx)
      (div_nonneg (hρnonneg z) hρx.le)
  have hden_le : newDen ≤ oldDen := by
    dsimp [oldDen, newDen]
    linarith
  exact one_div_le_one_div_of_le hnewpos hden_le

lemma tilt_tilt_mul {ρ ℓ₁ ℓ₂ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hℓ₁ : ∀ x : α, 0 < ℓ₁ x) (hℓ₂ : ∀ x : α, 0 < ℓ₂ x) :
    tilt (tilt ρ ℓ₁) ℓ₂ = tilt ρ (fun x => ℓ₁ x * ℓ₂ x) := by
  funext x
  have hden₁ : tiltDen ρ ℓ₁ ≠ 0 := (tiltDen_pos hρ hℓ₁).ne'
  have hden₁₂ : tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x) ≠ 0 := by
    exact (tiltDen_pos hρ fun x => mul_pos (hℓ₁ x) (hℓ₂ x)).ne'
  have hden_tilt :
      tiltDen (tilt ρ ℓ₁) ℓ₂ =
        tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x) / tiltDen ρ ℓ₁ :=
    tiltDen_tilt hρ hℓ₁
  change (tilt ρ ℓ₁ x * ℓ₂ x / tiltDen (tilt ρ ℓ₁) ℓ₂) =
    (ρ x * (ℓ₁ x * ℓ₂ x) / tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x))
  rw [hden_tilt]
  unfold tilt
  field_simp [hden₁, hden₁₂]

/-- Proposition `RTBTorder` for every rule written as a positive multiplicative
tilt. This applies to both PB and RTBT after instantiating `ℓ`. -/
theorem tilt_commutative {ρ ℓ₁ ℓ₂ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hℓ₁ : ∀ x : α, 0 < ℓ₁ x) (hℓ₂ : ∀ x : α, 0 < ℓ₂ x) :
    tilt (tilt ρ ℓ₁) ℓ₂ = tilt (tilt ρ ℓ₂) ℓ₁ := by
  rw [tilt_tilt_mul hρ hℓ₁ hℓ₂, tilt_tilt_mul hρ hℓ₂ hℓ₁]
  funext x
  simp [tilt, mul_comm]

/-- A matrix-level rule obtained by multiplicatively tilting the reference by
a profile-dependent positive likelihood vector. -/
noncomputable def multiplicativeMatrixRule
    (ℓ : (α → α → ℝ) → α → ℝ) : MatrixRule α :=
  fun M ρ => tilt ρ (ℓ M)

/-- Proposition `RTBTorder`/PB commutativity in predicate form: any
profile-dependent multiplicative update is commutative when all likelihoods
are positive. -/
theorem multiplicativeMatrixRule_commutative
    (ℓ : (α → α → ℝ) → α → ℝ)
    (hℓ : ∀ (M : α → α → ℝ) (x : α), 0 < ℓ M x) :
    SatisfiesCommutativity (multiplicativeMatrixRule ℓ) := by
  intro M N ρ _hM _hN hρ
  exact tilt_commutative hρ.1 (hℓ M) (hℓ N)

theorem multiplicativeMatrixRule_preserves_fullSupport
    (ℓ : (α → α → ℝ) → α → ℝ)
    (hℓ : ∀ (M : α → α → ℝ) (x : α), 0 < ℓ M x)
    (M : α → α → ℝ) {ρ : α → ℝ}
    (hρ : IsFullSupportLottery ρ) :
    IsFullSupportLottery (multiplicativeMatrixRule ℓ M ρ) :=
  tilt_fullSupport hρ.1 (hℓ M)

end PaperFormalization
