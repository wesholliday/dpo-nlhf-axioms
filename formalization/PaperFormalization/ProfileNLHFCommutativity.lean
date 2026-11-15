import PaperFormalization.NLHFSelectedCommutativity
import PaperFormalization.ProfileFord
import PaperFormalization.WeakProfileBorda

/-!
# Profile realizations for Proposition `NLHFcomm`

The commutativity-violation witnesses `cycleMargin3` and `linearMargin3`
(`NLHFCommutativity.lean`) are here identified with the normalized strict
margin matrices of the actual linear-order profiles used in the paper's
proof of Proposition `NLHFcomm` (`paper/main.tex`): the three-voter
Condorcet-cycle profile `𝐂` with rankings `abc`, `bca`, `cab`, and the
one-voter profile `𝐋` with ranking `abc`.  The paper's parenthetical "even on
profiles of linear orders" is backed by linearity certificates for the
realized profiles.
-/

open scoped BigOperators

namespace PaperFormalization

/-- Strict preference induced by a rank function on three candidates
(`Fin 3` analogue of `prefByRank` in `NLHFInvolvement.lean`). -/
def prefByRank3 (rank : Fin 3 → ℕ) (x y : Fin 3) : Bool :=
  decide (rank x < rank y)

/-- Ranking `a b c`. -/
def rank3ABC : Fin 3 → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2

/-- Ranking `b c a`. -/
def rank3BCA : Fin 3 → ℕ
  | 1 => 0 | 2 => 1 | 0 => 2

/-- Ranking `c a b`. -/
def rank3CAB : Fin 3 → ℕ
  | 2 => 0 | 0 => 1 | 1 => 2

/-- The paper's three-voter Condorcet-cycle profile `𝐂` (rankings
`abc`, `bca`, `cab`) from the proof of Proposition `NLHFcomm`. -/
def cycleProfile3 : Fin 3 → Fin 3 → Fin 3 → Bool :=
  fun i =>
    if i = 0 then prefByRank3 rank3ABC
    else if i = 1 then prefByRank3 rank3BCA
    else prefByRank3 rank3CAB

/-- The paper's one-voter profile `𝐋` with ranking `abc`. -/
def linearProfile3 : Fin 1 → Fin 3 → Fin 3 → Bool :=
  fun _ => prefByRank3 rank3ABC

/-- A single voter's relation is a strict linear order. -/
def IsStrictLinearOrderPref (p : Fin 3 → Fin 3 → Bool) : Prop :=
  IsAsymmetricPref p ∧
    (∀ x y z : Fin 3, p x y = true → p y z = true → p x z = true) ∧
      ∀ x y : Fin 3, x ≠ y → p x y = true ∨ p y x = true

/-- Every voter's relation in the profile is a strict linear order. -/
def IsStrictLinearOrderProfile {V : Type*}
    (R : V → Fin 3 → Fin 3 → Bool) : Prop :=
  ∀ i, IsStrictLinearOrderPref (R i)

lemma isStrictLinearOrderPref_prefByRank3
    {rank : Fin 3 → ℕ} (hinj : Function.Injective rank) :
    IsStrictLinearOrderPref (prefByRank3 rank) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    simp only [prefByRank3, decide_eq_true_eq] at h
    simp only [prefByRank3, decide_eq_false_iff_not]
    omega
  · intro x y z hxy hyz
    simp only [prefByRank3, decide_eq_true_eq] at hxy hyz ⊢
    omega
  · intro x y hxy
    have hne : rank x ≠ rank y := fun h => hxy (hinj h)
    simp only [prefByRank3, decide_eq_true_eq]
    omega

lemma rank3ABC_injective : Function.Injective rank3ABC := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rank3ABC]

lemma rank3BCA_injective : Function.Injective rank3BCA := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rank3BCA]

lemma rank3CAB_injective : Function.Injective rank3CAB := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rank3CAB]

/-- The cycle profile consists of strict linear orders. -/
lemma cycleProfile3_isStrictLinearOrderProfile :
    IsStrictLinearOrderProfile cycleProfile3 := by
  intro i
  fin_cases i
  · simpa [cycleProfile3] using
      isStrictLinearOrderPref_prefByRank3 rank3ABC_injective
  · simpa [cycleProfile3] using
      isStrictLinearOrderPref_prefByRank3 rank3BCA_injective
  · simpa [cycleProfile3] using
      isStrictLinearOrderPref_prefByRank3 rank3CAB_injective

/-- The one-voter profile consists of strict linear orders. -/
lemma linearProfile3_isStrictLinearOrderProfile :
    IsStrictLinearOrderProfile linearProfile3 :=
  fun _ => isStrictLinearOrderPref_prefByRank3 rank3ABC_injective

/-- Unrolled form of `strictCount` for three-voter profiles, eliminating the
`Finset` sum up front (mirroring the `strictCount3` idiom of
`NLHFInvolvement.lean`). -/
lemma strictCount_fin3 {β : Type*} (R : Fin 3 → β → β → Bool) (x y : β) :
    strictCount R x y =
      prefIndicator (R 0 x y) + prefIndicator (R 1 x y) +
        prefIndicator (R 2 x y) := by
  unfold strictCount
  rw [Fin.sum_univ_three]

/-- Unrolled form of `strictCount` for one-voter profiles. -/
lemma strictCount_fin1 {β : Type*} (R : Fin 1 → β → β → Bool) (x y : β) :
    strictCount R x y = prefIndicator (R 0 x y) := by
  unfold strictCount
  rw [Fin.sum_univ_one]

/-- **Profile realization:** the normalized strict margin matrix of the
paper's cycle profile `𝐂` is the commutativity witness `cycleMargin3`. -/
lemma cycleProfile3_normalizedStrictMargin :
    normalizedStrictMargin cycleProfile3 = cycleMargin3 := by
  funext x y
  unfold normalizedStrictMargin strictMargin
  rw [strictCount_fin3, strictCount_fin3]
  fin_cases x <;> fin_cases y <;>
    simp [cycleProfile3, prefByRank3, rank3ABC, rank3BCA, rank3CAB,
      prefIndicator, cycleMargin3, Fintype.card_fin] <;>
    norm_num

/-- **Profile realization:** the normalized strict margin matrix of the
paper's one-voter profile `𝐋` is the commutativity witness
`linearMargin3`. -/
lemma linearProfile3_normalizedStrictMargin :
    normalizedStrictMargin linearProfile3 = linearMargin3 := by
  funext x y
  unfold normalizedStrictMargin strictMargin
  rw [strictCount_fin1, strictCount_fin1]
  fin_cases x <;> fin_cases y <;>
    simp [linearProfile3, prefByRank3, rank3ABC, prefIndicator,
      linearMargin3, Fintype.card_fin] <;>
    norm_num

/-- A strict linear order in the sense of `IsStrictLinearOrderPref` is a linear
preference in the sense of `IsLinearPref` (`WeakProfileBorda.lean`):
irreflexivity follows from asymmetry. -/
lemma isLinearPref_of_isStrictLinearOrderPref
    {p : Fin 3 → Fin 3 → Bool} (h : IsStrictLinearOrderPref p) :
    IsLinearPref p := by
  refine ⟨?_, h.1, h.2.2, ?_⟩
  · intro x
    cases hpx : p x x
    · rfl
    · have hfalse := h.1 hpx
      rw [hpx] at hfalse
      simp at hfalse
  · intro x y z hxy hyz
    exact h.2.1 x y z hxy hyz

/-- **Profile realization under the paper's pair normalization:** the
`t_{x,y}`-normalized margin matrix `m̄(𝐂)` of the cycle profile is
`cycleMargin3`.  On linear-order profiles the paper's normalization agrees
with the `|V|`-normalization used above. -/
lemma cycleProfile3_paperNormalizedMargin :
    paperNormalizedMargin cycleProfile3 = cycleMargin3 := by
  rw [paperNormalizedMargin_eq_normalizedStrictMargin_of_linearProfile
      (fun i => isLinearPref_of_isStrictLinearOrderPref
        (cycleProfile3_isStrictLinearOrderProfile i)),
    cycleProfile3_normalizedStrictMargin]

/-- **Profile realization under the paper's pair normalization** for the
one-voter profile `𝐋`. -/
lemma linearProfile3_paperNormalizedMargin :
    paperNormalizedMargin linearProfile3 = linearMargin3 := by
  rw [paperNormalizedMargin_eq_normalizedStrictMargin_of_linearProfile
      (fun i => isLinearPref_of_isStrictLinearOrderPref
        (linearProfile3_isStrictLinearOrderProfile i)),
    linearProfile3_normalizedStrictMargin]

/-- Proposition `NLHFcomm` at the profile level: any rule satisfying the
NLHF fixed-point characterization fails commutativity on the realized
linear-order profiles `𝐂`, `𝐋` with the uniform reference. -/
theorem NLHFcomm_profile_from_fixed_point_characterization
    {τ : ℝ} (hτ : 0 < τ)
    (F : MatrixRule (Fin 3))
    (hfixed : ∀ (M : Fin 3 → Fin 3 → ℝ) (ρ : Fin 3 → ℝ),
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ → IsNLHFFixedPoint τ M ρ (F M ρ))
    (hunique : ∀ (M : Fin 3 → Fin 3 → ℝ) (ρ π : Fin 3 → ℝ),
      IsNormalizedMarginMatrix M → IsNLHFFixedPoint τ M ρ π → F M ρ = π) :
    F (normalizedStrictMargin cycleProfile3)
        (F (normalizedStrictMargin linearProfile3) uniform3) ≠
      F (normalizedStrictMargin linearProfile3)
        (F (normalizedStrictMargin cycleProfile3) uniform3) := by
  rw [cycleProfile3_normalizedStrictMargin,
    linearProfile3_normalizedStrictMargin]
  exact NLHFcomm_from_fixed_point_characterization hτ F hfixed hunique

/-- The selected NLHF rule violates commutativity on the realized
linear-order profiles. -/
theorem selectedNLHF_profile_commutativity_violation
    {τ : ℝ} (hτ : 0 < τ) :
    selectedNLHF (α := Fin 3) τ (normalizedStrictMargin cycleProfile3)
        (selectedNLHF (α := Fin 3) τ
          (normalizedStrictMargin linearProfile3) uniform3) ≠
      selectedNLHF (α := Fin 3) τ (normalizedStrictMargin linearProfile3)
        (selectedNLHF (α := Fin 3) τ
          (normalizedStrictMargin cycleProfile3) uniform3) :=
  NLHFcomm_profile_from_fixed_point_characterization hτ
    ((selectedNLHF (α := Fin 3)) τ)
    (fun _ _ hM hρ => selectedNLHF_selection hτ hM hρ)
    (fun _ _ _ hM hπ => selectedNLHF_isTheNLHF hM hπ)

end PaperFormalization
