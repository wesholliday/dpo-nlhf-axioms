import PaperFormalization.Axioms
import PaperFormalization.Multiplicative

open scoped BigOperators
open scoped Topology
open Filter

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [DecidableEq α] [Nonempty α] in
/-- RTBT is a multiplicative tilt once the Bradley--Terry strength vector has
been fixed. -/
lemma RTBTFromStrength_eq_tilt (β : ℝ) (ρ u : α → ℝ) :
    RTBTFromStrength β ρ u = tilt ρ (fun x => (u x) ^ (1 / β)) := by
  rfl

lemma RTBTFromStrength_fullSupport
    (β : ℝ) {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hu : ∀ x : α, 0 < u x) :
    IsFullSupportLottery (RTBTFromStrength β ρ u) := by
  rw [RTBTFromStrength_eq_tilt]
  refine ⟨?_, ?_⟩
  · intro x
    exact tilt_pos hρ (fun z => Real.rpow_pos_of_pos (hu z) _) x
  · exact tilt_sum_one hρ (fun z => Real.rpow_pos_of_pos (hu z) _)

/-- Normalize a positive strength vector to a lottery.  This is useful because
Bradley--Terry equations and RTBT are invariant under positive rescaling,
while `IsBTStrength` records the simplex-normalized representative. -/
noncomputable def normalizeStrength (u : α → ℝ) : α → ℝ :=
  fun x => u x / Finset.sum Finset.univ (fun z => u z)

omit [DecidableEq α] in
lemma normalizeStrength_den_pos {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    0 < Finset.sum Finset.univ (fun z => u z) := by
  obtain ⟨z0⟩ := ‹Nonempty α›
  exact Finset.sum_pos (fun z _hz => hu z) ⟨z0, by simp⟩

omit [DecidableEq α] in
lemma normalizeStrength_fullSupport {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    IsFullSupportLottery (normalizeStrength u) := by
  have hden_pos := normalizeStrength_den_pos (α := α) hu
  refine ⟨?_, ?_⟩
  · intro x
    exact div_pos (hu x) hden_pos
  · unfold normalizeStrength
    rw [← Finset.sum_div]
    exact div_self hden_pos.ne'

omit [DecidableEq α] [Nonempty α] in
theorem RTBTFromStrength_scaled
    {β a : ℝ} (ha : 0 < a) {ρ u : α → ℝ}
    (hu : ∀ x : α, 0 ≤ u x) :
    RTBTFromStrength β ρ (fun x => a * u x) =
      RTBTFromStrength β ρ u := by
  classical
  have hscale_ne : a ^ (1 / β) ≠ 0 :=
    (Real.rpow_pos_of_pos ha (1 / β)).ne'
  funext x
  have hden :
      Finset.sum Finset.univ
          (fun z => ρ z * (a * u z) ^ (1 / β)) =
        a ^ (1 / β) *
          Finset.sum Finset.univ (fun z => ρ z * (u z) ^ (1 / β)) := by
    calc
      Finset.sum Finset.univ
          (fun z => ρ z * (a * u z) ^ (1 / β))
          =
        Finset.sum Finset.univ
          (fun z => a ^ (1 / β) * (ρ z * (u z) ^ (1 / β))) := by
            refine Finset.sum_congr rfl ?_
            intro z _hz
            rw [Real.mul_rpow ha.le (hu z)]
            ring
      _ =
        a ^ (1 / β) *
          Finset.sum Finset.univ (fun z => ρ z * (u z) ^ (1 / β)) := by
            rw [Finset.mul_sum]
  unfold RTBTFromStrength
  rw [hden, Real.mul_rpow ha.le (hu x)]
  field_simp [hscale_ne]

omit [DecidableEq α] in
theorem RTBTFromStrength_normalizeStrength
    {β : ℝ} {ρ u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    RTBTFromStrength β ρ (normalizeStrength u) =
      RTBTFromStrength β ρ u := by
  have hden_pos := normalizeStrength_den_pos (α := α) hu
  have hnorm :
      normalizeStrength u =
        fun x => (1 / Finset.sum Finset.univ (fun z => u z)) * u x := by
    funext x
    unfold normalizeStrength
    ring
  rw [hnorm]
  exact RTBTFromStrength_scaled
    (one_div_pos.mpr hden_pos) (fun x => (hu x).le)

omit [DecidableEq α] in
/-- With equal reference mass on two alternatives, RTBT orders those
alternatives exactly as their Bradley--Terry strengths do. This is the
order-preservation step used to extend Anderson et al.'s `β = 1` statement to
all `β > 0`. -/
theorem RTBTFromStrength_order_iff_of_equal_reference
    {β : ℝ} (hβ : 0 < β) {ρ u : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x) (hu : ∀ x : α, 0 < u x)
    {x y : α} (hρxy : ρ x = ρ y) :
    RTBTFromStrength β ρ u y ≤ RTBTFromStrength β ρ u x ↔
      u y ≤ u x := by
  classical
  let D : ℝ :=
    Finset.sum Finset.univ (fun z => ρ z * (u z) ^ (1 / β))
  have hDpos : 0 < D := by
    obtain ⟨z0⟩ := ‹Nonempty α›
    dsimp [D]
    exact Finset.sum_pos
      (fun z _hz => mul_pos (hρ z) (Real.rpow_pos_of_pos (hu z) _))
      ⟨z0, by simp⟩
  have hexp_pos : 0 < 1 / β := one_div_pos.mpr hβ
  constructor
  · intro hrtbt
    have hnum :
        ρ y * (u y) ^ (1 / β) ≤ ρ x * (u x) ^ (1 / β) := by
      simpa [RTBTFromStrength, D] using
        (div_le_div_iff_of_pos_right hDpos).mp hrtbt
    have hpow :
        (u y) ^ (1 / β) ≤ (u x) ^ (1 / β) := by
      have hnum' :
          ρ x * (u y) ^ (1 / β) ≤ ρ x * (u x) ^ (1 / β) := by
        simpa [hρxy.symm] using hnum
      exact le_of_mul_le_mul_left hnum' (hρ x)
    by_contra hnot
    have hxy : u x < u y := lt_of_not_ge hnot
    have hpow_lt :
        (u x) ^ (1 / β) < (u y) ^ (1 / β) :=
      Real.rpow_lt_rpow (hu x).le hxy hexp_pos
    exact not_lt_of_ge hpow hpow_lt
  · intro hu_le
    have hpow :
        (u y) ^ (1 / β) ≤ (u x) ^ (1 / β) :=
      Real.rpow_le_rpow (hu y).le hu_le hexp_pos.le
    have hnum' :
        ρ x * (u y) ^ (1 / β) ≤ ρ x * (u x) ^ (1 / β) :=
      mul_le_mul_of_nonneg_left hpow (hρ x).le
    have hnum :
        ρ y * (u y) ^ (1 / β) ≤ ρ x * (u x) ^ (1 / β) := by
      simpa [hρxy.symm] using hnum'
    simpa [RTBTFromStrength, D] using
      (div_le_div_iff_of_pos_right hDpos).mpr hnum

/-- Proposition `RTBTorder`, specialized to two already-computed BT strength
vectors. The Ford/Zermelo existence theorem supplies those vectors; the
commutativity argument itself is purely multiplicative. -/
theorem RTBTFromStrength_commutative
    {β : ℝ} (hβ : 0 < β) {ρ u₁ u₂ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hu₁ : ∀ x : α, 0 < u₁ x) (hu₂ : ∀ x : α, 0 < u₂ x) :
    RTBTFromStrength β (RTBTFromStrength β ρ u₁) u₂ =
      RTBTFromStrength β (RTBTFromStrength β ρ u₂) u₁ := by
  have _hβne : β ≠ 0 := hβ.ne'
  rw [RTBTFromStrength_eq_tilt, RTBTFromStrength_eq_tilt,
    RTBTFromStrength_eq_tilt, RTBTFromStrength_eq_tilt]
  apply tilt_commutative hρ
  · intro x
    exact Real.rpow_pos_of_pos (hu₁ x) _
  · intro x
    exact Real.rpow_pos_of_pos (hu₂ x) _

/-- Proposition `RTBTorder`, RTBT half: once the Bradley--Terry strength vector
has been selected for each margin matrix and is always positive, the resulting
RTBT rule is commutative. -/
theorem RTBTorder_from_positive_BT_selection
    {β : ℝ} (hβ : 0 < β) {BT : (α → α → ℝ) → α → ℝ}
    (hBTpos : ∀ M : α → α → ℝ, ∀ x : α, 0 < BT M x) :
    SatisfiesCommutativity (fun M ρ => RTBTFromStrength β ρ (BT M)) := by
  intro M N ρ _hM _hN hρ
  exact RTBTFromStrength_commutative hβ hρ.1 (hBTpos M) (hBTpos N)

omit [Nonempty α] in
/-- Proposition `RTBTPM`, after the Bradley--Terry comparative-statics step:
if every strength ratio `u_z/u_x` weakly decreases when `x` is improved, then
the RTBT probability of `x` weakly increases. -/
theorem RTBTPM_from_BT_ratio_monotonicity
    {β : ℝ} (hβ : 0 < β) {ρ u u' : α → ℝ} {x : α}
    (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hu : ∀ z : α, 0 < u z) (hu' : ∀ z : α, 0 < u' z)
    (hratio : ∀ z : α, z ≠ x → u' z / u' x ≤ u z / u x) :
    RTBTFromStrength β ρ u x ≤ RTBTFromStrength β ρ u' x := by
  rw [RTBTFromStrength_eq_tilt, RTBTFromStrength_eq_tilt]
  refine tilt_le_of_likelihood_ratio_le hρnonneg hρx ?_ ?_ ?_
  · intro z
    exact Real.rpow_pos_of_pos (hu z) _
  · intro z
    exact Real.rpow_pos_of_pos (hu' z) _
  · intro z hzx
    have hpow :
        (u' z / u' x) ^ (1 / β) ≤ (u z / u x) ^ (1 / β) := by
      exact Real.rpow_le_rpow
        (div_nonneg (hu' z).le (hu' x).le)
        (hratio z hzx)
        (by positivity)
    rwa [Real.div_rpow (hu' z).le (hu' x).le,
      Real.div_rpow (hu z).le (hu x).le] at hpow

/-- Positivity and ratio monotonicity for a Bradley--Terry strength selector.
This reusable interface isolates the comparative-static property needed by
the RTBT denominator argument. -/
def HasBTRatioMonotonicityForImprovements
    (BT : (α → α → ℝ) → α → ℝ) : Prop :=
  (∀ (M : α → α → ℝ) (x : α), 0 < BT M x) ∧
  ∀ (M M' : α → α → ℝ) (x : α),
    IsNormalizedMarginMatrix M →
      IsNormalizedMarginMatrix M' →
        IsImprovementOf M M' x →
          ∀ z : α, z ≠ x → BT M' z / BT M' x ≤ BT M z / BT M x

omit [Nonempty α] in
/-- The RTBT probabilistic-monotonicity implication for any strength selector
satisfying `HasBTRatioMonotonicityForImprovements`. -/
theorem RTBTPM_from_BT_ratio_certificate
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTRatioMonotonicityForImprovements BT) :
    SatisfiesProbabilisticMonotonicity
      (fun M ρ => RTBTFromStrength β ρ (BT M)) := by
  intro M M' ρ x hM hM' hρ himp
  exact RTBTPM_from_BT_ratio_monotonicity hβ
    (fun z => (hρ.1 z).le) (hρ.1 x)
    (hBT.1 M) (hBT.1 M')
    (hBT.2 M M' x hM hM' himp)

/-- A reference distribution concentrating on the first two alternatives. -/
noncomputable def twoPointReference (ε : ℝ) : Fin 3 → ℝ
  | 0 => (1 - ε) / 2
  | 1 => (1 - ε) / 2
  | 2 => ε

/-- Limit-based reduction for RTBT involvement counterexamples. The concrete
paper proof supplies `f` and `g` from the two profiles and verifies the two
limits from the BT strength ratios. -/
theorem exists_drop_from_right_limit_drop
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 a))
    (hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 b))
    (hba : b < a) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ g ε < f ε := by
  have hgt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), g ε < f ε :=
    hg.eventually_lt hf hba
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hlt1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 := by
    exact eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  rcases (hgt.and (hpos.and hlt1)).exists with ⟨ε, hε⟩
  exact ⟨ε, hε.2.1, hε.2.2, hε.1⟩

/-- RTBT positive-involvement violation from the ratio drop in the appendix
proof of Proposition `InvolveViolRTBT`.

The hypotheses are exactly the analytic limits after concentrating the
reference on `{a,b}`; the theorem extracts the full-support reference
parameter witnessing the strict probability drop. -/
theorem rtbt_positive_involvement_violation_from_limits
    {β r r' : ℝ} (hβ : 0 < β)
    (hr : 0 < r) (hr' : 0 < r') (hrdrop : r' < r)
    {f g : ℝ → ℝ}
    (hf :
      Tendsto f (𝓝[>] (0 : ℝ))
        (𝓝 (r ^ (1 / β) / (r ^ (1 / β) + 1))))
    (hg :
      Tendsto g (𝓝[>] (0 : ℝ))
        (𝓝 (r' ^ (1 / β) / (r' ^ (1 / β) + 1)))) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ g ε < f ε := by
  have hpow : r' ^ (1 / β) < r ^ (1 / β) :=
    Real.rpow_lt_rpow hr'.le hrdrop (by positivity)
  have hlim :
      r' ^ (1 / β) / (r' ^ (1 / β) + 1) <
        r ^ (1 / β) / (r ^ (1 / β) + 1) := by
    have hden' : 0 < r' ^ (1 / β) + 1 := by positivity
    have hden : 0 < r ^ (1 / β) + 1 := by positivity
    rw [div_lt_div_iff₀ hden' hden]
    nlinarith [hpow]
  exact exists_drop_from_right_limit_drop hf hg hlim

/-- Negative involvement is obtained by the same concentration argument after
reversing all pairwise outcomes, which inverts the relevant BT ratio. -/
theorem rtbt_negative_involvement_violation_from_limits
    {β r r' : ℝ} (hβ : 0 < β)
    (hr : 0 < r) (hr' : 0 < r') (hrdrop : r' < r)
    {f g : ℝ → ℝ}
    (hf :
      Tendsto f (𝓝[>] (0 : ℝ))
        (𝓝 ((1 / r) ^ (1 / β) / ((1 / r) ^ (1 / β) + 1))))
    (hg :
      Tendsto g (𝓝[>] (0 : ℝ))
        (𝓝 ((1 / r') ^ (1 / β) / ((1 / r') ^ (1 / β) + 1)))) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ f ε < g ε := by
  have hrr : 1 / r < 1 / r' := by
    exact one_div_lt_one_div_of_lt hr' hrdrop
  have hpow : (1 / r) ^ (1 / β) < (1 / r') ^ (1 / β) := by
    exact Real.rpow_lt_rpow (one_div_pos.mpr hr).le hrr (by positivity)
  have hlim :
      (1 / r) ^ (1 / β) / ((1 / r) ^ (1 / β) + 1) <
        (1 / r') ^ (1 / β) / ((1 / r') ^ (1 / β) + 1) := by
    have hden : 0 < (1 / r) ^ (1 / β) + 1 := by positivity
    have hden' : 0 < (1 / r') ^ (1 / β) + 1 := by positivity
    rw [div_lt_div_iff₀ hden hden']
    nlinarith [hpow]
  obtain ⟨ε, hεpos, hεlt, hlt⟩ := exists_drop_from_right_limit_drop hg hf hlim
  exact ⟨ε, hεpos, hεlt, hlt⟩

end PaperFormalization
