import PaperFormalization.ProfileBorda
import PaperFormalization.WeakProfileBorda
import PaperFormalization.FordZermelo
import PaperFormalization.RTBT

open scoped BigOperators
open scoped Topology
open Filter Set

namespace PaperFormalization

lemma SatisfiesBTDisplayedEquation_normalizeStrength
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {w : α → α → ℝ} {B u : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hBT : SatisfiesBTDisplayedEquation w B u) :
    SatisfiesBTDisplayedEquation w B (normalizeStrength u) := by
  intro x
  have hden_pos := normalizeStrength_den_pos (α := α) hu
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y =>
          w x y *
            (normalizeStrength u x /
              (normalizeStrength u x + normalizeStrength u y)))
        =
      Finset.sum (Finset.univ.erase x)
        (fun y => w x y * (u x / (u x + u y))) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          have hxy : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
          unfold normalizeStrength
          field_simp [hden_pos.ne', hxy]
    _ = B x := hBT x

lemma IsBTStrength_of_displayed_normalized
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {w c : α → α → ℝ} {B u : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hB : ∀ x : α,
      B x = Finset.sum (Finset.univ.erase x) (fun y => c x y))
    (hBT : SatisfiesBTDisplayedEquation w B u) :
    IsBTStrength w c (normalizeStrength u) := by
  refine ⟨normalizeStrength_fullSupport hu, ?_⟩
  intro x
  have hx := SatisfiesBTDisplayedEquation_normalizeStrength hu hBT x
  simpa [hB x] using hx

/-- The analytic limit used in the final step of the RTBT involvement proof:
when the reference `rho_epsilon` concentrates equally on alternatives `0` and
`1`, the RTBT probability of alternative `0` tends to the two-alternative
normalization of the BT strengths. -/
lemma RTBTFromStrength_twoPointReference_tendsto_zero
    {β : ℝ} {u : Fin 3 → ℝ} (hu0 : 0 < u 0) (hu1 : 0 < u 1) :
    Tendsto
      (fun ε : ℝ => RTBTFromStrength β (twoPointReference ε) u 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((u 0) ^ (1 / β) / ((u 0) ^ (1 / β) + (u 1) ^ (1 / β)))) := by
  unfold RTBTFromStrength twoPointReference
  simp [Fin.sum_univ_three]
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hhalf : Tendsto (fun ε : ℝ => (1 - ε) / 2) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 - 0) / 2 : ℝ)) :=
    (tendsto_const_nhds.sub hε).div_const 2
  have hnum : Tendsto (fun ε : ℝ => (1 - ε) / 2 * (u 0) ^ β⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (((1 - 0) / 2 : ℝ) * (u 0) ^ β⁻¹)) :=
    hhalf.mul tendsto_const_nhds
  have hden :
      Tendsto
        (fun ε : ℝ =>
          (1 - ε) / 2 * (u 0) ^ β⁻¹ + (1 - ε) / 2 * (u 1) ^ β⁻¹ +
            ε * (u 2) ^ β⁻¹)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((1 - 0) / 2 : ℝ) * (u 0) ^ β⁻¹ +
          ((1 - 0) / 2 : ℝ) * (u 1) ^ β⁻¹ +
          0 * (u 2) ^ β⁻¹)) :=
    (hnum.add (hhalf.mul tendsto_const_nhds)).add (hε.mul tendsto_const_nhds)
  have hden_ne :
      ((1 - 0) / 2 : ℝ) * (u 0) ^ β⁻¹ +
          ((1 - 0) / 2 : ℝ) * (u 1) ^ β⁻¹ +
          0 * (u 2) ^ β⁻¹ ≠ 0 := by
    have hs0pos : 0 < (u 0) ^ β⁻¹ := Real.rpow_pos_of_pos hu0 _
    have hs1pos : 0 < (u 1) ^ β⁻¹ := Real.rpow_pos_of_pos hu1 _
    apply ne_of_gt
    norm_num
    nlinarith
  have hquot := hnum.div hden hden_ne
  have hquot' :
      Tendsto
        (fun ε : ℝ =>
          (1 - ε) / 2 * (u 0) ^ β⁻¹ /
            ((1 - ε) / 2 * (u 0) ^ β⁻¹ +
              (1 - ε) / 2 * (u 1) ^ β⁻¹ +
              ε * (u 2) ^ β⁻¹))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((1 - 0) / 2 : ℝ) * (u 0) ^ β⁻¹ /
          (((1 - 0) / 2 : ℝ) * (u 0) ^ β⁻¹ +
            ((1 - 0) / 2 : ℝ) * (u 1) ^ β⁻¹ +
            0 * (u 2) ^ β⁻¹))) := by
    simpa [Pi.div_apply] using hquot
  have htarget :
      2⁻¹ * (u 0) ^ β⁻¹ /
          (2⁻¹ * (u 0) ^ β⁻¹ + 2⁻¹ * (u 1) ^ β⁻¹) =
        (u 0) ^ β⁻¹ / ((u 0) ^ β⁻¹ + (u 1) ^ β⁻¹) := by
    have hs0pos : 0 < (u 0) ^ β⁻¹ := Real.rpow_pos_of_pos hu0 _
    have hs1pos : 0 < (u 1) ^ β⁻¹ := Real.rpow_pos_of_pos hu1 _
    field_simp [show (2 : ℝ) ≠ 0 by norm_num,
      ne_of_gt (by positivity : 0 < (u 0) ^ β⁻¹ + (u 1) ^ β⁻¹)]
  simpa [htarget] using hquot'

/-- Candidate order: `0 = a`, `1 = b`, `2 = c`. -/
noncomputable def rtbtInvWeightR : Fin 3 → Fin 3 → ℝ :=
  fun x y => if x = y then 0 else 3

noncomputable def rtbtInvBordaR : Fin 3 → ℝ
  | 0 => 3
  | 1 => 1
  | 2 => 5

noncomputable def rtbtInvWeightRPlus : Fin 3 → Fin 3 → ℝ :=
  fun x y => if x = y then 0 else 4

noncomputable def rtbtInvBordaRPlus : Fin 3 → ℝ
  | 0 => 5
  | 1 => 2
  | 2 => 5

noncomputable def rtbtInvBordaRReverse : Fin 3 → ℝ
  | 0 => 3
  | 1 => 5
  | 2 => 1

noncomputable def rtbtInvBordaRPlusReverse : Fin 3 → ℝ
  | 0 => 3
  | 1 => 6
  | 2 => 3

def rtbtPrefByRank3 (rank : Fin 3 → Nat) (x y : Fin 3) : Bool :=
  decide (rank x < rank y)

def rtbtRankACB : Fin 3 → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 1

def rtbtRankCAB : Fin 3 → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 0

def rtbtRankCBA : Fin 3 → Nat
  | 0 => 2
  | 1 => 1
  | 2 => 0

def rtbtRankABC : Fin 3 → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2

def rtbtPrefACB : Fin 3 → Fin 3 → Bool :=
  rtbtPrefByRank3 rtbtRankACB

def rtbtPrefCAB : Fin 3 → Fin 3 → Bool :=
  rtbtPrefByRank3 rtbtRankCAB

def rtbtPrefCBA : Fin 3 → Fin 3 → Bool :=
  rtbtPrefByRank3 rtbtRankCBA

def rtbtPrefABC : Fin 3 → Fin 3 → Bool :=
  rtbtPrefByRank3 rtbtRankABC

/-- The three-voter profile `R` in the proof of Proposition
`InvolveViolRTBT`: `acb`, `cab`, `cba`. -/
def rtbtInvProfileR : Fin 3 → Fin 3 → Fin 3 → Bool
  | 0 => rtbtPrefACB
  | 1 => rtbtPrefCAB
  | 2 => rtbtPrefCBA

/-- The four-voter profile `R+`, obtained from `R` by adding `abc`. -/
def rtbtInvProfileRPlus : Fin 4 → Fin 3 → Fin 3 → Bool
  | 0 => rtbtPrefACB
  | 1 => rtbtPrefCAB
  | 2 => rtbtPrefCBA
  | 3 => rtbtPrefABC

def rtbtReverseProfile3
    (R : Fin 3 → Fin 3 → Fin 3 → Bool) : Fin 3 → Fin 3 → Fin 3 → Bool :=
  fun i x y => R i y x

def rtbtReverseProfile4
    (R : Fin 4 → Fin 3 → Fin 3 → Bool) : Fin 4 → Fin 3 → Fin 3 → Bool :=
  fun i x y => R i y x

/-- The profile obtained from `R` by reversing every voter ranking. -/
def rtbtInvProfileRReverse : Fin 3 → Fin 3 → Fin 3 → Bool :=
  rtbtReverseProfile3 rtbtInvProfileR

/-- The profile obtained from `R+` by reversing every voter ranking. -/
def rtbtInvProfileRPlusReverse : Fin 4 → Fin 3 → Fin 3 → Bool :=
  rtbtReverseProfile4 rtbtInvProfileRPlus

lemma rtbtPrefABC_asymmetric :
    IsAsymmetricPref rtbtPrefABC := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    simp [rtbtPrefABC, rtbtPrefByRank3, rtbtRankABC] at hxy ⊢

lemma rtbtPrefCBA_asymmetric :
    IsAsymmetricPref rtbtPrefCBA := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    simp [rtbtPrefCBA, rtbtPrefByRank3, rtbtRankCBA] at hxy ⊢

lemma rtbtPrefCBA_eq_reverse_ABC (x y : Fin 3) :
    rtbtPrefCBA x y = rtbtPrefABC y x := by
  fin_cases x <;> fin_cases y <;>
    simp [rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3,
      rtbtRankCBA, rtbtRankABC]

lemma rtbtPrefByRank3_linear
    {rank : Fin 3 → Nat} (hinj : Function.Injective rank) :
    IsLinearPref (rtbtPrefByRank3 rank) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp [rtbtPrefByRank3]
  · intro x y hxy
    simp only [rtbtPrefByRank3, decide_eq_true_eq] at hxy
    simp only [rtbtPrefByRank3, decide_eq_false_iff_not]
    omega
  · intro x y hne
    have hrank : rank x ≠ rank y := fun h => hne (hinj h)
    simp only [rtbtPrefByRank3, decide_eq_true_eq]
    omega
  · intro x y z hxy hyz
    simp only [rtbtPrefByRank3, decide_eq_true_eq] at hxy hyz ⊢
    omega

lemma rtbtRankACB_injective : Function.Injective rtbtRankACB := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rtbtRankACB]

lemma rtbtRankCAB_injective : Function.Injective rtbtRankCAB := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rtbtRankCAB]

lemma rtbtRankCBA_injective : Function.Injective rtbtRankCBA := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rtbtRankCBA]

lemma rtbtRankABC_injective : Function.Injective rtbtRankABC := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [rtbtRankABC]

lemma rtbtPrefACB_linear : IsLinearPref rtbtPrefACB :=
  rtbtPrefByRank3_linear rtbtRankACB_injective

lemma rtbtPrefCAB_linear : IsLinearPref rtbtPrefCAB :=
  rtbtPrefByRank3_linear rtbtRankCAB_injective

lemma rtbtPrefCBA_linear : IsLinearPref rtbtPrefCBA :=
  rtbtPrefByRank3_linear rtbtRankCBA_injective

lemma rtbtPrefABC_linear : IsLinearPref rtbtPrefABC :=
  rtbtPrefByRank3_linear rtbtRankABC_injective

lemma IsLinearPref.reverse {p : Fin 3 → Fin 3 → Bool}
    (h : IsLinearPref p) :
    IsLinearPref (fun x y => p y x) := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro x y hxy
    exact h.2.1 hxy
  · intro x y hne
    rcases h.2.2.1 x y hne with hxy | hyx
    · exact Or.inr hxy
    · exact Or.inl hyx
  · intro x y z hxy hyz
    exact h.2.2.2 hyz hxy

lemma rtbtInvProfileR_linear :
    ∀ i, IsLinearPref (rtbtInvProfileR i) := by
  intro i
  fin_cases i
  · exact rtbtPrefACB_linear
  · exact rtbtPrefCAB_linear
  · exact rtbtPrefCBA_linear

lemma rtbtInvProfileRReverse_linear :
    ∀ i, IsLinearPref (rtbtInvProfileRReverse i) := by
  intro i
  exact (rtbtInvProfileR_linear i).reverse

lemma rtbtInvProfileR_irreflexive :
    IsIrreflexiveProfile rtbtInvProfileR :=
  fun i => (rtbtInvProfileR_linear i).1

lemma rtbtInvProfileRReverse_irreflexive :
    IsIrreflexiveProfile rtbtInvProfileRReverse :=
  fun i => (rtbtInvProfileRReverse_linear i).1

lemma rtbtPrefABC_ranksTop_zero :
    RanksTop rtbtPrefABC 0 := by
  intro y hy
  fin_cases y <;>
    simp [rtbtPrefABC, rtbtPrefByRank3, rtbtRankABC] at hy ⊢

lemma rtbtPrefCBA_ranksBottom_zero :
    RanksBottom rtbtPrefCBA 0 := by
  intro y hy
  fin_cases y <;>
    simp [rtbtPrefCBA, rtbtPrefByRank3, rtbtRankCBA] at hy ⊢

def rtbtStrictCount3 (R : Fin 3 → Fin 3 → Fin 3 → Bool)
    (x y : Fin 3) : ℝ :=
  prefIndicator (R 0 x y) + prefIndicator (R 1 x y) +
    prefIndicator (R 2 x y)

def rtbtStrictCount4 (R : Fin 4 → Fin 3 → Fin 3 → Bool)
    (x y : Fin 3) : ℝ :=
  prefIndicator (R 0 x y) + prefIndicator (R 1 x y) +
    prefIndicator (R 2 x y) + prefIndicator (R 3 x y)

lemma strictCount_rtbtInvProfileR :
    strictCount rtbtInvProfileR = rtbtStrictCount3 rtbtInvProfileR := by
  funext x y
  simp [strictCount, rtbtStrictCount3, Fin.sum_univ_three]

lemma strictCount_addVoter_rtbtInvProfileR :
    strictCount (addVoterProfile rtbtInvProfileR rtbtPrefABC) =
      rtbtStrictCount4 rtbtInvProfileRPlus := by
  funext x y
  rw [strictCount_addVoterProfile]
  rw [congrFun (congrFun strictCount_rtbtInvProfileR x) y]
  rfl

lemma strictCount_rtbtInvProfileRReverse :
    strictCount rtbtInvProfileRReverse =
      rtbtStrictCount3 rtbtInvProfileRReverse := by
  funext x y
  simp [strictCount, rtbtStrictCount3, Fin.sum_univ_three]

lemma strictCount_addVoter_rtbtInvProfileRReverse :
    strictCount (addVoterProfile rtbtInvProfileRReverse rtbtPrefCBA) =
      rtbtStrictCount4 rtbtInvProfileRPlusReverse := by
  funext x y
  rw [strictCount_addVoterProfile]
  rw [congrFun (congrFun strictCount_rtbtInvProfileRReverse x) y]
  simp only [rtbtStrictCount3, rtbtStrictCount4,
    rtbtInvProfileRPlusReverse, rtbtReverseProfile4, rtbtInvProfileRPlus,
    rtbtInvProfileRReverse, rtbtReverseProfile3, rtbtInvProfileR]
  simp only [rtbtPrefCBA_eq_reverse_ABC]

lemma rtbtStrictCount3_nonneg
    (R : Fin 3 → Fin 3 → Fin 3 → Bool) (x y : Fin 3) :
    0 ≤ rtbtStrictCount3 R x y := by
  unfold rtbtStrictCount3
  nlinarith [prefIndicator_nonneg (R 0 x y),
    prefIndicator_nonneg (R 1 x y), prefIndicator_nonneg (R 2 x y)]

lemma rtbtStrictCount4_nonneg
    (R : Fin 4 → Fin 3 → Fin 3 → Bool) (x y : Fin 3) :
    0 ≤ rtbtStrictCount4 R x y := by
  unfold rtbtStrictCount4
  nlinarith [prefIndicator_nonneg (R 0 x y),
    prefIndicator_nonneg (R 1 x y), prefIndicator_nonneg (R 2 x y),
    prefIndicator_nonneg (R 3 x y)]

noncomputable def rtbtProfileBorda3
    (R : Fin 3 → Fin 3 → Fin 3 → Bool) : Fin 3 → ℝ :=
  fun x => rtbtStrictCount3 R x 0 + rtbtStrictCount3 R x 1 +
    rtbtStrictCount3 R x 2

noncomputable def rtbtProfileBorda4
    (R : Fin 4 → Fin 3 → Fin 3 → Bool) : Fin 3 → ℝ :=
  fun x => rtbtStrictCount4 R x 0 + rtbtStrictCount4 R x 1 +
    rtbtStrictCount4 R x 2

noncomputable def rtbtProfileWeight3
    (R : Fin 3 → Fin 3 → Fin 3 → Bool) : Fin 3 → Fin 3 → ℝ :=
  fun x y => rtbtStrictCount3 R x y + rtbtStrictCount3 R y x

noncomputable def rtbtProfileWeight4
    (R : Fin 4 → Fin 3 → Fin 3 → Bool) : Fin 3 → Fin 3 → ℝ :=
  fun x y => rtbtStrictCount4 R x y + rtbtStrictCount4 R y x

noncomputable def rtbtProfileMargin3
    (R : Fin 3 → Fin 3 → Fin 3 → Bool) : Fin 3 → Fin 3 → ℝ :=
  fun x y => (rtbtStrictCount3 R x y - rtbtStrictCount3 R y x) / 3

noncomputable def rtbtProfileMargin4
    (R : Fin 4 → Fin 3 → Fin 3 → Bool) : Fin 3 → Fin 3 → ℝ :=
  fun x y => (rtbtStrictCount4 R x y - rtbtStrictCount4 R y x) / 4

lemma rtbtInvProfileR_borda_eq :
    rtbtProfileBorda3 rtbtInvProfileR = rtbtInvBordaR := by
  funext x
  fin_cases x <;>
    norm_num [rtbtProfileBorda3, rtbtStrictCount3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator, rtbtInvBordaR]

lemma rtbtInvProfileRPlus_borda_eq :
    rtbtProfileBorda4 rtbtInvProfileRPlus = rtbtInvBordaRPlus := by
  funext x
  fin_cases x <;>
    norm_num [rtbtProfileBorda4, rtbtStrictCount4, rtbtInvProfileRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC, prefIndicator,
      rtbtInvBordaRPlus]

lemma rtbtInvProfileRReverse_borda_eq :
    rtbtProfileBorda3 rtbtInvProfileRReverse = rtbtInvBordaRReverse := by
  funext x
  fin_cases x <;>
    norm_num [rtbtProfileBorda3, rtbtStrictCount3, rtbtInvProfileRReverse,
      rtbtReverseProfile3, rtbtInvProfileR, rtbtPrefACB, rtbtPrefCAB,
      rtbtPrefCBA, rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB, rtbtRankCBA,
      prefIndicator, rtbtInvBordaRReverse]

lemma rtbtInvProfileRPlusReverse_borda_eq :
    rtbtProfileBorda4 rtbtInvProfileRPlusReverse =
      rtbtInvBordaRPlusReverse := by
  funext x
  fin_cases x <;>
    norm_num [rtbtProfileBorda4, rtbtStrictCount4,
      rtbtInvProfileRPlusReverse, rtbtReverseProfile4, rtbtInvProfileRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC,
      rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC,
      prefIndicator, rtbtInvBordaRPlusReverse]

lemma rtbtInvProfileR_borda_erase_eq (x : Fin 3) :
    rtbtInvBordaR x =
      Finset.sum (Finset.univ.erase x)
        (fun y => rtbtStrictCount3 rtbtInvProfileR x y) := by
  have hzero : rtbtStrictCount3 rtbtInvProfileR x x = 0 := by
    fin_cases x <;>
      norm_num [rtbtStrictCount3, rtbtInvProfileR, rtbtPrefACB,
        rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3, rtbtRankACB,
        rtbtRankCAB, rtbtRankCBA, prefIndicator]
  rw [Finset.sum_erase (s := Finset.univ)
    (f := fun y => rtbtStrictCount3 rtbtInvProfileR x y) hzero]
  fin_cases x <;>
    norm_num [Fin.sum_univ_three, rtbtStrictCount3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator, rtbtInvBordaR]

lemma rtbtInvProfileRPlus_borda_erase_eq (x : Fin 3) :
    rtbtInvBordaRPlus x =
      Finset.sum (Finset.univ.erase x)
        (fun y => rtbtStrictCount4 rtbtInvProfileRPlus x y) := by
  have hzero : rtbtStrictCount4 rtbtInvProfileRPlus x x = 0 := by
    fin_cases x <;>
      norm_num [rtbtStrictCount4, rtbtInvProfileRPlus, rtbtPrefACB,
        rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3,
        rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC, prefIndicator]
  rw [Finset.sum_erase (s := Finset.univ)
    (f := fun y => rtbtStrictCount4 rtbtInvProfileRPlus x y) hzero]
  fin_cases x <;>
    norm_num [Fin.sum_univ_three, rtbtStrictCount4, rtbtInvProfileRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC, prefIndicator,
      rtbtInvBordaRPlus]

lemma rtbtInvProfileRReverse_borda_erase_eq (x : Fin 3) :
    rtbtInvBordaRReverse x =
      Finset.sum (Finset.univ.erase x)
        (fun y => rtbtStrictCount3 rtbtInvProfileRReverse x y) := by
  have hzero : rtbtStrictCount3 rtbtInvProfileRReverse x x = 0 := by
    fin_cases x <;>
      norm_num [rtbtStrictCount3, rtbtInvProfileRReverse,
        rtbtReverseProfile3, rtbtInvProfileR, rtbtPrefACB, rtbtPrefCAB,
        rtbtPrefCBA, rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB,
        rtbtRankCBA, prefIndicator]
  rw [Finset.sum_erase (s := Finset.univ)
    (f := fun y => rtbtStrictCount3 rtbtInvProfileRReverse x y) hzero]
  fin_cases x
  · norm_num [Fin.sum_univ_three, rtbtStrictCount3,
      rtbtInvProfileRReverse, rtbtReverseProfile3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator,
      rtbtInvBordaRReverse]
  · norm_num [Fin.sum_univ_three, rtbtStrictCount3,
      rtbtInvProfileRReverse, rtbtReverseProfile3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator,
      rtbtInvBordaRReverse]
  · norm_num [Fin.sum_univ_three, rtbtStrictCount3,
      rtbtInvProfileRReverse, rtbtReverseProfile3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator,
      rtbtInvBordaRReverse]
    have hcard :
        ((Finset.univ.filter (fun x : Fin 3 => rtbtRankACB x = 0)).card : ℕ) = 1 := by
      decide
    have hcardR :
        (1 : ℝ) =
          ((Finset.univ.filter (fun x : Fin 3 => rtbtRankACB x = 0)).card : ℝ) := by
      norm_num [hcard]
    simpa [rtbtRankACB] using hcardR

lemma rtbtInvProfileRPlusReverse_borda_erase_eq (x : Fin 3) :
    rtbtInvBordaRPlusReverse x =
      Finset.sum (Finset.univ.erase x)
        (fun y => rtbtStrictCount4 rtbtInvProfileRPlusReverse x y) := by
  have hzero : rtbtStrictCount4 rtbtInvProfileRPlusReverse x x = 0 := by
    fin_cases x <;>
      norm_num [rtbtStrictCount4, rtbtInvProfileRPlusReverse,
        rtbtReverseProfile4, rtbtInvProfileRPlus, rtbtPrefACB, rtbtPrefCAB,
        rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3, rtbtRankACB,
        rtbtRankCAB, rtbtRankCBA, rtbtRankABC, prefIndicator]
  rw [Finset.sum_erase (s := Finset.univ)
    (f := fun y => rtbtStrictCount4 rtbtInvProfileRPlusReverse x y) hzero]
  fin_cases x <;>
    norm_num [Fin.sum_univ_three, rtbtStrictCount4,
      rtbtInvProfileRPlusReverse, rtbtReverseProfile4, rtbtInvProfileRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC,
      rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC,
      prefIndicator, rtbtInvBordaRPlusReverse]

lemma rtbtInvProfileR_weight_eq :
    rtbtProfileWeight3 rtbtInvProfileR = rtbtInvWeightR := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [rtbtProfileWeight3, rtbtStrictCount3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator, rtbtInvWeightR]

lemma rtbtInvProfileRPlus_weight_eq :
    rtbtProfileWeight4 rtbtInvProfileRPlus = rtbtInvWeightRPlus := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [rtbtProfileWeight4, rtbtStrictCount4, rtbtInvProfileRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC, prefIndicator,
      rtbtInvWeightRPlus]

lemma rtbtInvProfileRReverse_weight_eq :
    rtbtProfileWeight3 rtbtInvProfileRReverse = rtbtInvWeightR := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [rtbtProfileWeight3, rtbtStrictCount3,
      rtbtInvProfileRReverse, rtbtReverseProfile3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator, rtbtInvWeightR]

lemma rtbtInvProfileRPlusReverse_weight_eq :
    rtbtProfileWeight4 rtbtInvProfileRPlusReverse = rtbtInvWeightRPlus := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [rtbtProfileWeight4, rtbtStrictCount4,
      rtbtInvProfileRPlusReverse, rtbtReverseProfile4, rtbtInvProfileRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC,
      rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC,
      prefIndicator, rtbtInvWeightRPlus]

/-- Normalized margin matrix for the positive-involvement RTBT witness `R`
from the appendix proof. Candidate order is `0 = a`, `1 = b`, `2 = c`. -/
noncomputable def rtbtInvMarginR : Fin 3 → Fin 3 → ℝ
  | 0, 1 => 1 / 3
  | 1, 0 => -1 / 3
  | 0, 2 => -1 / 3
  | 2, 0 => 1 / 3
  | 1, 2 => -1
  | 2, 1 => 1
  | _, _ => 0

/-- Normalized margin matrix for `R+`, obtained from `R` by adding the voter
with ranking `abc`. -/
noncomputable def rtbtInvMarginRPlus : Fin 3 → Fin 3 → ℝ
  | 0, 1 => 1 / 2
  | 1, 0 => -1 / 2
  | 0, 2 => 0
  | 2, 0 => 0
  | 1, 2 => -1 / 2
  | 2, 1 => 1 / 2
  | _, _ => 0

noncomputable def rtbtInvMarginRReverse : Fin 3 → Fin 3 → ℝ :=
  fun x y => -rtbtInvMarginR x y

noncomputable def rtbtInvMarginRPlusReverse : Fin 3 → Fin 3 → ℝ :=
  fun x y => -rtbtInvMarginRPlus x y

lemma rtbtInvProfileR_margin_eq :
    rtbtProfileMargin3 rtbtInvProfileR = rtbtInvMarginR := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [rtbtProfileMargin3, rtbtStrictCount3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator, rtbtInvMarginR]

lemma rtbtInvProfileRPlus_margin_eq :
    rtbtProfileMargin4 rtbtInvProfileRPlus = rtbtInvMarginRPlus := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [rtbtProfileMargin4, rtbtStrictCount4, rtbtInvProfileRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC, prefIndicator,
      rtbtInvMarginRPlus]

lemma rtbtInvProfileRReverse_margin_eq :
    rtbtProfileMargin3 rtbtInvProfileRReverse = rtbtInvMarginRReverse := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [rtbtProfileMargin3, rtbtStrictCount3,
      rtbtInvProfileRReverse, rtbtReverseProfile3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3,
      rtbtRankACB, rtbtRankCAB, rtbtRankCBA, prefIndicator,
      rtbtInvMarginRReverse, rtbtInvMarginR]

lemma rtbtInvProfileRPlusReverse_margin_eq :
    rtbtProfileMargin4 rtbtInvProfileRPlusReverse =
      rtbtInvMarginRPlusReverse := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    norm_num [rtbtProfileMargin4, rtbtStrictCount4,
      rtbtInvProfileRPlusReverse, rtbtReverseProfile4, rtbtInvProfileRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC,
      rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC,
      prefIndicator, rtbtInvMarginRPlusReverse, rtbtInvMarginRPlus]

lemma rtbtInvMarginR_normalized :
    IsNormalizedMarginMatrix rtbtInvMarginR := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [rtbtInvMarginR]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [rtbtInvMarginR] <;> norm_num
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [rtbtInvMarginR] <;> norm_num

lemma rtbtInvMarginRPlus_normalized :
    IsNormalizedMarginMatrix rtbtInvMarginRPlus := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [rtbtInvMarginRPlus]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [rtbtInvMarginRPlus] <;> norm_num
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [rtbtInvMarginRPlus] <;> norm_num

lemma rtbtInvMarginRReverse_normalized :
    IsNormalizedMarginMatrix rtbtInvMarginRReverse := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [rtbtInvMarginRReverse, rtbtInvMarginR]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [rtbtInvMarginRReverse, rtbtInvMarginR] <;> norm_num
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [rtbtInvMarginRReverse, rtbtInvMarginR] <;> norm_num

lemma rtbtInvMarginRPlusReverse_normalized :
    IsNormalizedMarginMatrix rtbtInvMarginRPlusReverse := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp [rtbtInvMarginRPlusReverse, rtbtInvMarginRPlus]
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [rtbtInvMarginRPlusReverse, rtbtInvMarginRPlus] <;> norm_num
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [rtbtInvMarginRPlusReverse, rtbtInvMarginRPlus] <;> norm_num

def rtbtPositiveLinearAddsTopWitness
    (M M' : Fin 3 → Fin 3 → ℝ) (x : Fin 3) : Prop :=
  M = rtbtInvMarginR ∧ M' = rtbtInvMarginRPlus ∧ x = 0

def rtbtNegativeLinearAddsBottomWitness
    (M M' : Fin 3 → Fin 3 → ℝ) (x : Fin 3) : Prop :=
  M = rtbtInvMarginRReverse ∧ M' = rtbtInvMarginRPlusReverse ∧ x = 0

lemma rtbtPositiveLinearAddsTopWitness_here :
    rtbtPositiveLinearAddsTopWitness rtbtInvMarginR rtbtInvMarginRPlus 0 := by
  exact ⟨rfl, rfl, rfl⟩

lemma rtbtNegativeLinearAddsBottomWitness_here :
    rtbtNegativeLinearAddsBottomWitness
      rtbtInvMarginRReverse rtbtInvMarginRPlusReverse 0 := by
  exact ⟨rfl, rfl, rfl⟩

lemma twoPointReference_fullSupport {ε : ℝ}
    (hεpos : 0 < ε) (hεlt : ε < 1) :
    IsFullSupportLottery (twoPointReference ε) := by
  constructor
  · intro x
    fin_cases x <;> simp [twoPointReference] <;> linarith
  · simp [twoPointReference, Fin.sum_univ_three]

def rtbtProfileEdge3
    (R : Fin 3 → Fin 3 → Fin 3 → Bool) (x y : Fin 3) : Prop :=
  ∃ i : Fin 3, R i x y = true

def rtbtProfileEdge4
    (R : Fin 4 → Fin 3 → Fin 3 → Bool) (x y : Fin 3) : Prop :=
  ∃ i : Fin 4, R i x y = true

/-- A concrete directed edge certificate for the graph of the three-voter
profile `R` in the paper proof.  The alternatives are `0 = a`, `1 = b`,
`2 = c`, and `edge x y` means some voter ranks `x` above `y`. -/
def rtbtInvEdgeR : Fin 3 → Fin 3 → Prop
  | 0, 1 => True
  | 0, 2 => True
  | 1, 0 => True
  | 2, 0 => True
  | 2, 1 => True
  | _, _ => False

def rtbtInvEdgeRPlus : Fin 3 → Fin 3 → Prop
  | 0, 1 => True
  | 0, 2 => True
  | 1, 0 => True
  | 1, 2 => True
  | 2, 0 => True
  | 2, 1 => True
  | _, _ => False

def rtbtInvEdgeRReverse : Fin 3 → Fin 3 → Prop :=
  fun x y => rtbtInvEdgeR y x

def rtbtInvEdgeRPlusReverse : Fin 3 → Fin 3 → Prop :=
  fun x y => rtbtInvEdgeRPlus y x

lemma rtbtInvProfileR_edge_iff (x y : Fin 3) :
    rtbtProfileEdge3 rtbtInvProfileR x y ↔ rtbtInvEdgeR x y := by
  fin_cases x <;> fin_cases y <;>
    simp [rtbtProfileEdge3, rtbtInvProfileR, rtbtInvEdgeR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA] <;>
    decide

lemma rtbtInvProfileRPlus_edge_iff (x y : Fin 3) :
    rtbtProfileEdge4 rtbtInvProfileRPlus x y ↔ rtbtInvEdgeRPlus x y := by
  fin_cases x <;> fin_cases y <;>
    simp [rtbtProfileEdge4, rtbtInvProfileRPlus, rtbtInvEdgeRPlus,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC] <;>
    decide

lemma rtbtInvProfileRReverse_edge_iff (x y : Fin 3) :
    rtbtProfileEdge3 rtbtInvProfileRReverse x y ↔
      rtbtInvEdgeRReverse x y := by
  fin_cases x <;> fin_cases y <;>
    simp [rtbtProfileEdge3, rtbtInvProfileRReverse, rtbtInvEdgeRReverse,
      rtbtInvEdgeR, rtbtReverseProfile3, rtbtInvProfileR,
      rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA] <;>
    decide

lemma rtbtInvProfileRPlusReverse_edge_iff (x y : Fin 3) :
    rtbtProfileEdge4 rtbtInvProfileRPlusReverse x y ↔
      rtbtInvEdgeRPlusReverse x y := by
  fin_cases x <;> fin_cases y <;>
    simp [rtbtProfileEdge4, rtbtInvProfileRPlusReverse,
      rtbtInvEdgeRPlusReverse, rtbtInvEdgeRPlus, rtbtReverseProfile4,
      rtbtInvProfileRPlus, rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA,
      rtbtPrefABC] <;>
    decide

lemma rtbtInvGraphR_stronglyConnected :
    stronglyConnectedByShortPaths rtbtInvEdgeR := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp [hasDirectedPathLengthAtMostTwo, rtbtInvEdgeR]
  exact ⟨0, by simp, by simp⟩

lemma rtbtInvGraphRPlus_stronglyConnected :
    stronglyConnectedByShortPaths rtbtInvEdgeRPlus := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp [hasDirectedPathLengthAtMostTwo, rtbtInvEdgeRPlus]

lemma rtbtInvGraphRReverse_stronglyConnected :
    stronglyConnectedByShortPaths rtbtInvEdgeRReverse := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp [hasDirectedPathLengthAtMostTwo, rtbtInvEdgeRReverse, rtbtInvEdgeR]
  exact ⟨0, by simp, by simp⟩

lemma rtbtInvGraphRPlusReverse_stronglyConnected :
    stronglyConnectedByShortPaths rtbtInvEdgeRPlusReverse := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp [hasDirectedPathLengthAtMostTwo, rtbtInvEdgeRPlusReverse,
      rtbtInvEdgeRPlus]

lemma rtbtInvProfileR_stronglyConnected :
    stronglyConnectedByShortPaths (rtbtProfileEdge3 rtbtInvProfileR) :=
  stronglyConnectedByShortPaths_congr
    (fun x y => (rtbtInvProfileR_edge_iff x y).symm)
    rtbtInvGraphR_stronglyConnected

lemma rtbtInvProfileRPlus_stronglyConnected :
    stronglyConnectedByShortPaths (rtbtProfileEdge4 rtbtInvProfileRPlus) :=
  stronglyConnectedByShortPaths_congr
    (fun x y => (rtbtInvProfileRPlus_edge_iff x y).symm)
    rtbtInvGraphRPlus_stronglyConnected

lemma rtbtInvProfileRReverse_stronglyConnected :
    stronglyConnectedByShortPaths (rtbtProfileEdge3 rtbtInvProfileRReverse) :=
  stronglyConnectedByShortPaths_congr
    (fun x y => (rtbtInvProfileRReverse_edge_iff x y).symm)
    rtbtInvGraphRReverse_stronglyConnected

lemma rtbtInvProfileRPlusReverse_stronglyConnected :
    stronglyConnectedByShortPaths
      (rtbtProfileEdge4 rtbtInvProfileRPlusReverse) :=
  stronglyConnectedByShortPaths_congr
    (fun x y => (rtbtInvProfileRPlusReverse_edge_iff x y).symm)
    rtbtInvGraphRPlusReverse_stronglyConnected

lemma rtbtInvProfileR_fordCountMatrix :
    IsFordCountMatrix (rtbtStrictCount3 rtbtInvProfileR) := by
  constructor
  · intro x
    fin_cases x <;>
      norm_num [rtbtStrictCount3, rtbtInvProfileR, rtbtPrefACB,
        rtbtPrefCAB, rtbtPrefCBA, rtbtPrefByRank3, rtbtRankACB,
        rtbtRankCAB, rtbtRankCBA, prefIndicator]
  · intro x y
    exact rtbtStrictCount3_nonneg rtbtInvProfileR x y

lemma rtbtInvProfileRPlus_fordCountMatrix :
    IsFordCountMatrix (rtbtStrictCount4 rtbtInvProfileRPlus) := by
  constructor
  · intro x
    fin_cases x <;>
      norm_num [rtbtStrictCount4, rtbtInvProfileRPlus, rtbtPrefACB,
        rtbtPrefCAB, rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3,
        rtbtRankACB, rtbtRankCAB, rtbtRankCBA, rtbtRankABC, prefIndicator]
  · intro x y
    exact rtbtStrictCount4_nonneg rtbtInvProfileRPlus x y

lemma rtbtInvProfileRReverse_fordCountMatrix :
    IsFordCountMatrix (rtbtStrictCount3 rtbtInvProfileRReverse) := by
  constructor
  · intro x
    fin_cases x <;>
      norm_num [rtbtStrictCount3, rtbtInvProfileRReverse,
        rtbtReverseProfile3, rtbtInvProfileR, rtbtPrefACB, rtbtPrefCAB,
        rtbtPrefCBA, rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB,
        rtbtRankCBA, prefIndicator]
  · intro x y
    exact rtbtStrictCount3_nonneg rtbtInvProfileRReverse x y

lemma rtbtInvProfileRPlusReverse_fordCountMatrix :
    IsFordCountMatrix (rtbtStrictCount4 rtbtInvProfileRPlusReverse) := by
  constructor
  · intro x
    fin_cases x <;>
      norm_num [rtbtStrictCount4, rtbtInvProfileRPlusReverse,
        rtbtReverseProfile4, rtbtInvProfileRPlus, rtbtPrefACB, rtbtPrefCAB,
        rtbtPrefCBA, rtbtPrefABC, rtbtPrefByRank3, rtbtRankACB,
        rtbtRankCAB, rtbtRankCBA, rtbtRankABC, prefIndicator]
  · intro x y
    exact rtbtStrictCount4_nonneg rtbtInvProfileRPlusReverse x y

lemma rtbtInvProfileR_fordCountEdge_iff (x y : Fin 3) :
    fordCountEdge (rtbtStrictCount3 rtbtInvProfileR) x y ↔
      rtbtProfileEdge3 rtbtInvProfileR x y := by
  rw [rtbtInvProfileR_edge_iff x y]
  fin_cases x <;> fin_cases y <;>
    norm_num [fordCountEdge, rtbtStrictCount3, rtbtInvProfileR,
      rtbtInvEdgeR, rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA,
      rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB, rtbtRankCBA,
      prefIndicator]

lemma rtbtInvProfileRPlus_fordCountEdge_iff (x y : Fin 3) :
    fordCountEdge (rtbtStrictCount4 rtbtInvProfileRPlus) x y ↔
      rtbtProfileEdge4 rtbtInvProfileRPlus x y := by
  rw [rtbtInvProfileRPlus_edge_iff x y]
  fin_cases x <;> fin_cases y <;>
    norm_num [fordCountEdge, rtbtStrictCount4, rtbtInvProfileRPlus,
      rtbtInvEdgeRPlus, rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA,
      rtbtPrefABC, rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB,
      rtbtRankCBA, rtbtRankABC, prefIndicator]

lemma rtbtInvProfileRReverse_fordCountEdge_iff (x y : Fin 3) :
    fordCountEdge (rtbtStrictCount3 rtbtInvProfileRReverse) x y ↔
      rtbtProfileEdge3 rtbtInvProfileRReverse x y := by
  rw [rtbtInvProfileRReverse_edge_iff x y]
  fin_cases x <;> fin_cases y <;>
    norm_num [fordCountEdge, rtbtStrictCount3, rtbtInvProfileRReverse,
      rtbtInvEdgeRReverse, rtbtInvEdgeR, rtbtReverseProfile3,
      rtbtInvProfileR, rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA,
      rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB, rtbtRankCBA,
      prefIndicator]

lemma rtbtInvProfileRPlusReverse_fordCountEdge_iff (x y : Fin 3) :
    fordCountEdge (rtbtStrictCount4 rtbtInvProfileRPlusReverse) x y ↔
      rtbtProfileEdge4 rtbtInvProfileRPlusReverse x y := by
  rw [rtbtInvProfileRPlusReverse_edge_iff x y]
  fin_cases x <;> fin_cases y <;>
    norm_num [fordCountEdge, rtbtStrictCount4, rtbtInvProfileRPlusReverse,
      rtbtInvEdgeRPlusReverse, rtbtInvEdgeRPlus, rtbtReverseProfile4,
      rtbtInvProfileRPlus, rtbtPrefACB, rtbtPrefCAB, rtbtPrefCBA,
      rtbtPrefABC, rtbtPrefByRank3, rtbtRankACB, rtbtRankCAB,
      rtbtRankCBA, rtbtRankABC, prefIndicator]

lemma rtbtInvProfileR_fordStronglyConnected :
    FordStronglyConnected (rtbtStrictCount3 rtbtInvProfileR) :=
  FordStronglyConnected_of_shortPaths <|
    stronglyConnectedByShortPaths_congr
      (fun x y => (rtbtInvProfileR_fordCountEdge_iff x y).symm)
      rtbtInvProfileR_stronglyConnected

lemma rtbtInvProfileRPlus_fordStronglyConnected :
    FordStronglyConnected (rtbtStrictCount4 rtbtInvProfileRPlus) :=
  FordStronglyConnected_of_shortPaths <|
    stronglyConnectedByShortPaths_congr
      (fun x y => (rtbtInvProfileRPlus_fordCountEdge_iff x y).symm)
      rtbtInvProfileRPlus_stronglyConnected

lemma rtbtInvProfileRReverse_fordStronglyConnected :
    FordStronglyConnected (rtbtStrictCount3 rtbtInvProfileRReverse) :=
  FordStronglyConnected_of_shortPaths <|
    stronglyConnectedByShortPaths_congr
      (fun x y => (rtbtInvProfileRReverse_fordCountEdge_iff x y).symm)
      rtbtInvProfileRReverse_stronglyConnected

lemma rtbtInvProfileRPlusReverse_fordStronglyConnected :
    FordStronglyConnected (rtbtStrictCount4 rtbtInvProfileRPlusReverse) :=
  FordStronglyConnected_of_shortPaths <|
    stronglyConnectedByShortPaths_congr
      (fun x y => (rtbtInvProfileRPlusReverse_fordCountEdge_iff x y).symm)
      rtbtInvProfileRPlusReverse_stronglyConnected

lemma rtbtInvProfileR_actual_fordStronglyConnected :
    FordStronglyConnected (strictCount rtbtInvProfileR) := by
  simpa only [strictCount_rtbtInvProfileR] using
    rtbtInvProfileR_fordStronglyConnected

lemma rtbtInvProfileR_addVoter_actual_fordStronglyConnected :
    FordStronglyConnected
      (strictCount (addVoterProfile rtbtInvProfileR rtbtPrefABC)) := by
  simpa only [strictCount_addVoter_rtbtInvProfileR] using
    rtbtInvProfileRPlus_fordStronglyConnected

lemma rtbtInvProfileRReverse_actual_fordStronglyConnected :
    FordStronglyConnected (strictCount rtbtInvProfileRReverse) := by
  simpa only [strictCount_rtbtInvProfileRReverse] using
    rtbtInvProfileRReverse_fordStronglyConnected

lemma rtbtInvProfileRReverse_addVoter_actual_fordStronglyConnected :
    FordStronglyConnected
      (strictCount
        (addVoterProfile rtbtInvProfileRReverse rtbtPrefCBA)) := by
  simpa only [strictCount_addVoter_rtbtInvProfileRReverse] using
    rtbtInvProfileRPlusReverse_fordStronglyConnected

lemma rtbtInvProfileR_fordPairTotal_eq :
    fordPairTotal (rtbtStrictCount3 rtbtInvProfileR) = rtbtInvWeightR := by
  calc
    fordPairTotal (rtbtStrictCount3 rtbtInvProfileR) =
        rtbtProfileWeight3 rtbtInvProfileR := by
      funext x y
      rfl
    _ = rtbtInvWeightR := rtbtInvProfileR_weight_eq

lemma rtbtInvProfileRPlus_fordPairTotal_eq :
    fordPairTotal (rtbtStrictCount4 rtbtInvProfileRPlus) =
      rtbtInvWeightRPlus := by
  calc
    fordPairTotal (rtbtStrictCount4 rtbtInvProfileRPlus) =
        rtbtProfileWeight4 rtbtInvProfileRPlus := by
      funext x y
      rfl
    _ = rtbtInvWeightRPlus := rtbtInvProfileRPlus_weight_eq

lemma rtbtInvProfileRReverse_fordPairTotal_eq :
    fordPairTotal (rtbtStrictCount3 rtbtInvProfileRReverse) =
      rtbtInvWeightR := by
  calc
    fordPairTotal (rtbtStrictCount3 rtbtInvProfileRReverse) =
        rtbtProfileWeight3 rtbtInvProfileRReverse := by
      funext x y
      rfl
    _ = rtbtInvWeightR := rtbtInvProfileRReverse_weight_eq

lemma rtbtInvProfileRPlusReverse_fordPairTotal_eq :
    fordPairTotal (rtbtStrictCount4 rtbtInvProfileRPlusReverse) =
      rtbtInvWeightRPlus := by
  calc
    fordPairTotal (rtbtStrictCount4 rtbtInvProfileRPlusReverse) =
        rtbtProfileWeight4 rtbtInvProfileRPlusReverse := by
      funext x y
      rfl
    _ = rtbtInvWeightRPlus := rtbtInvProfileRPlusReverse_weight_eq

theorem exists_rtbtInvProfileR_DPOasRTBT_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β) {ρ : Fin 3 → ℝ}
    (hρ : ∀ x : Fin 3, 0 < ρ x) :
    ∃ u : Fin 3 → ℝ,
      HasBTPropCertificate rtbtInvWeightR
        (rtbtStrictCount3 rtbtInvProfileR) u ∧
        dpoArgmaxSet β (rtbtStrictCount3 rtbtInvProfileR) ρ =
          ({RTBTFromStrength β ρ u} : Set (Fin 3 → ℝ)) := by
  rcases DPOasRTBT_from_ford_zermelo hFord hβ hρ
      rtbtInvProfileR_fordCountMatrix
      rtbtInvProfileR_fordStronglyConnected with
    ⟨u, hBT, hDPO⟩
  exact ⟨u, by simpa [rtbtInvProfileR_fordPairTotal_eq] using hBT, hDPO⟩

theorem exists_rtbtInvProfileRPlus_DPOasRTBT_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β) {ρ : Fin 3 → ℝ}
    (hρ : ∀ x : Fin 3, 0 < ρ x) :
    ∃ u : Fin 3 → ℝ,
      HasBTPropCertificate rtbtInvWeightRPlus
        (rtbtStrictCount4 rtbtInvProfileRPlus) u ∧
        dpoArgmaxSet β (rtbtStrictCount4 rtbtInvProfileRPlus) ρ =
          ({RTBTFromStrength β ρ u} : Set (Fin 3 → ℝ)) := by
  rcases DPOasRTBT_from_ford_zermelo hFord hβ hρ
      rtbtInvProfileRPlus_fordCountMatrix
      rtbtInvProfileRPlus_fordStronglyConnected with
    ⟨u, hBT, hDPO⟩
  exact ⟨u, by simpa [rtbtInvProfileRPlus_fordPairTotal_eq] using hBT,
    hDPO⟩

theorem exists_rtbtInvProfileRReverse_DPOasRTBT_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β) {ρ : Fin 3 → ℝ}
    (hρ : ∀ x : Fin 3, 0 < ρ x) :
    ∃ u : Fin 3 → ℝ,
      HasBTPropCertificate rtbtInvWeightR
        (rtbtStrictCount3 rtbtInvProfileRReverse) u ∧
        dpoArgmaxSet β (rtbtStrictCount3 rtbtInvProfileRReverse) ρ =
          ({RTBTFromStrength β ρ u} : Set (Fin 3 → ℝ)) := by
  rcases DPOasRTBT_from_ford_zermelo hFord hβ hρ
      rtbtInvProfileRReverse_fordCountMatrix
      rtbtInvProfileRReverse_fordStronglyConnected with
    ⟨u, hBT, hDPO⟩
  exact ⟨u, by simpa [rtbtInvProfileRReverse_fordPairTotal_eq] using hBT,
    hDPO⟩

theorem exists_rtbtInvProfileRPlusReverse_DPOasRTBT_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β) {ρ : Fin 3 → ℝ}
    (hρ : ∀ x : Fin 3, 0 < ρ x) :
    ∃ u : Fin 3 → ℝ,
      HasBTPropCertificate rtbtInvWeightRPlus
        (rtbtStrictCount4 rtbtInvProfileRPlusReverse) u ∧
        dpoArgmaxSet β (rtbtStrictCount4 rtbtInvProfileRPlusReverse) ρ =
          ({RTBTFromStrength β ρ u} : Set (Fin 3 → ℝ)) := by
  rcases DPOasRTBT_from_ford_zermelo hFord hβ hρ
      rtbtInvProfileRPlusReverse_fordCountMatrix
      rtbtInvProfileRPlusReverse_fordStronglyConnected with
    ⟨u, hBT, hDPO⟩
  exact ⟨u,
    by simpa [rtbtInvProfileRPlusReverse_fordPairTotal_eq] using hBT,
    hDPO⟩

noncomputable def rtbtInvStrengthR (r : ℝ) : Fin 3 → ℝ
  | 0 => r
  | 1 => 1
  | 2 => r ^ 2

noncomputable def rtbtInvStrengthRPlus : Fin 3 → ℝ
  | 0 => 3
  | 1 => 1
  | 2 => 3

noncomputable def rtbtInvStrengthRReverse (r : ℝ) : Fin 3 → ℝ
  | 0 => 1 / r
  | 1 => 1
  | 2 => 1 / r ^ 2

noncomputable def rtbtInvStrengthRPlusReverse : Fin 3 → ℝ
  | 0 => 1 / 3
  | 1 => 1
  | 2 => 1 / 3

noncomputable def rtbtInvCubic (r : ℝ) : ℝ :=
  r ^ 3 - 2 * r ^ 2 - 2 * r - 5

lemma rtbtInvCubic_root_gt_three {r : ℝ}
    (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0) : 3 < r := by
  by_contra hnot
  have hle : r ≤ 3 := le_of_not_gt hnot
  have hcube_le : r ^ 3 ≤ 3 * r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg r)]
  have hsquare_le : r ^ 2 ≤ 3 * r := by
    nlinarith [mul_le_mul_of_nonneg_left hle hrpos.le]
  have hneg : rtbtInvCubic r < 0 := by
    unfold rtbtInvCubic
    nlinarith
  nlinarith

lemma exists_rtbtInvCubic_root_gt_three :
    ∃ r : ℝ, 3 < r ∧ rtbtInvCubic r = 0 := by
  let f : ℝ → ℝ := rtbtInvCubic
  have hcont : ContinuousOn f (Icc (3 : ℝ) 4) := by
    have hcontAll : Continuous f := by
      unfold f rtbtInvCubic
      continuity
    exact hcontAll.continuousOn
  have hzero : (0 : ℝ) ∈ Icc (f 3) (f 4) := by
    simp [f, rtbtInvCubic]
    norm_num
  rcases intermediate_value_Icc (show (3 : ℝ) ≤ 4 by norm_num) hcont hzero with
    ⟨r, hrIcc, hrroot⟩
  have hrpos : 0 < r := by nlinarith [hrIcc.1]
  exact ⟨r, rtbtInvCubic_root_gt_three hrpos hrroot, hrroot⟩

lemma rtbtInvStrengthR_pos {r : ℝ} (hrpos : 0 < r) :
    ∀ x : Fin 3, 0 < rtbtInvStrengthR r x := by
  intro x
  fin_cases x <;> simp [rtbtInvStrengthR, hrpos, pow_pos hrpos]

lemma rtbtInvStrengthRPlus_pos :
    ∀ x : Fin 3, 0 < rtbtInvStrengthRPlus x := by
  intro x
  fin_cases x <;> norm_num [rtbtInvStrengthRPlus]

lemma rtbtInvStrengthRReverse_pos {r : ℝ} (hrpos : 0 < r) :
    ∀ x : Fin 3, 0 < rtbtInvStrengthRReverse r x := by
  intro x
  fin_cases x <;> simp [rtbtInvStrengthRReverse, hrpos, pow_pos hrpos]

lemma rtbtInvStrengthRPlusReverse_pos :
    ∀ x : Fin 3, 0 < rtbtInvStrengthRPlusReverse x := by
  intro x
  fin_cases x <;> norm_num [rtbtInvStrengthRPlusReverse]

lemma rtbtInvStrengthR_ratio (r : ℝ) :
    rtbtInvStrengthR r 0 / rtbtInvStrengthR r 1 = r := by
  simp [rtbtInvStrengthR]

lemma rtbtInvStrengthRPlus_ratio :
    rtbtInvStrengthRPlus 0 / rtbtInvStrengthRPlus 1 = 3 := by
  norm_num [rtbtInvStrengthRPlus]

lemma rtbtInvStrengthRReverse_ratio (r : ℝ) :
    rtbtInvStrengthRReverse r 0 / rtbtInvStrengthRReverse r 1 = 1 / r := by
  simp [rtbtInvStrengthRReverse]

lemma rtbtInvStrengthRPlusReverse_ratio :
    rtbtInvStrengthRPlusReverse 0 / rtbtInvStrengthRPlusReverse 1 = 1 / 3 := by
  norm_num [rtbtInvStrengthRPlusReverse]

lemma rtbtInvStrengthR_satisfies_BT {r : ℝ}
    (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0) :
    SatisfiesBTDisplayedEquation rtbtInvWeightR rtbtInvBordaR
      (rtbtInvStrengthR r) := by
  intro x
  fin_cases x
  · simp [rtbtInvWeightR, rtbtInvBordaR, rtbtInvStrengthR, Fin.sum_univ_three]
    field_simp [ne_of_gt (add_pos hrpos zero_lt_one),
      ne_of_gt (add_pos hrpos (pow_pos hrpos 2))]
    ring_nf
  · have hpoly : r ^ 3 - 2 * r ^ 2 - 2 * r - 5 = 0 := by
      simpa [rtbtInvCubic] using hroot
    simp [rtbtInvWeightR, rtbtInvBordaR, rtbtInvStrengthR, Fin.sum_univ_three]
    field_simp [ne_of_gt (add_pos zero_lt_one hrpos),
      ne_of_gt (add_pos zero_lt_one (pow_pos hrpos 2))]
    nlinarith
  · have hpoly : r ^ 3 - 2 * r ^ 2 - 2 * r - 5 = 0 := by
      simpa [rtbtInvCubic] using hroot
    simp [rtbtInvWeightR, rtbtInvBordaR, rtbtInvStrengthR, Fin.sum_univ_three]
    field_simp [ne_of_gt (add_pos (pow_pos hrpos 2) hrpos),
      ne_of_gt (add_pos (pow_pos hrpos 2) zero_lt_one)]
    nlinarith

lemma rtbtInvStrengthRPlus_satisfies_BT :
    SatisfiesBTDisplayedEquation rtbtInvWeightRPlus rtbtInvBordaRPlus
      rtbtInvStrengthRPlus := by
  intro x
  fin_cases x <;>
    simp [rtbtInvWeightRPlus, Fin.sum_univ_three, rtbtInvBordaRPlus,
      rtbtInvStrengthRPlus] <;>
      norm_num

lemma rtbtInvStrengthRReverse_satisfies_BT {r : ℝ}
    (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0) :
    SatisfiesBTDisplayedEquation rtbtInvWeightR rtbtInvBordaRReverse
      (rtbtInvStrengthRReverse r) := by
  intro x
  fin_cases x
  · simp [rtbtInvWeightR, rtbtInvBordaRReverse, rtbtInvStrengthRReverse,
      Fin.sum_univ_three]
    field_simp [hrpos.ne', ne_of_gt (pow_pos hrpos 2),
      ne_of_gt (add_pos (one_div_pos.mpr hrpos) zero_lt_one),
      ne_of_gt (add_pos (one_div_pos.mpr hrpos)
        (one_div_pos.mpr (pow_pos hrpos 2)))]
    ring_nf
  · have hpoly : r ^ 3 - 2 * r ^ 2 - 2 * r - 5 = 0 := by
      simpa [rtbtInvCubic] using hroot
    simp [rtbtInvWeightR, rtbtInvBordaRReverse, rtbtInvStrengthRReverse,
      Fin.sum_univ_three]
    field_simp [hrpos.ne', ne_of_gt (pow_pos hrpos 2),
      ne_of_gt (add_pos zero_lt_one (one_div_pos.mpr hrpos)),
      ne_of_gt (add_pos zero_lt_one (one_div_pos.mpr (pow_pos hrpos 2)))]
    nlinarith
  · have hpoly : r ^ 3 - 2 * r ^ 2 - 2 * r - 5 = 0 := by
      simpa [rtbtInvCubic] using hroot
    simp [rtbtInvWeightR, rtbtInvBordaRReverse, rtbtInvStrengthRReverse,
      Fin.sum_univ_three]
    field_simp [hrpos.ne', ne_of_gt (pow_pos hrpos 2),
      ne_of_gt (add_pos (one_div_pos.mpr (pow_pos hrpos 2))
        (one_div_pos.mpr hrpos)),
      ne_of_gt (add_pos (one_div_pos.mpr (pow_pos hrpos 2)) zero_lt_one)]
    nlinarith

lemma rtbtInvStrengthRPlusReverse_satisfies_BT :
    SatisfiesBTDisplayedEquation rtbtInvWeightRPlus
      rtbtInvBordaRPlusReverse rtbtInvStrengthRPlusReverse := by
  intro x
  fin_cases x <;>
    simp [rtbtInvWeightRPlus, Fin.sum_univ_three,
      rtbtInvBordaRPlusReverse, rtbtInvStrengthRPlusReverse] <;>
      norm_num

theorem rtbtInvStrengthR_normalized_isBTStrength {r : ℝ}
    (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0) :
    IsBTStrength rtbtInvWeightR (rtbtStrictCount3 rtbtInvProfileR)
      (normalizeStrength (rtbtInvStrengthR r)) :=
  IsBTStrength_of_displayed_normalized
    (rtbtInvStrengthR_pos hrpos)
    rtbtInvProfileR_borda_erase_eq
    (rtbtInvStrengthR_satisfies_BT hrpos hroot)

theorem rtbtInvStrengthRPlus_normalized_isBTStrength :
    IsBTStrength rtbtInvWeightRPlus (rtbtStrictCount4 rtbtInvProfileRPlus)
      (normalizeStrength rtbtInvStrengthRPlus) :=
  IsBTStrength_of_displayed_normalized
    rtbtInvStrengthRPlus_pos
    rtbtInvProfileRPlus_borda_erase_eq
    rtbtInvStrengthRPlus_satisfies_BT

theorem rtbtInvStrengthRReverse_normalized_isBTStrength {r : ℝ}
    (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0) :
    IsBTStrength rtbtInvWeightR (rtbtStrictCount3 rtbtInvProfileRReverse)
      (normalizeStrength (rtbtInvStrengthRReverse r)) :=
  IsBTStrength_of_displayed_normalized
    (rtbtInvStrengthRReverse_pos hrpos)
    rtbtInvProfileRReverse_borda_erase_eq
    (rtbtInvStrengthRReverse_satisfies_BT hrpos hroot)

theorem rtbtInvStrengthRPlusReverse_normalized_isBTStrength :
    IsBTStrength rtbtInvWeightRPlus
      (rtbtStrictCount4 rtbtInvProfileRPlusReverse)
      (normalizeStrength rtbtInvStrengthRPlusReverse) :=
  IsBTStrength_of_displayed_normalized
    rtbtInvStrengthRPlusReverse_pos
    rtbtInvProfileRPlusReverse_borda_erase_eq
    rtbtInvStrengthRPlusReverse_satisfies_BT

lemma rtbtInv_ratio_drop {r : ℝ}
    (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0) :
    rtbtInvStrengthRPlus 0 / rtbtInvStrengthRPlus 1 <
      rtbtInvStrengthR r 0 / rtbtInvStrengthR r 1 := by
  rw [rtbtInvStrengthRPlus_ratio, rtbtInvStrengthR_ratio]
  exact rtbtInvCubic_root_gt_three hrpos hroot

/-- The concrete algebraic data in the appendix proof of Proposition
`InvolveViolRTBT`: there is a cubic root `r > 3`; `(r,1,r^2)` satisfies the displayed BT equation for
`R`; `(3,1,3)` satisfies it for `R+`; and the `a/b` strength ratio strictly
drops after adding the voter who ranks `a` first. -/
theorem exists_rtbtInv_BT_ratio_drop :
    ∃ r : ℝ,
      3 < r ∧
        rtbtInvCubic r = 0 ∧
          SatisfiesBTDisplayedEquation rtbtInvWeightR rtbtInvBordaR
            (rtbtInvStrengthR r) ∧
          SatisfiesBTDisplayedEquation rtbtInvWeightRPlus rtbtInvBordaRPlus
            rtbtInvStrengthRPlus ∧
          rtbtInvStrengthRPlus 0 / rtbtInvStrengthRPlus 1 <
            rtbtInvStrengthR r 0 / rtbtInvStrengthR r 1 := by
  rcases exists_rtbtInvCubic_root_gt_three with ⟨r, hrgt, hroot⟩
  have hrpos : 0 < r := by nlinarith
  exact ⟨r, hrgt, hroot, rtbtInvStrengthR_satisfies_BT hrpos hroot,
    rtbtInvStrengthRPlus_satisfies_BT, rtbtInv_ratio_drop hrpos hroot⟩

/-- The same concrete RTBT involvement data stated with the simplex-normalized
Bradley--Terry representatives used by `IsBTStrength`.  The unnormalized
vectors above are still the convenient algebraic representatives; RTBT ignores
this positive rescaling. -/
theorem exists_rtbtInv_normalized_BT_witnesses :
    ∃ r : ℝ,
      3 < r ∧
        rtbtInvCubic r = 0 ∧
          IsBTStrength rtbtInvWeightR (rtbtStrictCount3 rtbtInvProfileR)
            (normalizeStrength (rtbtInvStrengthR r)) ∧
          IsBTStrength rtbtInvWeightRPlus
            (rtbtStrictCount4 rtbtInvProfileRPlus)
            (normalizeStrength rtbtInvStrengthRPlus) ∧
          IsBTStrength rtbtInvWeightR
            (rtbtStrictCount3 rtbtInvProfileRReverse)
            (normalizeStrength (rtbtInvStrengthRReverse r)) ∧
          IsBTStrength rtbtInvWeightRPlus
            (rtbtStrictCount4 rtbtInvProfileRPlusReverse)
            (normalizeStrength rtbtInvStrengthRPlusReverse) ∧
          rtbtInvStrengthRPlus 0 / rtbtInvStrengthRPlus 1 <
            rtbtInvStrengthR r 0 / rtbtInvStrengthR r 1 := by
  rcases exists_rtbtInvCubic_root_gt_three with ⟨r, hrgt, hroot⟩
  have hrpos : 0 < r := by nlinarith
  exact ⟨r, hrgt, hroot,
    rtbtInvStrengthR_normalized_isBTStrength hrpos hroot,
    rtbtInvStrengthRPlus_normalized_isBTStrength,
    rtbtInvStrengthRReverse_normalized_isBTStrength hrpos hroot,
    rtbtInvStrengthRPlusReverse_normalized_isBTStrength,
    rtbtInv_ratio_drop hrpos hroot⟩

/-- The concrete RTBT positive-involvement probability drop for any positive
root of the cubic used in the appendix proof. -/
theorem rtbtInv_positive_involvement_limit_counterexample_of_root
    {β r : ℝ} (hβ : 0 < β) (hrgt : 3 < r)
    (_hroot : rtbtInvCubic r = 0) :
    ∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
        RTBTFromStrength β (twoPointReference ε) rtbtInvStrengthRPlus 0 <
          RTBTFromStrength β (twoPointReference ε) (rtbtInvStrengthR r) 0 := by
  have hrpos : 0 < r := by nlinarith
  have hR :
      Tendsto
        (fun ε : ℝ =>
          RTBTFromStrength β (twoPointReference ε) (rtbtInvStrengthR r) 0)
        (𝓝[>] (0 : ℝ))
        (𝓝 (r ^ (1 / β) / (r ^ (1 / β) + 1))) := by
    simpa [rtbtInvStrengthR] using
      RTBTFromStrength_twoPointReference_tendsto_zero
        (β := β) (u := rtbtInvStrengthR r) hrpos zero_lt_one
  have hRPlus :
      Tendsto
        (fun ε : ℝ =>
          RTBTFromStrength β (twoPointReference ε) rtbtInvStrengthRPlus 0)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((3 : ℝ) ^ (1 / β) / ((3 : ℝ) ^ (1 / β) + 1))) := by
    simpa [rtbtInvStrengthRPlus] using
      RTBTFromStrength_twoPointReference_tendsto_zero
        (β := β) (u := rtbtInvStrengthRPlus)
        (by norm_num [rtbtInvStrengthRPlus]) (by norm_num [rtbtInvStrengthRPlus])
  obtain ⟨ε, hεpos, hεlt, hlt⟩ :=
    rtbt_positive_involvement_violation_from_limits hβ hrpos (by norm_num) hrgt hR hRPlus
  exact ⟨ε, hεpos, hεlt, hlt⟩

/-- The concrete RTBT positive-involvement violation for every `β > 0`, with
the same limiting reference distributions used in the paper proof. -/
theorem rtbtInv_positive_involvement_limit_counterexample
    {β : ℝ} (hβ : 0 < β) :
    ∃ r : ℝ,
      3 < r ∧ rtbtInvCubic r = 0 ∧
        ∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
            RTBTFromStrength β (twoPointReference ε) rtbtInvStrengthRPlus 0 <
              RTBTFromStrength β (twoPointReference ε) (rtbtInvStrengthR r) 0 := by
  rcases exists_rtbtInvCubic_root_gt_three with ⟨r, hrgt, hroot⟩
  obtain ⟨ε, hεpos, hεlt, hlt⟩ :=
    rtbtInv_positive_involvement_limit_counterexample_of_root hβ hrgt hroot
  exact ⟨r, hrgt, hroot, ε, hεpos, hεlt, hlt⟩

/-- The concrete RTBT negative-involvement probability increase for any
positive root of the cubic used in the appendix proof, using the reversed
profile BT ratios `1 / r` and `1 / 3`. -/
theorem rtbtInv_negative_involvement_limit_counterexample_of_root
    {β r : ℝ} (hβ : 0 < β) (hrgt : 3 < r)
    (_hroot : rtbtInvCubic r = 0) :
    ∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
        RTBTFromStrength β (twoPointReference ε) (rtbtInvStrengthRReverse r) 0 <
          RTBTFromStrength β (twoPointReference ε) rtbtInvStrengthRPlusReverse 0 := by
  have hrpos : 0 < r := by nlinarith
  have hR :
      Tendsto
        (fun ε : ℝ =>
          RTBTFromStrength β (twoPointReference ε) (rtbtInvStrengthRReverse r) 0)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((1 / r) ^ (1 / β) / ((1 / r) ^ (1 / β) + 1))) := by
    simpa [rtbtInvStrengthRReverse] using
      RTBTFromStrength_twoPointReference_tendsto_zero
        (β := β) (u := rtbtInvStrengthRReverse r)
        (one_div_pos.mpr hrpos) zero_lt_one
  have hRPlus :
      Tendsto
        (fun ε : ℝ =>
          RTBTFromStrength β (twoPointReference ε) rtbtInvStrengthRPlusReverse 0)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((1 / (3 : ℝ)) ^ (1 / β) /
          ((1 / (3 : ℝ)) ^ (1 / β) + 1))) := by
    simpa [rtbtInvStrengthRPlusReverse] using
      RTBTFromStrength_twoPointReference_tendsto_zero
        (β := β) (u := rtbtInvStrengthRPlusReverse)
        (by norm_num [rtbtInvStrengthRPlusReverse])
        (by norm_num [rtbtInvStrengthRPlusReverse])
  obtain ⟨ε, hεpos, hεlt, hlt⟩ :=
    rtbt_negative_involvement_violation_from_limits hβ hrpos (by norm_num) hrgt hR hRPlus
  exact ⟨ε, hεpos, hεlt, hlt⟩

/-- The concrete RTBT negative-involvement violation for every `β > 0`, using
the reversed-profile BT ratios `1 / r` and `1 / 3`. -/
theorem rtbtInv_negative_involvement_limit_counterexample
    {β : ℝ} (hβ : 0 < β) :
    ∃ r : ℝ,
      3 < r ∧ rtbtInvCubic r = 0 ∧
        ∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
            RTBTFromStrength β (twoPointReference ε) (rtbtInvStrengthRReverse r) 0 <
              RTBTFromStrength β (twoPointReference ε) rtbtInvStrengthRPlusReverse 0 := by
  rcases exists_rtbtInvCubic_root_gt_three with ⟨r, hrgt, hroot⟩
  obtain ⟨ε, hεpos, hεlt, hlt⟩ :=
    rtbtInv_negative_involvement_limit_counterexample_of_root hβ hrgt hroot
  exact ⟨r, hrgt, hroot, ε, hεpos, hεlt, hlt⟩

/-- Positive-involvement violation for any BT selector that returns the
appendix proof's two concrete strength vectors on the two concrete profiles. -/
theorem rtbtInv_positive_involvement_violation_from_BT_selection
    {β r : ℝ} (hβ : 0 < β) (hrgt : 3 < r)
    (hroot : rtbtInvCubic r = 0)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT_R : BT rtbtInvMarginR = rtbtInvStrengthR r)
    (hBT_RPlus : BT rtbtInvMarginRPlus = rtbtInvStrengthRPlus) :
    ViolatesPositiveInvolvement
      (fun M ρ => RTBTFromStrength β ρ (BT M))
      rtbtPositiveLinearAddsTopWitness := by
  intro hsatisfies
  rcases rtbtInv_positive_involvement_limit_counterexample_of_root
      hβ hrgt hroot with ⟨ε, hεpos, hεlt, hdrop⟩
  have hle :=
    hsatisfies rtbtInvMarginR rtbtInvMarginRPlus (twoPointReference ε) 0
      rtbtInvMarginR_normalized rtbtInvMarginRPlus_normalized
      (twoPointReference_fullSupport hεpos hεlt)
      rtbtPositiveLinearAddsTopWitness_here
  change RTBTFromStrength β (twoPointReference ε) (BT rtbtInvMarginR) 0 ≤
    RTBTFromStrength β (twoPointReference ε) (BT rtbtInvMarginRPlus) 0 at hle
  rw [hBT_R, hBT_RPlus] at hle
  exact not_lt_of_ge hle hdrop

/-- Negative-involvement violation for any BT selector that returns the
appendix proof's reversed-profile strength vectors on the two reversed
concrete profiles. -/
theorem rtbtInv_negative_involvement_violation_from_BT_selection
    {β r : ℝ} (hβ : 0 < β) (hrgt : 3 < r)
    (hroot : rtbtInvCubic r = 0)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT_R : BT rtbtInvMarginRReverse = rtbtInvStrengthRReverse r)
    (hBT_RPlus : BT rtbtInvMarginRPlusReverse = rtbtInvStrengthRPlusReverse) :
    ViolatesNegativeInvolvement
      (fun M ρ => RTBTFromStrength β ρ (BT M))
      rtbtNegativeLinearAddsBottomWitness := by
  intro hsatisfies
  rcases rtbtInv_negative_involvement_limit_counterexample_of_root
      hβ hrgt hroot with ⟨ε, hεpos, hεlt, hincrease⟩
  have hle :=
    hsatisfies rtbtInvMarginRReverse rtbtInvMarginRPlusReverse
      (twoPointReference ε) 0
      rtbtInvMarginRReverse_normalized rtbtInvMarginRPlusReverse_normalized
      (twoPointReference_fullSupport hεpos hεlt)
      rtbtNegativeLinearAddsBottomWitness_here
  change
    RTBTFromStrength β (twoPointReference ε) (BT rtbtInvMarginRPlusReverse) 0 ≤
      RTBTFromStrength β (twoPointReference ε) (BT rtbtInvMarginRReverse) 0 at hle
  rw [hBT_R, hBT_RPlus] at hle
  exact not_lt_of_ge hle hincrease

/-- Positive-involvement violation for a BT selector returning the
simplex-normalized concrete BT strength vectors. -/
theorem rtbtInv_positive_involvement_violation_from_normalized_BT_selection
    {β r : ℝ} (hβ : 0 < β) (hrgt : 3 < r)
    (hroot : rtbtInvCubic r = 0)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT_R : BT rtbtInvMarginR = normalizeStrength (rtbtInvStrengthR r))
    (hBT_RPlus :
      BT rtbtInvMarginRPlus = normalizeStrength rtbtInvStrengthRPlus) :
    ViolatesPositiveInvolvement
      (fun M ρ => RTBTFromStrength β ρ (BT M))
      rtbtPositiveLinearAddsTopWitness := by
  intro hsatisfies
  have hrpos : 0 < r := by nlinarith
  rcases rtbtInv_positive_involvement_limit_counterexample_of_root
      hβ hrgt hroot with ⟨ε, hεpos, hεlt, hdrop⟩
  have hle :=
    hsatisfies rtbtInvMarginR rtbtInvMarginRPlus (twoPointReference ε) 0
      rtbtInvMarginR_normalized rtbtInvMarginRPlus_normalized
      (twoPointReference_fullSupport hεpos hεlt)
      rtbtPositiveLinearAddsTopWitness_here
  change RTBTFromStrength β (twoPointReference ε) (BT rtbtInvMarginR) 0 ≤
    RTBTFromStrength β (twoPointReference ε) (BT rtbtInvMarginRPlus) 0 at hle
  rw [hBT_R, hBT_RPlus] at hle
  rw [RTBTFromStrength_normalizeStrength
        (β := β) (ρ := twoPointReference ε)
        (u := rtbtInvStrengthR r) (rtbtInvStrengthR_pos hrpos),
      RTBTFromStrength_normalizeStrength
        (β := β) (ρ := twoPointReference ε)
        (u := rtbtInvStrengthRPlus) rtbtInvStrengthRPlus_pos] at hle
  exact not_lt_of_ge hle hdrop

/-- Negative-involvement violation for a BT selector returning the
simplex-normalized reversed-profile BT strength vectors. -/
theorem rtbtInv_negative_involvement_violation_from_normalized_BT_selection
    {β r : ℝ} (hβ : 0 < β) (hrgt : 3 < r)
    (hroot : rtbtInvCubic r = 0)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT_R : BT rtbtInvMarginRReverse =
      normalizeStrength (rtbtInvStrengthRReverse r))
    (hBT_RPlus : BT rtbtInvMarginRPlusReverse =
      normalizeStrength rtbtInvStrengthRPlusReverse) :
    ViolatesNegativeInvolvement
      (fun M ρ => RTBTFromStrength β ρ (BT M))
      rtbtNegativeLinearAddsBottomWitness := by
  intro hsatisfies
  have hrpos : 0 < r := by nlinarith
  rcases rtbtInv_negative_involvement_limit_counterexample_of_root
      hβ hrgt hroot with ⟨ε, hεpos, hεlt, hincrease⟩
  have hle :=
    hsatisfies rtbtInvMarginRReverse rtbtInvMarginRPlusReverse
      (twoPointReference ε) 0
      rtbtInvMarginRReverse_normalized rtbtInvMarginRPlusReverse_normalized
      (twoPointReference_fullSupport hεpos hεlt)
      rtbtNegativeLinearAddsBottomWitness_here
  change
    RTBTFromStrength β (twoPointReference ε) (BT rtbtInvMarginRPlusReverse) 0 ≤
      RTBTFromStrength β (twoPointReference ε) (BT rtbtInvMarginRReverse) 0 at hle
  rw [hBT_R, hBT_RPlus] at hle
  rw [RTBTFromStrength_normalizeStrength
        (β := β) (ρ := twoPointReference ε)
        (u := rtbtInvStrengthRReverse r)
        (rtbtInvStrengthRReverse_pos hrpos),
      RTBTFromStrength_normalizeStrength
        (β := β) (ρ := twoPointReference ε)
        (u := rtbtInvStrengthRPlusReverse)
        rtbtInvStrengthRPlusReverse_pos] at hle
  exact not_lt_of_ge hle hincrease

/-- Proposition `InvolveViolRTBT` in concrete witness form: once the BT
selector agrees with the BT strengths
computed in the appendix on the four displayed profiles, RTBT violates both
involvement axioms. -/
theorem InvolveViolRTBT_from_concrete_BT_selection
    {β r : ℝ} (hβ : 0 < β) (hrgt : 3 < r)
    (hroot : rtbtInvCubic r = 0)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT_R : BT rtbtInvMarginR = rtbtInvStrengthR r)
    (hBT_RPlus : BT rtbtInvMarginRPlus = rtbtInvStrengthRPlus)
    (hBT_Rrev : BT rtbtInvMarginRReverse = rtbtInvStrengthRReverse r)
    (hBT_RPlusRev :
      BT rtbtInvMarginRPlusReverse = rtbtInvStrengthRPlusReverse) :
    ViolatesPositiveInvolvement
        (fun M ρ => RTBTFromStrength β ρ (BT M))
        rtbtPositiveLinearAddsTopWitness ∧
      ViolatesNegativeInvolvement
        (fun M ρ => RTBTFromStrength β ρ (BT M))
        rtbtNegativeLinearAddsBottomWitness := by
  exact
    ⟨rtbtInv_positive_involvement_violation_from_BT_selection
        hβ hrgt hroot hBT_R hBT_RPlus,
      rtbtInv_negative_involvement_violation_from_BT_selection
        hβ hrgt hroot hBT_Rrev hBT_RPlusRev⟩

/-- Proposition `InvolveViolRTBT`, with the BT selector returning the
simplex-normalized representatives guaranteed by Proposition `BTProp`. -/
theorem InvolveViolRTBT_from_concrete_normalized_BT_selection
    {β r : ℝ} (hβ : 0 < β) (hrgt : 3 < r)
    (hroot : rtbtInvCubic r = 0)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT_R : BT rtbtInvMarginR = normalizeStrength (rtbtInvStrengthR r))
    (hBT_RPlus :
      BT rtbtInvMarginRPlus = normalizeStrength rtbtInvStrengthRPlus)
    (hBT_Rrev : BT rtbtInvMarginRReverse =
      normalizeStrength (rtbtInvStrengthRReverse r))
    (hBT_RPlusRev : BT rtbtInvMarginRPlusReverse =
      normalizeStrength rtbtInvStrengthRPlusReverse) :
    ViolatesPositiveInvolvement
        (fun M ρ => RTBTFromStrength β ρ (BT M))
        rtbtPositiveLinearAddsTopWitness ∧
      ViolatesNegativeInvolvement
        (fun M ρ => RTBTFromStrength β ρ (BT M))
        rtbtNegativeLinearAddsBottomWitness := by
  exact
    ⟨rtbtInv_positive_involvement_violation_from_normalized_BT_selection
        hβ hrgt hroot hBT_R hBT_RPlus,
      rtbtInv_negative_involvement_violation_from_normalized_BT_selection
        hβ hrgt hroot hBT_Rrev hBT_RPlusRev⟩

/-- The local BT-selection condition needed for the concrete RTBT involvement
witnesses: on each of the four displayed margin matrices, the selector returns
a normalized Bradley--Terry solution for the corresponding profile counts. -/
def IsRTBTInvolvementBTSelector
    (BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ) : Prop :=
  IsBTStrength rtbtInvWeightR (rtbtStrictCount3 rtbtInvProfileR)
      (BT rtbtInvMarginR) ∧
    IsBTStrength rtbtInvWeightRPlus (rtbtStrictCount4 rtbtInvProfileRPlus)
      (BT rtbtInvMarginRPlus) ∧
    IsBTStrength rtbtInvWeightR (rtbtStrictCount3 rtbtInvProfileRReverse)
      (BT rtbtInvMarginRReverse) ∧
    IsBTStrength rtbtInvWeightRPlus
      (rtbtStrictCount4 rtbtInvProfileRPlusReverse)
      (BT rtbtInvMarginRPlusReverse)

lemma rtbtInvMarginRPlus_ne_R :
    rtbtInvMarginRPlus ≠ rtbtInvMarginR := by
  intro h
  have hx := congrFun (congrFun h 0) 1
  norm_num [rtbtInvMarginRPlus, rtbtInvMarginR] at hx

lemma rtbtInvMarginRReverse_ne_R :
    rtbtInvMarginRReverse ≠ rtbtInvMarginR := by
  intro h
  have hx := congrFun (congrFun h 0) 1
  norm_num [rtbtInvMarginRReverse, rtbtInvMarginR] at hx

lemma rtbtInvMarginRReverse_ne_RPlus :
    rtbtInvMarginRReverse ≠ rtbtInvMarginRPlus := by
  intro h
  have hx := congrFun (congrFun h 0) 1
  norm_num [rtbtInvMarginRReverse, rtbtInvMarginR, rtbtInvMarginRPlus] at hx

lemma rtbtInvMarginRPlusReverse_ne_R :
    rtbtInvMarginRPlusReverse ≠ rtbtInvMarginR := by
  intro h
  have hx := congrFun (congrFun h 0) 1
  norm_num [rtbtInvMarginRPlusReverse, rtbtInvMarginRPlus,
    rtbtInvMarginR] at hx

lemma rtbtInvMarginRPlusReverse_ne_RPlus :
    rtbtInvMarginRPlusReverse ≠ rtbtInvMarginRPlus := by
  intro h
  have hx := congrFun (congrFun h 0) 1
  norm_num [rtbtInvMarginRPlusReverse, rtbtInvMarginRPlus] at hx

lemma rtbtInvMarginRPlusReverse_ne_RReverse :
    rtbtInvMarginRPlusReverse ≠ rtbtInvMarginRReverse := by
  intro h
  have hx := congrFun (congrFun h 0) 1
  norm_num [rtbtInvMarginRPlusReverse, rtbtInvMarginRPlus,
    rtbtInvMarginRReverse, rtbtInvMarginR] at hx

/-- The Ford/Zermelo-selected BT rule on the four concrete margins used in the
RTBT involvement counterexample.  Outside those margins it falls back to the
first concrete profile; that fallback is irrelevant to the counterexample. -/
noncomputable def rtbtInvSelectedBTOfFordZermelo
    (hFord : FordZermeloBTTheorem (Fin 3)) :
    (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ := by
  classical
  exact fun M =>
    if M = rtbtInvMarginR then
      selectedBTOfFordZermelo hFord (rtbtStrictCount3 rtbtInvProfileR)
        rtbtInvProfileR_fordCountMatrix
        rtbtInvProfileR_fordStronglyConnected
    else if M = rtbtInvMarginRPlus then
      selectedBTOfFordZermelo hFord (rtbtStrictCount4 rtbtInvProfileRPlus)
        rtbtInvProfileRPlus_fordCountMatrix
        rtbtInvProfileRPlus_fordStronglyConnected
    else if M = rtbtInvMarginRReverse then
      selectedBTOfFordZermelo hFord (rtbtStrictCount3 rtbtInvProfileRReverse)
        rtbtInvProfileRReverse_fordCountMatrix
        rtbtInvProfileRReverse_fordStronglyConnected
    else if M = rtbtInvMarginRPlusReverse then
      selectedBTOfFordZermelo hFord
        (rtbtStrictCount4 rtbtInvProfileRPlusReverse)
        rtbtInvProfileRPlusReverse_fordCountMatrix
        rtbtInvProfileRPlusReverse_fordStronglyConnected
    else
      selectedBTOfFordZermelo hFord (rtbtStrictCount3 rtbtInvProfileR)
        rtbtInvProfileR_fordCountMatrix
        rtbtInvProfileR_fordStronglyConnected

lemma rtbtInvSelectedBTOfFordZermelo_is_selector
    (hFord : FordZermeloBTTheorem (Fin 3)) :
    IsRTBTInvolvementBTSelector (rtbtInvSelectedBTOfFordZermelo hFord) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [rtbtInvSelectedBTOfFordZermelo,
      rtbtInvProfileR_fordPairTotal_eq] using
      selectedBTOfFordZermelo_isBTStrength hFord
        rtbtInvProfileR_fordCountMatrix
        rtbtInvProfileR_fordStronglyConnected
  · simpa [rtbtInvSelectedBTOfFordZermelo,
      rtbtInvMarginRPlus_ne_R,
      rtbtInvProfileRPlus_fordPairTotal_eq] using
      selectedBTOfFordZermelo_isBTStrength hFord
        rtbtInvProfileRPlus_fordCountMatrix
        rtbtInvProfileRPlus_fordStronglyConnected
  · simpa [rtbtInvSelectedBTOfFordZermelo,
      rtbtInvMarginRReverse_ne_R,
      rtbtInvMarginRReverse_ne_RPlus,
      rtbtInvProfileRReverse_fordPairTotal_eq] using
      selectedBTOfFordZermelo_isBTStrength hFord
        rtbtInvProfileRReverse_fordCountMatrix
        rtbtInvProfileRReverse_fordStronglyConnected
  · simpa [rtbtInvSelectedBTOfFordZermelo,
      rtbtInvMarginRPlusReverse_ne_R,
      rtbtInvMarginRPlusReverse_ne_RPlus,
      rtbtInvMarginRPlusReverse_ne_RReverse,
      rtbtInvProfileRPlusReverse_fordPairTotal_eq] using
      selectedBTOfFordZermelo_isBTStrength hFord
        rtbtInvProfileRPlusReverse_fordCountMatrix
        rtbtInvProfileRPlusReverse_fordStronglyConnected

lemma rtbtInvProfileR_BT_selector_eq_normalized_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {r : ℝ} (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT :
      IsBTStrength rtbtInvWeightR (rtbtStrictCount3 rtbtInvProfileR)
        (BT rtbtInvMarginR)) :
    BT rtbtInvMarginR = normalizeStrength (rtbtInvStrengthR r) := by
  rcases exists_BTProp_certificate_of_ford_zermelo hFord
      rtbtInvProfileR_fordCountMatrix
      rtbtInvProfileR_fordStronglyConnected with
    ⟨u, hu⟩
  have hcert :
      HasBTPropCertificate rtbtInvWeightR
        (rtbtStrictCount3 rtbtInvProfileR) u := by
    simpa [rtbtInvProfileR_fordPairTotal_eq] using hu
  have hsel : BT rtbtInvMarginR = u := hcert.2.2 _ hBT
  have hconcrete :
      normalizeStrength (rtbtInvStrengthR r) = u :=
    hcert.2.2 _ (rtbtInvStrengthR_normalized_isBTStrength hrpos hroot)
  exact hsel.trans hconcrete.symm

lemma rtbtInvProfileRPlus_BT_selector_eq_normalized_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT :
      IsBTStrength rtbtInvWeightRPlus
        (rtbtStrictCount4 rtbtInvProfileRPlus)
        (BT rtbtInvMarginRPlus)) :
    BT rtbtInvMarginRPlus = normalizeStrength rtbtInvStrengthRPlus := by
  rcases exists_BTProp_certificate_of_ford_zermelo hFord
      rtbtInvProfileRPlus_fordCountMatrix
      rtbtInvProfileRPlus_fordStronglyConnected with
    ⟨u, hu⟩
  have hcert :
      HasBTPropCertificate rtbtInvWeightRPlus
        (rtbtStrictCount4 rtbtInvProfileRPlus) u := by
    simpa [rtbtInvProfileRPlus_fordPairTotal_eq] using hu
  have hsel : BT rtbtInvMarginRPlus = u := hcert.2.2 _ hBT
  have hconcrete :
      normalizeStrength rtbtInvStrengthRPlus = u :=
    hcert.2.2 _ rtbtInvStrengthRPlus_normalized_isBTStrength
  exact hsel.trans hconcrete.symm

lemma rtbtInvProfileRReverse_BT_selector_eq_normalized_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {r : ℝ} (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT :
      IsBTStrength rtbtInvWeightR
        (rtbtStrictCount3 rtbtInvProfileRReverse)
        (BT rtbtInvMarginRReverse)) :
    BT rtbtInvMarginRReverse =
      normalizeStrength (rtbtInvStrengthRReverse r) := by
  rcases exists_BTProp_certificate_of_ford_zermelo hFord
      rtbtInvProfileRReverse_fordCountMatrix
      rtbtInvProfileRReverse_fordStronglyConnected with
    ⟨u, hu⟩
  have hcert :
      HasBTPropCertificate rtbtInvWeightR
        (rtbtStrictCount3 rtbtInvProfileRReverse) u := by
    simpa [rtbtInvProfileRReverse_fordPairTotal_eq] using hu
  have hsel : BT rtbtInvMarginRReverse = u := hcert.2.2 _ hBT
  have hconcrete :
      normalizeStrength (rtbtInvStrengthRReverse r) = u :=
    hcert.2.2 _ (rtbtInvStrengthRReverse_normalized_isBTStrength hrpos hroot)
  exact hsel.trans hconcrete.symm

lemma rtbtInvProfileRPlusReverse_BT_selector_eq_normalized_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT :
      IsBTStrength rtbtInvWeightRPlus
        (rtbtStrictCount4 rtbtInvProfileRPlusReverse)
        (BT rtbtInvMarginRPlusReverse)) :
    BT rtbtInvMarginRPlusReverse =
      normalizeStrength rtbtInvStrengthRPlusReverse := by
  rcases exists_BTProp_certificate_of_ford_zermelo hFord
      rtbtInvProfileRPlusReverse_fordCountMatrix
      rtbtInvProfileRPlusReverse_fordStronglyConnected with
    ⟨u, hu⟩
  have hcert :
      HasBTPropCertificate rtbtInvWeightRPlus
        (rtbtStrictCount4 rtbtInvProfileRPlusReverse) u := by
    simpa [rtbtInvProfileRPlusReverse_fordPairTotal_eq] using hu
  have hsel : BT rtbtInvMarginRPlusReverse = u := hcert.2.2 _ hBT
  have hconcrete :
      normalizeStrength rtbtInvStrengthRPlusReverse = u :=
    hcert.2.2 _ rtbtInvStrengthRPlusReverse_normalized_isBTStrength
  exact hsel.trans hconcrete.symm

/-- The actual Ford/Zermelo selector on the literal three-voter profile `R`
is the normalized concrete strength vector computed in the appendix proof. -/
lemma selectedBTOfFordZermelo_rtbtInvProfileR_eq_normalized
    (hFord : FordZermeloBTTheorem (Fin 3))
    {r : ℝ} (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0) :
    selectedBTOfFordZermelo hFord (strictCount rtbtInvProfileR)
        (strictCount_isFordCountMatrix rtbtInvProfileR_irreflexive)
        rtbtInvProfileR_actual_fordStronglyConnected =
      normalizeStrength (rtbtInvStrengthR r) := by
  refine rtbtInvProfileR_BT_selector_eq_normalized_of_ford_zermelo
    (BT := fun _ =>
      selectedBTOfFordZermelo hFord (strictCount rtbtInvProfileR)
        (strictCount_isFordCountMatrix rtbtInvProfileR_irreflexive)
        rtbtInvProfileR_actual_fordStronglyConnected)
    hFord hrpos hroot ?_
  simpa only [strictCount_rtbtInvProfileR,
      rtbtInvProfileR_fordPairTotal_eq] using
    selectedBTOfFordZermelo_isBTStrength hFord
      (strictCount_isFordCountMatrix rtbtInvProfileR_irreflexive)
      rtbtInvProfileR_actual_fordStronglyConnected

/-- The actual selector on `addVoterProfile R abc` is the normalized
three-to-one concrete strength vector. -/
lemma selectedBTOfFordZermelo_rtbtInvProfileR_addVoter_eq_normalized
    (hFord : FordZermeloBTTheorem (Fin 3)) :
    selectedBTOfFordZermelo hFord
        (strictCount (addVoterProfile rtbtInvProfileR rtbtPrefABC))
        (strictCount_addVoterProfile_isFordCountMatrix
          rtbtInvProfileR_irreflexive rtbtPrefABC_linear.1)
        rtbtInvProfileR_addVoter_actual_fordStronglyConnected =
      normalizeStrength rtbtInvStrengthRPlus := by
  refine rtbtInvProfileRPlus_BT_selector_eq_normalized_of_ford_zermelo
    (BT := fun _ =>
      selectedBTOfFordZermelo hFord
        (strictCount (addVoterProfile rtbtInvProfileR rtbtPrefABC))
        (strictCount_addVoterProfile_isFordCountMatrix
          rtbtInvProfileR_irreflexive rtbtPrefABC_linear.1)
        rtbtInvProfileR_addVoter_actual_fordStronglyConnected)
    hFord ?_
  simpa only [strictCount_addVoter_rtbtInvProfileR,
      rtbtInvProfileRPlus_fordPairTotal_eq] using
    selectedBTOfFordZermelo_isBTStrength hFord
      (strictCount_addVoterProfile_isFordCountMatrix
        rtbtInvProfileR_irreflexive rtbtPrefABC_linear.1)
      rtbtInvProfileR_addVoter_actual_fordStronglyConnected

/-- The actual selector on the reversed three-voter profile is the normalized
reversed concrete strength vector. -/
lemma selectedBTOfFordZermelo_rtbtInvProfileRReverse_eq_normalized
    (hFord : FordZermeloBTTheorem (Fin 3))
    {r : ℝ} (hrpos : 0 < r) (hroot : rtbtInvCubic r = 0) :
    selectedBTOfFordZermelo hFord (strictCount rtbtInvProfileRReverse)
        (strictCount_isFordCountMatrix rtbtInvProfileRReverse_irreflexive)
        rtbtInvProfileRReverse_actual_fordStronglyConnected =
      normalizeStrength (rtbtInvStrengthRReverse r) := by
  refine rtbtInvProfileRReverse_BT_selector_eq_normalized_of_ford_zermelo
    (BT := fun _ =>
      selectedBTOfFordZermelo hFord (strictCount rtbtInvProfileRReverse)
        (strictCount_isFordCountMatrix rtbtInvProfileRReverse_irreflexive)
        rtbtInvProfileRReverse_actual_fordStronglyConnected)
    hFord hrpos hroot ?_
  simpa only [strictCount_rtbtInvProfileRReverse,
      rtbtInvProfileRReverse_fordPairTotal_eq] using
    selectedBTOfFordZermelo_isBTStrength hFord
      (strictCount_isFordCountMatrix rtbtInvProfileRReverse_irreflexive)
      rtbtInvProfileRReverse_actual_fordStronglyConnected

/-- The actual selector on the reversed profile plus the bottom-ranking voter
is the normalized reversed three-to-one concrete strength vector. -/
lemma selectedBTOfFordZermelo_rtbtInvProfileRReverse_addVoter_eq_normalized
    (hFord : FordZermeloBTTheorem (Fin 3)) :
    selectedBTOfFordZermelo hFord
        (strictCount
          (addVoterProfile rtbtInvProfileRReverse rtbtPrefCBA))
        (strictCount_addVoterProfile_isFordCountMatrix
          rtbtInvProfileRReverse_irreflexive rtbtPrefCBA_linear.1)
        rtbtInvProfileRReverse_addVoter_actual_fordStronglyConnected =
      normalizeStrength rtbtInvStrengthRPlusReverse := by
  refine
    rtbtInvProfileRPlusReverse_BT_selector_eq_normalized_of_ford_zermelo
      (BT := fun _ =>
        selectedBTOfFordZermelo hFord
          (strictCount
            (addVoterProfile rtbtInvProfileRReverse rtbtPrefCBA))
          (strictCount_addVoterProfile_isFordCountMatrix
            rtbtInvProfileRReverse_irreflexive rtbtPrefCBA_linear.1)
          rtbtInvProfileRReverse_addVoter_actual_fordStronglyConnected)
      hFord ?_
  simpa only [strictCount_addVoter_rtbtInvProfileRReverse,
      rtbtInvProfileRPlusReverse_fordPairTotal_eq] using
    selectedBTOfFordZermelo_isBTStrength hFord
      (strictCount_addVoterProfile_isFordCountMatrix
        rtbtInvProfileRReverse_irreflexive rtbtPrefCBA_linear.1)
      rtbtInvProfileRReverse_addVoter_actual_fordStronglyConnected

/-- Genuine profile-level positive-involvement witness for selected RTBT.
The theorem quantifies literal strict-linear-order profile and added-voter
data, carries both Ford-domain certificates, and compares the actual
Ford/Zermelo-selected RTBT values computed from their `strictCount`s. -/
theorem InvolveViolRTBT_positive_profile_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β) :
    ∃ (R : Fin 3 → Fin 3 → Fin 3 → Bool)
        (p : Fin 3 → Fin 3 → Bool) (x : Fin 3),
      (∀ i, IsLinearPref (R i)) ∧
        IsLinearPref p ∧ RanksTop p x ∧
        ∃ (hR : IsIrreflexiveProfile R)
          (hp : ∀ z, p z z = false)
          (hconnR : FordStronglyConnected (strictCount R))
          (hconnPlus :
            FordStronglyConnected (strictCount (addVoterProfile R p))),
          ∃ ρ : Fin 3 → ℝ,
            IsFullSupportLottery ρ ∧
              RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo hFord
                    (strictCount (addVoterProfile R p))
                    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
                    hconnPlus) x <
                RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo hFord (strictCount R)
                    (strictCount_isFordCountMatrix hR) hconnR) x := by
  refine ⟨rtbtInvProfileR, rtbtPrefABC, 0,
    rtbtInvProfileR_linear, rtbtPrefABC_linear,
    rtbtPrefABC_ranksTop_zero, rtbtInvProfileR_irreflexive,
    rtbtPrefABC_linear.1, rtbtInvProfileR_actual_fordStronglyConnected,
    rtbtInvProfileR_addVoter_actual_fordStronglyConnected, ?_⟩
  rcases exists_rtbtInvCubic_root_gt_three with ⟨r, hrgt, hroot⟩
  have hrpos : 0 < r := by nlinarith
  rcases rtbtInv_positive_involvement_limit_counterexample_of_root
      hβ hrgt hroot with ⟨ε, hεpos, hεlt, hdrop⟩
  refine ⟨twoPointReference ε,
    twoPointReference_fullSupport hεpos hεlt, ?_⟩
  rw [selectedBTOfFordZermelo_rtbtInvProfileR_eq_normalized
        hFord hrpos hroot,
      selectedBTOfFordZermelo_rtbtInvProfileR_addVoter_eq_normalized hFord,
      RTBTFromStrength_normalizeStrength
        (β := β) (ρ := twoPointReference ε)
        (u := rtbtInvStrengthR r) (rtbtInvStrengthR_pos hrpos),
      RTBTFromStrength_normalizeStrength
        (β := β) (ρ := twoPointReference ε)
        (u := rtbtInvStrengthRPlus) rtbtInvStrengthRPlus_pos]
  exact hdrop

/-- Genuine profile-level negative-involvement witness for selected RTBT,
using the reversed strict-linear-order profile and one actual added voter who
ranks the affected candidate last. -/
theorem InvolveViolRTBT_negative_profile_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β) :
    ∃ (R : Fin 3 → Fin 3 → Fin 3 → Bool)
        (p : Fin 3 → Fin 3 → Bool) (x : Fin 3),
      (∀ i, IsLinearPref (R i)) ∧
        IsLinearPref p ∧ RanksBottom p x ∧
        ∃ (hR : IsIrreflexiveProfile R)
          (hp : ∀ z, p z z = false)
          (hconnR : FordStronglyConnected (strictCount R))
          (hconnPlus :
            FordStronglyConnected (strictCount (addVoterProfile R p))),
          ∃ ρ : Fin 3 → ℝ,
            IsFullSupportLottery ρ ∧
              RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo hFord (strictCount R)
                    (strictCount_isFordCountMatrix hR) hconnR) x <
                RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo hFord
                    (strictCount (addVoterProfile R p))
                    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
                    hconnPlus) x := by
  refine ⟨rtbtInvProfileRReverse, rtbtPrefCBA, 0,
    rtbtInvProfileRReverse_linear, rtbtPrefCBA_linear,
    rtbtPrefCBA_ranksBottom_zero, rtbtInvProfileRReverse_irreflexive,
    rtbtPrefCBA_linear.1, rtbtInvProfileRReverse_actual_fordStronglyConnected,
    rtbtInvProfileRReverse_addVoter_actual_fordStronglyConnected, ?_⟩
  rcases exists_rtbtInvCubic_root_gt_three with ⟨r, hrgt, hroot⟩
  have hrpos : 0 < r := by nlinarith
  rcases rtbtInv_negative_involvement_limit_counterexample_of_root
      hβ hrgt hroot with ⟨ε, hεpos, hεlt, hincrease⟩
  refine ⟨twoPointReference ε,
    twoPointReference_fullSupport hεpos hεlt, ?_⟩
  rw [selectedBTOfFordZermelo_rtbtInvProfileRReverse_eq_normalized
        hFord hrpos hroot,
      selectedBTOfFordZermelo_rtbtInvProfileRReverse_addVoter_eq_normalized
        hFord,
      RTBTFromStrength_normalizeStrength
        (β := β) (ρ := twoPointReference ε)
        (u := rtbtInvStrengthRReverse r)
        (rtbtInvStrengthRReverse_pos hrpos),
      RTBTFromStrength_normalizeStrength
        (β := β) (ρ := twoPointReference ε)
        (u := rtbtInvStrengthRPlusReverse)
        rtbtInvStrengthRPlusReverse_pos]
  exact hincrease

/-- Bundled genuine profile-level positive and negative involvement
counterexamples for the actual selected RTBT rule. -/
theorem InvolveViolRTBT_profile_of_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β) :
    (∃ (R : Fin 3 → Fin 3 → Fin 3 → Bool)
        (p : Fin 3 → Fin 3 → Bool) (x : Fin 3),
      (∀ i, IsLinearPref (R i)) ∧
        IsLinearPref p ∧ RanksTop p x ∧
        ∃ (hR : IsIrreflexiveProfile R)
          (hp : ∀ z, p z z = false)
          (hconnR : FordStronglyConnected (strictCount R))
          (hconnPlus :
            FordStronglyConnected (strictCount (addVoterProfile R p))),
          ∃ ρ : Fin 3 → ℝ,
            IsFullSupportLottery ρ ∧
              RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo hFord
                    (strictCount (addVoterProfile R p))
                    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
                    hconnPlus) x <
                RTBTFromStrength β ρ
                  (selectedBTOfFordZermelo hFord (strictCount R)
                    (strictCount_isFordCountMatrix hR) hconnR) x) ∧
      (∃ (R : Fin 3 → Fin 3 → Fin 3 → Bool)
          (p : Fin 3 → Fin 3 → Bool) (x : Fin 3),
        (∀ i, IsLinearPref (R i)) ∧
          IsLinearPref p ∧ RanksBottom p x ∧
          ∃ (hR : IsIrreflexiveProfile R)
            (hp : ∀ z, p z z = false)
            (hconnR : FordStronglyConnected (strictCount R))
            (hconnPlus :
              FordStronglyConnected (strictCount (addVoterProfile R p))),
            ∃ ρ : Fin 3 → ℝ,
              IsFullSupportLottery ρ ∧
                RTBTFromStrength β ρ
                    (selectedBTOfFordZermelo hFord (strictCount R)
                      (strictCount_isFordCountMatrix hR) hconnR) x <
                  RTBTFromStrength β ρ
                    (selectedBTOfFordZermelo hFord
                      (strictCount (addVoterProfile R p))
                      (strictCount_addVoterProfile_isFordCountMatrix hR hp)
                      hconnPlus) x) :=
  ⟨InvolveViolRTBT_positive_profile_of_ford_zermelo hFord hβ,
    InvolveViolRTBT_negative_profile_of_ford_zermelo hFord hβ⟩

/-- Proposition `InvolveViolRTBT`, using Ford/Zermelo uniqueness to turn a
BT selector that returns normalized BT solutions on the four concrete margins
into the concrete algebraic selector equalities used by the counterexample. -/
theorem InvolveViolRTBT_from_ford_zermelo_BT_selector
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β)
    {BT : (Fin 3 → Fin 3 → ℝ) → Fin 3 → ℝ}
    (hBT : IsRTBTInvolvementBTSelector BT) :
    ViolatesPositiveInvolvement
        (fun M ρ => RTBTFromStrength β ρ (BT M))
        rtbtPositiveLinearAddsTopWitness ∧
      ViolatesNegativeInvolvement
        (fun M ρ => RTBTFromStrength β ρ (BT M))
        rtbtNegativeLinearAddsBottomWitness := by
  rcases exists_rtbtInvCubic_root_gt_three with ⟨r, hrgt, hroot⟩
  have hrpos : 0 < r := by nlinarith
  exact InvolveViolRTBT_from_concrete_normalized_BT_selection
    hβ hrgt hroot
    (rtbtInvProfileR_BT_selector_eq_normalized_of_ford_zermelo
      hFord hrpos hroot hBT.1)
    (rtbtInvProfileRPlus_BT_selector_eq_normalized_of_ford_zermelo
      hFord hBT.2.1)
    (rtbtInvProfileRReverse_BT_selector_eq_normalized_of_ford_zermelo
      hFord hrpos hroot hBT.2.2.1)
    (rtbtInvProfileRPlusReverse_BT_selector_eq_normalized_of_ford_zermelo
      hFord hBT.2.2.2)

/-- Proposition `InvolveViolRTBT` for the Ford/Zermelo-selected RTBT rule on
the concrete profiles in the proof.  The only remaining input is the cited
Ford/Zermelo theorem itself. -/
theorem InvolveViolRTBT_from_ford_zermelo
    (hFord : FordZermeloBTTheorem (Fin 3))
    {β : ℝ} (hβ : 0 < β) :
    ViolatesPositiveInvolvement
        (fun M ρ =>
          RTBTFromStrength β ρ (rtbtInvSelectedBTOfFordZermelo hFord M))
        rtbtPositiveLinearAddsTopWitness ∧
      ViolatesNegativeInvolvement
        (fun M ρ =>
          RTBTFromStrength β ρ (rtbtInvSelectedBTOfFordZermelo hFord M))
        rtbtNegativeLinearAddsBottomWitness :=
  InvolveViolRTBT_from_ford_zermelo_BT_selector hFord hβ
    (rtbtInvSelectedBTOfFordZermelo_is_selector hFord)

end PaperFormalization
