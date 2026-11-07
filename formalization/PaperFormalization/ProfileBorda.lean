import PaperFormalization.ProportionalBorda

open scoped BigOperators

namespace PaperFormalization

variable {α V : Type*}

/-- Boolean strict-preference indicators, coerced to real-valued counts. -/
def prefIndicator (b : Bool) : ℝ :=
  if b then 1 else 0

lemma prefIndicator_nonneg (b : Bool) : 0 ≤ prefIndicator b := by
  cases b <;> simp [prefIndicator]

lemma prefIndicator_le_one (b : Bool) : prefIndicator b ≤ 1 := by
  cases b <;> simp [prefIndicator]

lemma prefIndicator_le_of_imp {p q : Bool}
    (h : p = true → q = true) :
    prefIndicator p ≤ prefIndicator q := by
  cases p <;> cases q <;> simp [prefIndicator] at h ⊢

/-- Strict-domination Borda score of one alternative in a finite strict profile.
The partial-Borda score on weak relations is `partialBordaScoreP`. -/
noncomputable def strictDominationBordaScore
    [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (x : α) : ℝ :=
  Finset.sum Finset.univ (fun i =>
    Finset.sum (Finset.univ.erase x) (fun y => prefIndicator (R i x y)))

/-- Pairwise strict count matrix induced by a finite profile. -/
noncomputable def strictCount
    [Fintype V] (R : V → α → α → Bool) (x y : α) : ℝ :=
  Finset.sum Finset.univ (fun i => prefIndicator (R i x y))

/-- Profile-level improvement of candidate `x`, matching the monotonicity
definition in the paper: comparisons involving `x` only move in `x`'s favor,
and comparisons not involving `x` are unchanged. -/
def IsProfileImprovement
    (R R' : V → α → α → Bool) (x : α) : Prop :=
  (∀ i y, y ≠ x → R i x y = true → R' i x y = true) ∧
    (∀ i y, y ≠ x → R' i y x = true → R i y x = true) ∧
      ∀ i y z, y ≠ x → z ≠ x → R' i y z = R i y z

lemma strictDominationBordaScore_self_le_of_improvement
    [Fintype α] [DecidableEq α] [Fintype V]
    {R R' : V → α → α → Bool} {x : α}
    (h : IsProfileImprovement R R' x) :
    strictDominationBordaScore R x ≤ strictDominationBordaScore R' x := by
  classical
  unfold strictDominationBordaScore
  refine Finset.sum_le_sum ?_
  intro i hi
  refine Finset.sum_le_sum ?_
  intro y hy
  exact prefIndicator_le_of_imp (h.1 i y (Finset.mem_erase.mp hy).1)

lemma strictDominationBordaScore_other_le_of_improvement
    [Fintype α] [DecidableEq α] [Fintype V]
    {R R' : V → α → α → Bool} {x z : α}
    (h : IsProfileImprovement R R' x) (hzx : z ≠ x) :
    strictDominationBordaScore R' z ≤ strictDominationBordaScore R z := by
  classical
  unfold strictDominationBordaScore
  refine Finset.sum_le_sum ?_
  intro i hi
  refine Finset.sum_le_sum ?_
  intro y hy
  by_cases hyx : y = x
  · subst y
    exact prefIndicator_le_of_imp (h.2.1 i z hzx)
  · rw [h.2.2 i z y hzx hyx]

/-- The score-difference inequality used in the proof of `PBPM`, proved
from the concrete profile-level monotonicity assumptions. -/
theorem strictDominationBordaScore_diff_le_of_improvement
    [Fintype α] [DecidableEq α] [Fintype V]
    {R R' : V → α → α → Bool} {x z : α}
    (h : IsProfileImprovement R R' x) (hzx : z ≠ x) :
    strictDominationBordaScore R' z - strictDominationBordaScore R' x ≤
      strictDominationBordaScore R z - strictDominationBordaScore R x := by
  have hxle := strictDominationBordaScore_self_le_of_improvement (V := V) h
  have hzle := strictDominationBordaScore_other_le_of_improvement (V := V) h hzx
  linarith

/-- Profile-level version of Proposition `PBPM`, obtained by combining the
finite-profile score inequality above with the multiplicative PB proof. -/
theorem PBPM_from_profile_improvement
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R R' : V → α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (h : IsProfileImprovement R R' x) :
    proportionalBorda η ρ (strictDominationBordaScore R) x ≤
      proportionalBorda η ρ (strictDominationBordaScore R') x := by
  refine PBPM_from_score_differences hη hρnonneg hρx ?_
  intro z hzx
  exact strictDominationBordaScore_diff_le_of_improvement (V := V) h hzx

/-- Asymmetry of one added voter's strict preference relation. -/
def IsAsymmetricPref (p : α → α → Bool) : Prop :=
  ∀ ⦃x y : α⦄, p x y = true → p y x = false

def RanksTop (p : α → α → Bool) (x : α) : Prop :=
  ∀ y : α, y ≠ x → p x y = true

def RanksBottom (p : α → α → Bool) (x : α) : Prop :=
  ∀ y : α, y ≠ x → p y x = true

/-- Add one new voter, represented by `none`, to an existing profile. -/
def addVoterProfile
    (R : V → α → α → Bool) (p : α → α → Bool) :
    Option V → α → α → Bool
  | none => p
  | some i => R i

/-- Partial-Borda contribution of one added voter. -/
noncomputable def singleVoterBorda
    [Fintype α] [DecidableEq α] (p : α → α → Bool) (x : α) : ℝ :=
  Finset.sum (Finset.univ.erase x) (fun y => prefIndicator (p x y))

lemma strictDominationBordaScore_addVoterProfile
    [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool) (p : α → α → Bool) (x : α) :
    strictDominationBordaScore (addVoterProfile R p) x =
      strictDominationBordaScore R x + singleVoterBorda p x := by
  classical
  unfold strictDominationBordaScore singleVoterBorda
  simp [addVoterProfile, add_comm]
  ring

lemma singleVoterBorda_top_self
    [Fintype α] [DecidableEq α]
    {p : α → α → Bool} {x : α}
    (htop : RanksTop p x) :
    singleVoterBorda p x = (Fintype.card α : ℝ) - 1 := by
  classical
  unfold singleVoterBorda
  calc
    Finset.sum (Finset.univ.erase x) (fun y => prefIndicator (p x y))
        = Finset.sum (Finset.univ.erase x) (fun _ => (1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp [prefIndicator, htop y (Finset.mem_erase.mp hy).1]
    _ = ((Finset.univ.erase x).card : ℝ) := by simp
    _ = (Fintype.card α : ℝ) - 1 := by
          rw [Finset.cast_card_erase_of_mem (R := ℝ) (by simp)]
          simp

lemma singleVoterBorda_top_other_le
    [Fintype α] [DecidableEq α]
    {p : α → α → Bool} {x z : α}
    (hasymm : IsAsymmetricPref p) (htop : RanksTop p x) (hzx : z ≠ x) :
    singleVoterBorda p z ≤ (Fintype.card α : ℝ) - 2 := by
  classical
  have hxmem : x ∈ (Finset.univ.erase z : Finset α) := by
    simp [hzx.symm]
  have hzxfalse : p z x = false := hasymm (htop z hzx)
  have hrestcard :
      (((Finset.univ.erase z).erase x).card : ℝ) =
        (Fintype.card α : ℝ) - 2 := by
    rw [Finset.cast_card_erase_of_mem (R := ℝ) hxmem]
    rw [Finset.cast_card_erase_of_mem (R := ℝ) (by simp : z ∈ (Finset.univ : Finset α))]
    simp
    ring
  unfold singleVoterBorda
  calc
    Finset.sum (Finset.univ.erase z) (fun y => prefIndicator (p z y))
        =
      prefIndicator (p z x) +
        Finset.sum ((Finset.univ.erase z).erase x)
          (fun y => prefIndicator (p z y)) := by
          rw [← Finset.add_sum_erase (s := Finset.univ.erase z)
            (f := fun y => prefIndicator (p z y)) hxmem]
    _ =
        Finset.sum ((Finset.univ.erase z).erase x)
          (fun y => prefIndicator (p z y)) := by
          simp [prefIndicator, hzxfalse]
    _ ≤
        Finset.sum ((Finset.univ.erase z).erase x) (fun _ => (1 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro y hy
          exact prefIndicator_le_one (p z y)
    _ = (((Finset.univ.erase z).erase x).card : ℝ) := by simp
    _ = (Fintype.card α : ℝ) - 2 := hrestcard

lemma singleVoterBorda_bottom_self
    [Fintype α] [DecidableEq α]
    {p : α → α → Bool} {x : α}
    (hasymm : IsAsymmetricPref p) (hbottom : RanksBottom p x) :
    singleVoterBorda p x = 0 := by
  classical
  unfold singleVoterBorda
  refine Finset.sum_eq_zero ?_
  intro y hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hfalse : p x y = false := hasymm (hbottom y hyx)
  simp [prefIndicator, hfalse]

lemma singleVoterBorda_bottom_other_ge
    [Fintype α] [DecidableEq α]
    {p : α → α → Bool} {x z : α}
    (hbottom : RanksBottom p x) (hzx : z ≠ x) :
    1 ≤ singleVoterBorda p z := by
  classical
  have hxmem : x ∈ (Finset.univ.erase z : Finset α) := by
    simp [hzx.symm]
  have hzxtrue : p z x = true := hbottom z hzx
  unfold singleVoterBorda
  calc
    (1 : ℝ) ≤
        prefIndicator (p z x) +
          Finset.sum ((Finset.univ.erase z).erase x)
            (fun y => prefIndicator (p z y)) := by
          have hrest_nonneg :
              0 ≤ Finset.sum ((Finset.univ.erase z).erase x)
                (fun y => prefIndicator (p z y)) := by
            refine Finset.sum_nonneg ?_
            intro y hy
            exact prefIndicator_nonneg (p z y)
          simp [prefIndicator, hzxtrue]
    _ =
        Finset.sum (Finset.univ.erase z) (fun y => prefIndicator (p z y)) := by
          rw [← Finset.add_sum_erase (s := Finset.univ.erase z)
            (f := fun y => prefIndicator (p z y)) hxmem]

/-- Positive involvement for PB from an explicitly added top-ranking voter. -/
theorem PBPPI_from_added_top_voter
    [Fintype α] [DecidableEq α] [Nonempty α]
    {η : ℝ} {ρ B : α → ℝ} {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hcard : 2 ≤ Fintype.card α)
    (hasymm : IsAsymmetricPref p) (htop : RanksTop p x) :
    proportionalBorda η ρ B x ≤
      proportionalBorda η ρ (fun z => B z + singleVoterBorda p z) x := by
  refine PBPPI_from_score_bounds hη hρnonneg hρx hcard ?_ ?_
  · rw [singleVoterBorda_top_self htop]
  · intro z hzx
    have hz := singleVoterBorda_top_other_le hasymm htop hzx
    linarith

/-- Profile-level positive involvement for PB from adding an actual top-ranking
voter to the profile. -/
theorem PBPPI_from_added_top_profile
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hcard : 2 ≤ Fintype.card α)
    (hasymm : IsAsymmetricPref p) (htop : RanksTop p x) :
    proportionalBorda η ρ (strictDominationBordaScore R) x ≤
      proportionalBorda η ρ (strictDominationBordaScore (addVoterProfile R p)) x := by
  have hscore :
      strictDominationBordaScore (addVoterProfile R p) =
        fun z => strictDominationBordaScore R z + singleVoterBorda p z := by
    funext z
    exact strictDominationBordaScore_addVoterProfile R p z
  rw [hscore]
  exact PBPPI_from_added_top_voter hη hρnonneg hρx hcard hasymm htop

/-- Negative involvement for PB from an explicitly added bottom-ranking voter. -/
theorem PBPNI_from_added_bottom_voter
    [Fintype α] [DecidableEq α] [Nonempty α]
    {η : ℝ} {ρ B : α → ℝ} {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hasymm : IsAsymmetricPref p) (hbottom : RanksBottom p x) :
    proportionalBorda η ρ (fun z => B z + singleVoterBorda p z) x ≤
      proportionalBorda η ρ B x := by
  refine PBPNI_from_score_bounds hη hρnonneg hρx ?_ ?_
  · rw [singleVoterBorda_bottom_self hasymm hbottom]
    ring
  · intro z hzx
    have hz := singleVoterBorda_bottom_other_ge hbottom hzx
    linarith

/-- Profile-level negative involvement for PB from adding an actual
bottom-ranking voter to the profile. -/
theorem PBPNI_from_added_bottom_profile
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z) (hρx : 0 < ρ x)
    (hasymm : IsAsymmetricPref p) (hbottom : RanksBottom p x) :
    proportionalBorda η ρ (strictDominationBordaScore (addVoterProfile R p)) x ≤
      proportionalBorda η ρ (strictDominationBordaScore R) x := by
  have hscore :
      strictDominationBordaScore (addVoterProfile R p) =
        fun z => strictDominationBordaScore R z + singleVoterBorda p z := by
    funext z
    exact strictDominationBordaScore_addVoterProfile R p z
  rw [hscore]
  exact PBPNI_from_added_bottom_voter hη hρnonneg hρx hasymm hbottom

/-! ## The paper's trivial `ρ(x) = 0` case, at the profile level

The primed statements below drop the `0 < ρ x` hypothesis, quantifying over
the paper's full reference domain `ρ ∈ Δ`; see
`proportionalBorda_eq_zero_of_ref_zero`. -/

/-- `PBPM` for `B^d` over the paper's full reference domain `ρ ∈ Δ`. -/
theorem PBPM_from_profile_improvement'
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R R' : V → α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (h : IsProfileImprovement R R' x) :
    proportionalBorda η ρ (strictDominationBordaScore R) x ≤
      proportionalBorda η ρ (strictDominationBordaScore R') x := by
  refine PBPM_from_score_differences' hη hρnonneg ?_
  intro z hzx
  exact strictDominationBordaScore_diff_le_of_improvement (V := V) h hzx

/-- Positive involvement for `B^d` over the paper's full reference domain. -/
theorem PBPPI_from_added_top_profile'
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hcard : 2 ≤ Fintype.card α)
    (hasymm : IsAsymmetricPref p) (htop : RanksTop p x) :
    proportionalBorda η ρ (strictDominationBordaScore R) x ≤
      proportionalBorda η ρ
        (strictDominationBordaScore (addVoterProfile R p)) x := by
  have hscore :
      strictDominationBordaScore (addVoterProfile R p) =
        fun z => strictDominationBordaScore R z + singleVoterBorda p z := by
    funext z
    exact strictDominationBordaScore_addVoterProfile R p z
  rw [hscore]
  refine PBPPI_from_score_bounds' hη hρnonneg hcard ?_ ?_
  · rw [singleVoterBorda_top_self htop]
  · intro z hzx
    have hz := singleVoterBorda_top_other_le hasymm htop hzx
    linarith

/-- Negative involvement for `B^d` over the paper's full reference domain. -/
theorem PBPNI_from_added_bottom_profile'
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ} {R : V → α → α → Bool}
    {p : α → α → Bool} {x : α}
    (hη : 0 ≤ η) (hρnonneg : ∀ z : α, 0 ≤ ρ z)
    (hasymm : IsAsymmetricPref p) (hbottom : RanksBottom p x) :
    proportionalBorda η ρ
        (strictDominationBordaScore (addVoterProfile R p)) x ≤
      proportionalBorda η ρ (strictDominationBordaScore R) x := by
  have hscore :
      strictDominationBordaScore (addVoterProfile R p) =
        fun z => strictDominationBordaScore R z + singleVoterBorda p z := by
    funext z
    exact strictDominationBordaScore_addVoterProfile R p z
  rw [hscore]
  refine PBPNI_from_score_bounds' hη hρnonneg ?_ ?_
  · rw [singleVoterBorda_bottom_self hasymm hbottom]
    ring
  · intro z hzx
    have hz := singleVoterBorda_bottom_other_ge hbottom hzx
    linarith

/-- Proposition `RTBTorder`, proportional-Borda profile form: applying
proportional Borda updates for two finite profiles commutes. -/
theorem proportionalBordaProfile_commutative
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ}
    (R S : V → α → α → Bool)
    (hρ : IsFullSupportLottery ρ) :
    proportionalBorda η
        (proportionalBorda η ρ (strictDominationBordaScore R))
        (strictDominationBordaScore S) =
      proportionalBorda η
        (proportionalBorda η ρ (strictDominationBordaScore S))
        (strictDominationBordaScore R) :=
  proportionalBorda_commutative (η := η) hρ.1

/-- Proportional Borda preserves full support at the finite-profile level. -/
theorem proportionalBordaProfile_fullSupport
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {η : ℝ} {ρ : α → ℝ}
    (R : V → α → α → Bool)
    (hρ : IsFullSupportLottery ρ) :
    IsFullSupportLottery
      (proportionalBorda η ρ (strictDominationBordaScore R)) :=
  proportionalBorda_fullSupport hρ.1

end PaperFormalization
