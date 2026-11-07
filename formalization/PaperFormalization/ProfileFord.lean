import PaperFormalization.FordZermelo
import PaperFormalization.ProfileBorda

open scoped BigOperators

namespace PaperFormalization

variable {α V : Type*}

/-- A Boolean strict-preference profile has no self-strict preferences. -/
def IsIrreflexiveProfile (R : V → α → α → Bool) : Prop :=
  ∀ i x, R i x x = false

lemma strictCount_nonneg
    [Fintype V] (R : V → α → α → Bool) (x y : α) :
    0 ≤ strictCount R x y := by
  classical
  unfold strictCount
  exact Finset.sum_nonneg (fun i _hi => prefIndicator_nonneg (R i x y))

lemma strictCount_le_card
    [Fintype V] (R : V → α → α → Bool) (x y : α) :
    strictCount R x y ≤ (Fintype.card V : ℝ) := by
  classical
  unfold strictCount
  calc
    Finset.univ.sum (fun i : V => prefIndicator (R i x y))
        ≤ Finset.univ.sum (fun _ : V => (1 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact prefIndicator_le_one (R i x y)
    _ = (Fintype.card V : ℝ) := by simp

lemma strictCount_self_eq_zero
    [Fintype V] {R : V → α → α → Bool}
    (hirr : IsIrreflexiveProfile R) (x : α) :
    strictCount R x x = 0 := by
  classical
  unfold strictCount
  refine Finset.sum_eq_zero ?_
  intro i _hi
  simp [prefIndicator, hirr i x]

/-- The strict-count matrix induced by an irreflexive finite profile satisfies
Ford's basic count-matrix side conditions. -/
theorem strictCount_isFordCountMatrix
    [Fintype α] [DecidableEq α] [Fintype V]
    {R : V → α → α → Bool}
    (hirr : IsIrreflexiveProfile R) :
    IsFordCountMatrix (strictCount R) :=
  ⟨strictCount_self_eq_zero hirr, strictCount_nonneg R⟩

lemma isIrreflexiveProfile_addVoterProfile
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R) (hp : ∀ x, p x x = false) :
    IsIrreflexiveProfile (addVoterProfile R p) := by
  intro i x
  cases i with
  | none =>
      exact hp x
  | some i =>
      exact hR i x

lemma strictCount_addVoterProfile
    [Fintype V] (R : V → α → α → Bool) (p : α → α → Bool)
    (x y : α) :
    strictCount (addVoterProfile R p) x y =
      strictCount R x y + prefIndicator (p x y) := by
  classical
  unfold strictCount
  simp [addVoterProfile, add_comm]

lemma strictCount_le_addVoterProfile
    [Fintype V] (R : V → α → α → Bool) (p : α → α → Bool)
    (x y : α) :
    strictCount R x y ≤ strictCount (addVoterProfile R p) x y := by
  rw [strictCount_addVoterProfile]
  exact le_add_of_nonneg_right (prefIndicator_nonneg (p x y))

/-- Adding one voter preserves Ford strong connectivity of the strict-count
graph, because it can only add positive-count edges. -/
theorem FordStronglyConnected_strictCount_addVoterProfile
    [Fintype α] [DecidableEq α] [Fintype V]
    {R : V → α → α → Bool} (p : α → α → Bool)
    (hconn : FordStronglyConnected (strictCount R)) :
    FordStronglyConnected (strictCount (addVoterProfile R p)) := by
  refine FordStronglyConnected_mono ?_ hconn
  intro x y hpos
  have hle := strictCount_le_addVoterProfile R p x y
  linarith

/-- Adding one voter preserves Ford's original partition assumption for the
strict-count graph, because it can only add positive-count edges. -/
theorem FordPartitionAssumption_strictCount_addVoterProfile
    [Fintype α] [DecidableEq α] [Fintype V]
    {R : V → α → α → Bool} (p : α → α → Bool)
    (hpart : FordPartitionAssumption (strictCount R)) :
    FordPartitionAssumption (strictCount (addVoterProfile R p)) := by
  refine FordPartitionAssumption_mono ?_ hpart
  intro x y hpos
  have hle := strictCount_le_addVoterProfile R p x y
  linarith

theorem strictCount_addVoterProfile_isFordCountMatrix
    [Fintype α] [DecidableEq α] [Fintype V]
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R) (hp : ∀ x, p x x = false) :
    IsFordCountMatrix (strictCount (addVoterProfile R p)) :=
  strictCount_isFordCountMatrix
    (isIrreflexiveProfile_addVoterProfile hR hp)

/-- The profile strict-count Ford likelihood is bounded by `1` on positive
Bradley--Terry strength vectors. -/
lemma fordBTProductObjective_strictCountProfile_le_one_of_pos
    [Fintype α] [DecidableEq α] [Fintype V]
    (R : V → α → α → Bool)
    {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    fordBTProductObjective (strictCount R) u ≤ 1 :=
  fordBTProductObjective_le_one_of_pos (strictCount_nonneg R) hu

/-- Profile form of Ford's boundary exclusion: under Ford connectivity, any
positive point has strictly larger product likelihood than a simplex-boundary
strict-count profile point. -/
theorem fordBTProductObjective_strictCountProfile_boundary_lt_of_pos
    [Fintype α] [DecidableEq α] [Fintype V]
    {R : V → α → α → Bool} {u v : α → ℝ}
    (hconn : FordStronglyConnected (strictCount R))
    (hnonneg : ∀ z : α, 0 ≤ u z)
    (hsum : Finset.sum Finset.univ (fun z : α => u z) = 1)
    {x : α}
    (hx : u x = 0)
    (hv : ∀ z : α, 0 < v z) :
    fordBTProductObjective (strictCount R) u <
      fordBTProductObjective (strictCount R) v :=
  fordBTProductObjective_boundary_lt_of_pos hconn hnonneg hsum hx hv

/-- Profile form of Ford's boundary exclusion stated directly for lottery
boundary points and full-support interior points. -/
theorem fordBTProductObjective_strictCountProfile_lottery_boundary_lt_fullSupport
    [Fintype α] [DecidableEq α] [Fintype V]
    {R : V → α → α → Bool} {u v : α → ℝ}
    (hconn : FordStronglyConnected (strictCount R))
    (hu : IsLottery u)
    (hboundary : ∃ x : α, u x = 0)
    (hv : IsFullSupportLottery v) :
    fordBTProductObjective (strictCount R) u <
      fordBTProductObjective (strictCount R) v :=
  fordBTProductObjective_lottery_boundary_lt_fullSupport
    hconn hu hboundary hv

lemma strictCount_improved_candidate_le_of_profile_improvement
    [Fintype V]
    {R R' : V → α → α → Bool} {x y : α}
    (h : IsProfileImprovement R R' x) (hyx : y ≠ x) :
    strictCount R x y ≤ strictCount R' x y := by
  classical
  unfold strictCount
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact prefIndicator_le_of_imp (h.1 i y hyx)

lemma strictCount_against_improved_candidate_le_of_profile_improvement
    [Fintype V]
    {R R' : V → α → α → Bool} {x y : α}
    (h : IsProfileImprovement R R' x) (hyx : y ≠ x) :
    strictCount R' y x ≤ strictCount R y x := by
  classical
  unfold strictCount
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact prefIndicator_le_of_imp (h.2.1 i y hyx)

lemma strictCount_other_eq_of_profile_improvement
    [Fintype V]
    {R R' : V → α → α → Bool} {x y z : α}
    (h : IsProfileImprovement R R' x) (hyx : y ≠ x) (hzx : z ≠ x) :
    strictCount R' y z = strictCount R y z := by
  classical
  unfold strictCount
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [h.2.2 i y z hyx hzx]

/-- Unnormalized strict pairwise margin induced by a finite profile. -/
noncomputable def strictMargin
    [Fintype V] (R : V → α → α → Bool) (x y : α) : ℝ :=
  strictCount R x y - strictCount R y x

lemma strictMargin_skew
    [Fintype V] (R : V → α → α → Bool) (x y : α) :
    strictMargin R y x = -strictMargin R x y := by
  unfold strictMargin
  ring

lemma strictMargin_self_eq_zero
    [Fintype V] (R : V → α → α → Bool) (x : α) :
    strictMargin R x x = 0 := by
  unfold strictMargin
  ring

lemma strictMargin_abs_le_card
    [Fintype V] (R : V → α → α → Bool) (x y : α) :
    |strictMargin R x y| ≤ (Fintype.card V : ℝ) := by
  have hxy_nonneg := strictCount_nonneg R x y
  have hyx_nonneg := strictCount_nonneg R y x
  have hxy_le := strictCount_le_card R x y
  have hyx_le := strictCount_le_card R y x
  rw [abs_le]
  unfold strictMargin
  constructor <;> linarith

/-- Normalized pairwise strict margin induced by a nonempty finite profile.
For linear-order profiles this is the paper's usual average margin. -/
noncomputable def normalizedStrictMargin
    [Fintype V] (R : V → α → α → Bool) (x y : α) : ℝ :=
  strictMargin R x y / (Fintype.card V : ℝ)

theorem normalizedStrictMargin_isNormalizedMarginMatrix
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (R : V → α → α → Bool) :
    IsNormalizedMarginMatrix (normalizedStrictMargin R) := by
  have hcardpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card V)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    unfold normalizedStrictMargin
    rw [strictMargin_self_eq_zero]
    simp
  · intro x y
    unfold normalizedStrictMargin
    rw [strictMargin_skew]
    ring
  · intro x y
    unfold normalizedStrictMargin
    rw [abs_div, abs_of_pos hcardpos]
    exact (div_le_one hcardpos).mpr (strictMargin_abs_le_card R x y)

lemma strictMargin_improved_candidate_le_of_profile_improvement
    [Fintype V]
    {R R' : V → α → α → Bool} {x y : α}
    (h : IsProfileImprovement R R' x) (hyx : y ≠ x) :
    strictMargin R x y ≤ strictMargin R' x y := by
  have hxy :=
    strictCount_improved_candidate_le_of_profile_improvement h hyx
  have hyx' :=
    strictCount_against_improved_candidate_le_of_profile_improvement h hyx
  unfold strictMargin
  linarith

lemma strictMargin_other_eq_of_profile_improvement
    [Fintype V]
    {R R' : V → α → α → Bool} {x y z : α}
    (h : IsProfileImprovement R R' x) (hyx : y ≠ x) (hzx : z ≠ x) :
    strictMargin R' y z = strictMargin R y z := by
  unfold strictMargin
  rw [strictCount_other_eq_of_profile_improvement h hyx hzx,
    strictCount_other_eq_of_profile_improvement h hzx hyx]

/-- A profile-level improvement induces the matrix-level improvement relation
for normalized strict margins. -/
theorem normalizedStrictMargin_improvement_of_profile_improvement
    [Fintype V] [Nonempty V]
    {R R' : V → α → α → Bool} {x : α}
    (h : IsProfileImprovement R R' x) :
    IsImprovementOf (normalizedStrictMargin R) (normalizedStrictMargin R') x := by
  have hcardpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card V)
  refine ⟨?_, ?_, ?_⟩
  · intro y hyx
    unfold normalizedStrictMargin
    exact div_le_div_of_nonneg_right
      (strictMargin_improved_candidate_le_of_profile_improvement h hyx)
      hcardpos.le
  · intro y _hyx
    unfold normalizedStrictMargin
    rw [strictMargin_skew]
    ring
  · intro y z hyx hzx
    unfold normalizedStrictMargin
    rw [strictMargin_other_eq_of_profile_improvement h hyx hzx]

/-- Profile-level probabilistic monotonicity for a matrix rule, after finite
profiles are interpreted through normalized strict margins. -/
def SatisfiesProfileProbabilisticMonotonicity
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (F : MatrixRule α) : Prop :=
  ∀ (R R' : V → α → α → Bool) (ρ : α → ℝ) (x : α),
    IsFullSupportLottery ρ →
      IsProfileImprovement R R' x →
        F (normalizedStrictMargin R) ρ x ≤
          F (normalizedStrictMargin R') ρ x

/-- Matrix-level probabilistic monotonicity implies profile-level
probabilistic monotonicity for normalized strict margins. -/
theorem profileProbabilisticMonotonicity_of_matrix
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {F : MatrixRule α}
    (hF : SatisfiesProbabilisticMonotonicity F) :
    SatisfiesProfileProbabilisticMonotonicity (V := V) F := by
  intro R R' ρ x hρ h
  exact hF (normalizedStrictMargin R) (normalizedStrictMargin R') ρ x
    (normalizedStrictMargin_isNormalizedMarginMatrix R)
    (normalizedStrictMargin_isNormalizedMarginMatrix R') hρ
    (normalizedStrictMargin_improvement_of_profile_improvement h)

/-- Any matrix-level monotone rule is monotone for profile improvements after
passing profiles to their normalized strict-margin matrices. -/
theorem profile_monotonicity_of_matrix_monotonicity
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {F : MatrixRule α}
    (hF : SatisfiesProbabilisticMonotonicity F)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (h : IsProfileImprovement R R' x) :
    F (normalizedStrictMargin R) ρ x ≤
      F (normalizedStrictMargin R') ρ x :=
  profileProbabilisticMonotonicity_of_matrix (V := V) hF R R' ρ x hρ h

/-- Proposition `BTProp`, profile-count form using the normalized
Bradley--Terry selector obtained from Ford/Zermelo. -/
theorem selectedBTOfFordZermelo_strictCountProfile_isBTStrength
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    IsBTStrength (fordPairTotal (strictCount R)) (strictCount R)
      (selectedBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn) :=
  selectedBTOfFordZermelo_isBTStrength hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Proposition `BTProp`, profile-count form using the Ford/Zermelo selector
taken directly from the normalized maximum-likelihood certificate. -/
theorem selectedFordBTOfFordZermelo_strictCountProfile_isBTStrength
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    IsBTStrength (fordPairTotal (strictCount R)) (strictCount R)
      (selectedFordBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn) :=
  selectedFordBTOfFordZermelo_isBTStrength hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count form of the full-support conclusion for the normalized
Bradley--Terry selector obtained from Ford/Zermelo. -/
theorem selectedBTOfFordZermelo_strictCountProfile_fullSupport
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    IsFullSupportLottery
      (selectedBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn) :=
  selectedBTOfFordZermelo_fullSupport hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count form of the full-support conclusion for the Ford/Zermelo
selector taken directly from the normalized maximum-likelihood certificate. -/
theorem selectedFordBTOfFordZermelo_strictCountProfile_fullSupport
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    IsFullSupportLottery
      (selectedFordBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn) :=
  selectedFordBTOfFordZermelo_fullSupport hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count form of Ford's displayed equations for the normalized
Bradley--Terry selector obtained from Ford/Zermelo. -/
theorem selectedBTOfFordZermelo_strictCountProfile_satisfiesFordEquations
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    SatisfiesFordBTEquations (strictCount R)
      (selectedBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn) :=
  selectedBTOfFordZermelo_satisfiesFordEquations hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count form of Ford's original product-likelihood maximizer
statement for the normalized Bradley--Terry selector. -/
theorem selectedBTOfFordZermelo_strictCountProfile_productMaximizer
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    HasFordNormalizedBTProductMaximizer (strictCount R)
      (selectedBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn) :=
  selectedBTOfFordZermelo_productMaximizer hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count form of Ford's displayed equations for the Ford/Zermelo
selector taken directly from the normalized maximum-likelihood certificate. -/
theorem selectedFordBTOfFordZermelo_strictCountProfile_satisfiesFordEquations
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    SatisfiesFordBTEquations (strictCount R)
      (selectedFordBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn) :=
  selectedFordBTOfFordZermelo_satisfiesFordEquations hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count form of Ford's original product-likelihood maximizer
statement for the selector taken directly from the normalized
maximum-likelihood certificate. -/
theorem selectedFordBTOfFordZermelo_strictCountProfile_productMaximizer
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    HasFordNormalizedBTProductMaximizer (strictCount R)
      (selectedFordBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn) :=
  selectedFordBTOfFordZermelo_productMaximizer hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count form of Ford/Zermelo existence and uniqueness for
normalized Bradley--Terry strengths. -/
theorem exists_unique_ford_BTStrength_strictCountProfile_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      IsBTStrength (fordPairTotal (strictCount R)) (strictCount R) u :=
  exists_unique_ford_BTStrength_of_ford_zermelo hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count Ford/Zermelo existence and uniqueness using Ford's original
partition formulation on the strict-count matrix. -/
theorem exists_unique_ford_BTStrength_strictCountProfile_of_ford_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hpart : FordPartitionAssumption (strictCount R)) :
    ∃! u : α → ℝ,
      IsBTStrength (fordPairTotal (strictCount R)) (strictCount R) u :=
  exists_unique_ford_BTStrength_of_ford_partitionAssumption hFord
    (strictCount_isFordCountMatrix hR) hpart

/-- Profile-count form of Ford's normalized log-likelihood existence and
uniqueness conclusion. -/
theorem exists_unique_ford_normalizedBTMaximizer_strictCountProfile_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ, HasFordNormalizedBTMaximizer (strictCount R) u :=
  exists_unique_ford_normalizedBTMaximizer_of_ford_zermelo hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count normalized log-likelihood existence and uniqueness using
Ford's original partition formulation. -/
theorem exists_unique_ford_normalizedBTMaximizer_strictCountProfile_of_ford_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hpart : FordPartitionAssumption (strictCount R)) :
    ∃! u : α → ℝ, HasFordNormalizedBTMaximizer (strictCount R) u :=
  exists_unique_ford_normalizedBTMaximizer_of_ford_partitionAssumption hFord
    (strictCount_isFordCountMatrix hR) hpart

/-- Profile-count form of Ford's original product-likelihood existence and
uniqueness conclusion. -/
theorem exists_unique_ford_normalizedBTProductMaximizer_strictCountProfile_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ, HasFordNormalizedBTProductMaximizer (strictCount R) u :=
  exists_unique_ford_normalizedBTProductMaximizer_of_ford_zermelo hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count product-likelihood existence and uniqueness using Ford's
original partition formulation. -/
theorem exists_unique_ford_normalizedBTProductMaximizer_strictCountProfile_of_ford_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hpart : FordPartitionAssumption (strictCount R)) :
    ∃! u : α → ℝ, HasFordNormalizedBTProductMaximizer (strictCount R) u :=
  exists_unique_ford_normalizedBTProductMaximizer_of_ford_partitionAssumption
    hFord (strictCount_isFordCountMatrix hR) hpart

/-- Profile-count form of the combined Ford-style `BTProp` certificate. -/
theorem exists_unique_ford_BTProp_certificate_strictCountProfile_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      HasFordBTPropCertificate
        (fordPairTotal (strictCount R)) (strictCount R) u :=
  exists_unique_ford_BTProp_certificate_of_ford_zermelo hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count Ford-style certificate existence and uniqueness using
Ford's original partition formulation. -/
theorem exists_unique_ford_BTProp_certificate_strictCountProfile_of_ford_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hpart : FordPartitionAssumption (strictCount R)) :
    ∃! u : α → ℝ,
      HasFordBTPropCertificate
        (fordPairTotal (strictCount R)) (strictCount R) u :=
  exists_unique_ford_BTProp_certificate_of_ford_partitionAssumption hFord
    (strictCount_isFordCountMatrix hR) hpart

/-- Profile-count form of the combined `BTProp` certificate. -/
theorem exists_unique_BTProp_certificate_strictCountProfile_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      HasBTPropCertificate
        (fordPairTotal (strictCount R)) (strictCount R) u :=
  exists_unique_BTProp_certificate_of_ford_zermelo hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Profile-count combined `BTProp` certificate existence and uniqueness
using Ford's original partition formulation. -/
theorem exists_unique_BTProp_certificate_strictCountProfile_of_ford_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hpart : FordPartitionAssumption (strictCount R)) :
    ∃! u : α → ℝ,
      HasBTPropCertificate
        (fordPairTotal (strictCount R)) (strictCount R) u :=
  exists_unique_BTProp_certificate_of_ford_partitionAssumption hFord
    (strictCount_isFordCountMatrix hR) hpart

/-- The two profile-count Ford/Zermelo selectors coincide by uniqueness of the
normalized Bradley--Terry strength vector. -/
theorem selectedBTOfFordZermelo_strictCountProfile_eq_selectedFordBT
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R)) :
    selectedBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn =
      selectedFordBTOfFordZermelo hFord (strictCount R)
        (strictCount_isFordCountMatrix hR) hconn :=
  selectedBTOfFordZermelo_eq_selectedFordBTOfFordZermelo hFord
    (strictCount_isFordCountMatrix hR) hconn

/-- Proposition `DPOasRTBT`, profile-count form: for a finite irreflexive
profile whose strict-count graph satisfies Ford connectivity, the DPO argmax
set is the singleton RTBT lottery selected from Ford/Zermelo's normalized
maximum-likelihood theorem. -/
theorem DPOasRTBT_strictCountProfile_selectedFordBT
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    dpoArgmaxSet β (strictCount R) ρ =
      ({RTBTFromStrength β ρ
          (selectedFordBTOfFordZermelo hFord (strictCount R)
            (strictCount_isFordCountMatrix hR) hconn)} : Set (α → ℝ)) :=
  DPOasRTBT_selectedFordBTOfFordZermelo hFord hβ hρ
    (strictCount_isFordCountMatrix hR) hconn

/-- Proposition `DPOasRTBT`, profile-count form using the normalized
Bradley--Terry selector obtained after the Ford/Zermelo-to-DPO bridge. -/
theorem DPOasRTBT_strictCountProfile_selectedBT
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    dpoArgmaxSet β (strictCount R) ρ =
      ({RTBTFromStrength β ρ
          (selectedBTOfFordZermelo hFord (strictCount R)
            (strictCount_isFordCountMatrix hR) hconn)} : Set (α → ℝ)) :=
  DPOasRTBT_selectedBTOfFordZermelo hFord hβ hρ
    (strictCount_isFordCountMatrix hR) hconn

/-- Existential profile-count form of `DPOasRTBT`: a finite irreflexive profile
with Ford-connected strict-count graph has a Bradley--Terry certificate whose
RTBT lottery is exactly the DPO argmax singleton. -/
theorem exists_DPOasRTBT_strictCountProfile_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal (strictCount R)) (strictCount R) u ∧
        dpoArgmaxSet β (strictCount R) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_ford_zermelo hFord hβ hρ
    (strictCount_isFordCountMatrix hR) hconn

/-- Existential profile-count form of `DPOasRTBT` using Ford's original
partition formulation on the strict-count matrix. -/
theorem exists_DPOasRTBT_strictCountProfile_of_ford_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hpart : FordPartitionAssumption (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal (strictCount R)) (strictCount R) u ∧
        dpoArgmaxSet β (strictCount R) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_ford_zermelo_partitionAssumption hFord hβ hρ
    (strictCount_isFordCountMatrix hR) hpart

/-- Adding an irreflexive voter to a profile preserves the hypotheses needed
for the profile-count `DPOasRTBT` theorem. -/
theorem DPOasRTBT_strictCountProfile_addVoter_selectedFordBT
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {p : α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    dpoArgmaxSet β (strictCount (addVoterProfile R p)) ρ =
      ({RTBTFromStrength β ρ
          (selectedFordBTOfFordZermelo hFord
            (strictCount (addVoterProfile R p))
            (strictCount_addVoterProfile_isFordCountMatrix hR hp)
            (FordStronglyConnected_strictCount_addVoterProfile p hconn))} :
        Set (α → ℝ)) :=
  DPOasRTBT_selectedFordBTOfFordZermelo hFord hβ hρ
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Adding an irreflexive voter preserves the profile-count hypotheses for
the normalized Bradley--Terry strength selected from Ford/Zermelo. -/
theorem selectedBTOfFordZermelo_strictCountProfile_addVoter_isBTStrength
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    IsBTStrength
      (fordPairTotal (strictCount (addVoterProfile R p)))
      (strictCount (addVoterProfile R p))
      (selectedBTOfFordZermelo hFord
        (strictCount (addVoterProfile R p))
        (strictCount_addVoterProfile_isFordCountMatrix hR hp)
        (FordStronglyConnected_strictCount_addVoterProfile p hconn)) :=
  selectedBTOfFordZermelo_isBTStrength hFord
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Adding an irreflexive voter preserves the profile-count hypotheses for
the Ford/Zermelo selector taken directly from the normalized maximum-likelihood
certificate. -/
theorem selectedFordBTOfFordZermelo_strictCountProfile_addVoter_isBTStrength
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    IsBTStrength
      (fordPairTotal (strictCount (addVoterProfile R p)))
      (strictCount (addVoterProfile R p))
      (selectedFordBTOfFordZermelo hFord
        (strictCount (addVoterProfile R p))
        (strictCount_addVoterProfile_isFordCountMatrix hR hp)
        (FordStronglyConnected_strictCount_addVoterProfile p hconn)) :=
  selectedFordBTOfFordZermelo_isBTStrength hFord
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Add-voter profile-count form of Ford/Zermelo existence and uniqueness for
normalized Bradley--Terry strengths. -/
theorem exists_unique_ford_BTStrength_strictCountProfile_addVoter_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      IsBTStrength
        (fordPairTotal (strictCount (addVoterProfile R p)))
        (strictCount (addVoterProfile R p)) u :=
  exists_unique_ford_BTStrength_of_ford_zermelo hFord
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Add-voter profile-count form of Ford's normalized log-likelihood
existence and uniqueness conclusion. -/
theorem exists_unique_ford_normalizedBTMaximizer_strictCountProfile_addVoter_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      HasFordNormalizedBTMaximizer (strictCount (addVoterProfile R p)) u :=
  exists_unique_ford_normalizedBTMaximizer_of_ford_zermelo hFord
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Add-voter profile-count form of Ford's original product-likelihood
existence and uniqueness conclusion. -/
theorem exists_unique_ford_normalizedBTProductMaximizer_strictCountProfile_addVoter_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      HasFordNormalizedBTProductMaximizer
        (strictCount (addVoterProfile R p)) u :=
  exists_unique_ford_normalizedBTProductMaximizer_of_ford_zermelo hFord
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Add-voter profile-count form of the combined Ford-style `BTProp`
certificate. -/
theorem exists_unique_ford_BTProp_certificate_strictCountProfile_addVoter_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      HasFordBTPropCertificate
        (fordPairTotal (strictCount (addVoterProfile R p)))
        (strictCount (addVoterProfile R p)) u :=
  exists_unique_ford_BTProp_certificate_of_ford_zermelo hFord
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Add-voter profile-count form of the combined `BTProp` certificate. -/
theorem exists_unique_BTProp_certificate_strictCountProfile_addVoter_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R)) :
    ∃! u : α → ℝ,
      HasBTPropCertificate
        (fordPairTotal (strictCount (addVoterProfile R p)))
        (strictCount (addVoterProfile R p)) u :=
  exists_unique_BTProp_certificate_of_ford_zermelo hFord
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Add-voter combined `BTProp` certificate existence and uniqueness using
Ford's original partition formulation on the original strict-count matrix. -/
theorem exists_unique_BTProp_certificate_strictCountProfile_addVoter_of_ford_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {R : V → α → α → Bool} {p : α → α → Bool}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hpart : FordPartitionAssumption (strictCount R)) :
    ∃! u : α → ℝ,
      HasBTPropCertificate
        (fordPairTotal (strictCount (addVoterProfile R p)))
        (strictCount (addVoterProfile R p)) u :=
  exists_unique_BTProp_certificate_of_ford_partitionAssumption hFord
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordPartitionAssumption_strictCount_addVoterProfile p hpart)

/-- Adding an irreflexive voter also preserves the hypotheses for the
normalized Bradley--Terry selector form of the profile-count `DPOasRTBT`
theorem. -/
theorem DPOasRTBT_strictCountProfile_addVoter_selectedBT
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {p : α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    dpoArgmaxSet β (strictCount (addVoterProfile R p)) ρ =
      ({RTBTFromStrength β ρ
          (selectedBTOfFordZermelo hFord
            (strictCount (addVoterProfile R p))
            (strictCount_addVoterProfile_isFordCountMatrix hR hp)
            (FordStronglyConnected_strictCount_addVoterProfile p hconn))} :
        Set (α → ℝ)) :=
  DPOasRTBT_selectedBTOfFordZermelo hFord hβ hρ
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Existential add-voter form of `DPOasRTBT`: after adding an irreflexive
voter, Ford/Zermelo supplies a Bradley--Terry certificate whose RTBT lottery is
the DPO argmax singleton. -/
theorem exists_DPOasRTBT_strictCountProfile_addVoter_of_ford_zermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {p : α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    ∃ u : α → ℝ,
      HasBTPropCertificate
          (fordPairTotal (strictCount (addVoterProfile R p)))
          (strictCount (addVoterProfile R p)) u ∧
        dpoArgmaxSet β (strictCount (addVoterProfile R p)) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_ford_zermelo hFord hβ hρ
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordStronglyConnected_strictCount_addVoterProfile p hconn)

/-- Existential add-voter form of `DPOasRTBT` using Ford's original partition
formulation on the original strict-count matrix. -/
theorem exists_DPOasRTBT_strictCountProfile_addVoter_of_ford_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {p : α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hpart : FordPartitionAssumption (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    ∃ u : α → ℝ,
      HasBTPropCertificate
          (fordPairTotal (strictCount (addVoterProfile R p)))
          (strictCount (addVoterProfile R p)) u ∧
        dpoArgmaxSet β (strictCount (addVoterProfile R p)) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_ford_zermelo_partitionAssumption hFord hβ hρ
    (strictCount_addVoterProfile_isFordCountMatrix hR hp)
    (FordPartitionAssumption_strictCount_addVoterProfile p hpart)

/-- Existential profile-count `DPOasRTBT` with Ford/Zermelo discharged by the
proved finite theorem. -/
theorem exists_DPOasRTBT_strictCountProfile
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal (strictCount R)) (strictCount R) u ∧
        dpoArgmaxSet β (strictCount R) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  exists_DPOasRTBT_strictCountProfile_of_ford_zermelo
    FordZermeloBTTheorem_finite hβ hR hconn hρ

/-- Partition-assumption profile-count `DPOasRTBT` with Ford/Zermelo discharged
by the proved finite theorem. -/
theorem exists_DPOasRTBT_strictCountProfile_of_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hpart : FordPartitionAssumption (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal (strictCount R)) (strictCount R) u ∧
        dpoArgmaxSet β (strictCount R) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  exists_DPOasRTBT_strictCountProfile_of_ford_partitionAssumption
    FordZermeloBTTheorem_finite hβ hR hpart hρ

/-- Existential add-voter profile-count `DPOasRTBT` with Ford/Zermelo discharged
by the proved finite theorem. -/
theorem exists_DPOasRTBT_strictCountProfile_addVoter
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {p : α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    ∃ u : α → ℝ,
      HasBTPropCertificate
          (fordPairTotal (strictCount (addVoterProfile R p)))
          (strictCount (addVoterProfile R p)) u ∧
        dpoArgmaxSet β (strictCount (addVoterProfile R p)) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  exists_DPOasRTBT_strictCountProfile_addVoter_of_ford_zermelo
    FordZermeloBTTheorem_finite hβ hR hp hconn hρ

/-- Add-voter partition-assumption profile-count `DPOasRTBT` with Ford/Zermelo
discharged by the proved finite theorem. -/
theorem exists_DPOasRTBT_strictCountProfile_addVoter_of_partitionAssumption
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    {β : ℝ} (hβ : 0 < β)
    {R : V → α → α → Bool} {p : α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hp : ∀ x : α, p x x = false)
    (hpart : FordPartitionAssumption (strictCount R))
    (hρ : ∀ x : α, 0 < ρ x) :
    ∃ u : α → ℝ,
      HasBTPropCertificate
          (fordPairTotal (strictCount (addVoterProfile R p)))
          (strictCount (addVoterProfile R p)) u ∧
        dpoArgmaxSet β (strictCount (addVoterProfile R p)) ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  exists_DPOasRTBT_strictCountProfile_addVoter_of_ford_partitionAssumption
    FordZermeloBTTheorem_finite hβ hR hp hpart hρ

end PaperFormalization
