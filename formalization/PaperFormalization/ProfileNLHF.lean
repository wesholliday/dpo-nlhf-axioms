import PaperFormalization.NLHFSelectedMonotonicity
import PaperFormalization.ProfileFord

open scoped BigOperators

namespace PaperFormalization

variable {α V : Type*}

/-- Profile-level NLHF existence and uniqueness from the strict-KL
fixed-point existence interface. -/
theorem exists_unique_nlhfFixedPoint_profile_of_sionStrictKL
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ,
      IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ π :=
  exists_unique_nlhfFixedPoint_of_sionStrictKL hexists hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- Profile-level regularized saddle-pair existence and uniqueness from the
strict-KL fixed-point existence interface. -/
theorem exists_unique_nlhfRegularizedSaddlePair_profile_of_sionStrictKL
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedSaddle τ (normalizedStrictMargin R) ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedSaddlePair_of_sionStrictKLFixedPoint
    hexists hτ (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- The selected strict-KL NLHF rule is a fixed point on every finite profile's
normalized strict margin. -/
theorem selectedNLHFOfSionStrictKL_profile_fixedPoint
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ
      (selectedNLHFOfSionStrictKL hexists τ (normalizedStrictMargin R) ρ) :=
  selectedNLHFOfSionStrictKL_selection hexists hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- The selected strict-KL NLHF rule equals any profile-level fixed point. -/
theorem selectedNLHFOfSionStrictKL_profile_eq_of_fixedPoint
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} {R : V → α → α → Bool} {ρ π : α → ℝ}
    (hπ : IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ π) :
    selectedNLHFOfSionStrictKL hexists τ (normalizedStrictMargin R) ρ = π :=
  selectedNLHFOfSionStrictKL_eq_of_fixedPoint hexists
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hπ

/-- Profile-level NLHF existence and uniqueness from the proved Sion
specialization. -/
theorem exists_unique_nlhfFixedPoint_profile
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ,
      IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ π :=
  exists_unique_nlhfFixedPoint hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- Profile-level regularized saddle-pair existence and uniqueness from the
proved Sion specialization. -/
theorem exists_unique_nlhfRegularizedSaddlePair_profile
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedSaddle τ (normalizedStrictMargin R) ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedSaddlePair hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- Profile-level closed-simplex saddle-pair existence and uniqueness from the
proved Sion specialization. -/
theorem exists_unique_nlhfRegularizedClosedSaddlePair_profile
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedClosedSaddle τ (normalizedStrictMargin R) ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedClosedSaddlePair hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- The selected NLHF rule is a fixed point on every finite profile's
normalized strict margin. -/
theorem selectedNLHF_profile_fixedPoint
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ
      (selectedNLHF (α := α) τ (normalizedStrictMargin R) ρ) :=
  selectedNLHF_selection hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- The selected NLHF rule equals any profile-level fixed point. -/
theorem selectedNLHF_profile_eq_of_fixedPoint
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {τ : ℝ} {R : V → α → α → Bool} {ρ π : α → ℝ}
    (hπ : IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ π) :
    selectedNLHF (α := α) τ (normalizedStrictMargin R) ρ = π :=
  selectedNLHF_eq_of_fixedPoint
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hπ

/-- Profile-level NLHF existence and uniqueness from the closed-Sion saddle
existence interface. -/
theorem exists_unique_nlhfFixedPoint_profile_of_closedSion
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! π : α → ℝ,
      IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ π :=
  exists_unique_nlhfFixedPoint_of_closedSion hsion hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- Profile-level regularized saddle-pair existence and uniqueness from the
closed-Sion saddle existence interface. -/
theorem exists_unique_nlhfRegularizedSaddlePair_profile_of_closedSion
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedSaddle τ (normalizedStrictMargin R) ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedSaddlePair_of_closedSion hsion hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- Profile-level closed-simplex saddle-pair existence and uniqueness from the
closed-Sion saddle existence interface. -/
theorem exists_unique_nlhfRegularizedClosedSaddlePair_profile_of_closedSion
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    ∃! pq : (α → ℝ) × (α → ℝ),
      IsNLHFRegularizedClosedSaddle τ (normalizedStrictMargin R) ρ pq.1 pq.2 :=
  exists_unique_nlhfRegularizedClosedSaddlePair_of_closedSion hsion hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- The selected closed-Sion NLHF rule is a fixed point on every finite
profile's normalized strict margin. -/
theorem selectedNLHFOfClosedSion_profile_fixedPoint
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} (hτ : 0 < τ)
    (R : V → α → α → Bool)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ
      (selectedNLHFOfClosedSion hsion τ (normalizedStrictMargin R) ρ) :=
  selectedNLHFOfClosedSion_selection hsion hτ
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hρ

/-- The selected closed-Sion NLHF rule equals any profile-level fixed point. -/
theorem selectedNLHFOfClosedSion_profile_eq_of_fixedPoint
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} {R : V → α → α → Bool} {ρ π : α → ℝ}
    (hπ : IsNLHFFixedPoint τ (normalizedStrictMargin R) ρ π) :
    selectedNLHFOfClosedSion hsion τ (normalizedStrictMargin R) ρ = π :=
  selectedNLHFOfClosedSion_eq_of_fixedPoint hsion
    (normalizedStrictMargin_isNormalizedMarginMatrix R) hπ

/-- Profile-level large-temperature monotonicity for the selected NLHF rule
obtained from the strict-KL fixed-point existence interface. -/
theorem selectedNLHFOfSionStrictKL_largeTau_profileProbabilisticMonotonicity
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} (hτ : (3 : ℝ) / 8 ≤ τ) :
    SatisfiesProfileProbabilisticMonotonicity (V := V)
      ((selectedNLHFOfSionStrictKL hexists) τ) :=
  profileProbabilisticMonotonicity_of_matrix
    ((nlhf_largeTau_monotone_from_fixedPointSelection
      (selectedNLHFOfSionStrictKL_selection hexists)) τ hτ)

/-- Pointwise profile-improvement form for the strict-KL selected NLHF rule. -/
theorem selectedNLHFOfSionStrictKL_profile_largeTau_monotone
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ : ℝ} (hτ : (3 : ℝ) / 8 ≤ τ)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (hprof : IsProfileImprovement R R' x) :
    selectedNLHFOfSionStrictKL hexists τ (normalizedStrictMargin R) ρ x ≤
      selectedNLHFOfSionStrictKL hexists τ
        (normalizedStrictMargin R') ρ x :=
  selectedNLHFOfSionStrictKL_largeTau_profileProbabilisticMonotonicity
    (V := V) hexists hτ R R' ρ x hρ hprof

/-- Profile-level large-temperature monotonicity for the selected NLHF rule
obtained from the proved Sion specialization. -/
theorem selectedNLHF_largeTau_profileProbabilisticMonotonicity
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {τ : ℝ} (hτ : (3 : ℝ) / 8 ≤ τ) :
    SatisfiesProfileProbabilisticMonotonicity (V := V)
      ((selectedNLHF (α := α)) τ) :=
  profileProbabilisticMonotonicity_of_matrix
    ((selectedNLHF_largeTau_monotone (α := α)) τ hτ)

/-- Pointwise profile-improvement form for the selected NLHF rule with the
proved Sion specialization. -/
theorem selectedNLHF_profile_largeTau_monotone
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {τ : ℝ} (hτ : (3 : ℝ) / 8 ≤ τ)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (hprof : IsProfileImprovement R R' x) :
    selectedNLHF (α := α) τ (normalizedStrictMargin R) ρ x ≤
      selectedNLHF (α := α) τ (normalizedStrictMargin R') ρ x :=
  selectedNLHF_largeTau_profileProbabilisticMonotonicity
    (V := V) hτ R R' ρ x hρ hprof

/-- Profile-level large-temperature monotonicity for the selected closed-Sion
NLHF rule, obtained by combining the selected matrix-level NLHF theorem with
the normalized strict-margin profile bridge. -/
theorem selectedNLHFOfClosedSion_largeTau_profileProbabilisticMonotonicity
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} (hτ : (3 : ℝ) / 8 ≤ τ) :
    SatisfiesProfileProbabilisticMonotonicity (V := V)
      ((selectedNLHFOfClosedSion hsion) τ) :=
  profileProbabilisticMonotonicity_of_matrix
    ((selectedNLHFOfClosedSion_largeTau_monotone hsion) τ hτ)

/-- Pointwise profile-improvement form of the large-temperature monotonicity
theorem for the selected closed-Sion NLHF rule. -/
theorem selectedNLHFOfClosedSion_profile_largeTau_monotone
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ : ℝ} (hτ : (3 : ℝ) / 8 ≤ τ)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (hprof : IsProfileImprovement R R' x) :
    selectedNLHFOfClosedSion hsion τ (normalizedStrictMargin R) ρ x ≤
      selectedNLHFOfClosedSion hsion τ (normalizedStrictMargin R') ρ x :=
  selectedNLHFOfClosedSion_largeTau_profileProbabilisticMonotonicity
    (V := V) hsion hτ R R' ρ x hρ hprof

end PaperFormalization
