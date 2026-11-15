import PaperFormalization.ProfileFord
import PaperFormalization.RTBT

open scoped BigOperators

namespace PaperFormalization

variable {α V : Type*}

/-- Profile-level RTBT monotonicity for a strength selector equipped with a
ratio-monotonicity certificate. -/
theorem RTBTPM_profile_from_BT_ratio_certificate
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTRatioMonotonicityForImprovements BT) :
    SatisfiesProfileProbabilisticMonotonicity (V := V)
      (fun M ρ => RTBTFromStrength β ρ (BT M)) :=
  profileProbabilisticMonotonicity_of_matrix
    (RTBTPM_from_BT_ratio_certificate hβ hBT)

/-- Pointwise finite-profile form: after interpreting profiles as normalized
strict-margin matrices, improving `x` cannot decrease its RTBT probability for
a strength selector equipped with a ratio-monotonicity certificate. -/
theorem RTBTPM_profile_pointwise_from_BT_ratio_certificate
    [Fintype α] [DecidableEq α] [Fintype V] [Nonempty V]
    {β : ℝ} (hβ : 0 < β)
    {BT : (α → α → ℝ) → α → ℝ}
    (hBT : HasBTRatioMonotonicityForImprovements BT)
    {R R' : V → α → α → Bool} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (hprof : IsProfileImprovement R R' x) :
    RTBTFromStrength β ρ (BT (normalizedStrictMargin R)) x ≤
      RTBTFromStrength β ρ (BT (normalizedStrictMargin R')) x :=
  RTBTPM_profile_from_BT_ratio_certificate (V := V) hβ hBT
    R R' ρ x hρ hprof

/-- Proposition `RTBTorder`, profile-count selected-BT form: the RTBT update
using the normalized Bradley-Terry vector selected from Ford/Zermelo commutes
for any two finite profiles satisfying Ford's side conditions. -/
theorem RTBTorder_strictCountProfile_selectedBTOfFordZermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R S : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hS : IsIrreflexiveProfile S)
    (hconnR : FordStronglyConnected (strictCount R))
    (hconnS : FordStronglyConnected (strictCount S))
    (hρ : IsFullSupportLottery ρ) :
    RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedBTOfFordZermelo hFord (strictCount R)
            (strictCount_isFordCountMatrix hR) hconnR))
        (selectedBTOfFordZermelo hFord (strictCount S)
          (strictCount_isFordCountMatrix hS) hconnS) =
      RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedBTOfFordZermelo hFord (strictCount S)
            (strictCount_isFordCountMatrix hS) hconnS))
        (selectedBTOfFordZermelo hFord (strictCount R)
          (strictCount_isFordCountMatrix hR) hconnR) :=
  RTBTFromStrength_commutative hβ hρ.1
    (selectedBTOfFordZermelo_pos hFord
      (strictCount_isFordCountMatrix hR) hconnR)
    (selectedBTOfFordZermelo_pos hFord
      (strictCount_isFordCountMatrix hS) hconnS)

/-- Proposition `RTBTorder`, profile-count selected-Ford-BT form using the
normalized maximum-likelihood representative supplied directly by Ford/Zermelo. -/
theorem RTBTorder_strictCountProfile_selectedFordBTOfFordZermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {R S : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hS : IsIrreflexiveProfile S)
    (hconnR : FordStronglyConnected (strictCount R))
    (hconnS : FordStronglyConnected (strictCount S))
    (hρ : IsFullSupportLottery ρ) :
    RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedFordBTOfFordZermelo hFord (strictCount R)
            (strictCount_isFordCountMatrix hR) hconnR))
        (selectedFordBTOfFordZermelo hFord (strictCount S)
          (strictCount_isFordCountMatrix hS) hconnS) =
      RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedFordBTOfFordZermelo hFord (strictCount S)
            (strictCount_isFordCountMatrix hS) hconnS))
        (selectedFordBTOfFordZermelo hFord (strictCount R)
          (strictCount_isFordCountMatrix hR) hconnR) :=
  RTBTFromStrength_commutative hβ hρ.1
    (selectedFordBTOfFordZermelo_isBTStrength hFord
      (strictCount_isFordCountMatrix hR) hconnR).1.1
    (selectedFordBTOfFordZermelo_isBTStrength hFord
      (strictCount_isFordCountMatrix hS) hconnS).1.1

/-- The Ford/Zermelo-selected RTBT profile rule preserves full support. -/
theorem RTBTFrom_selectedBTOfFordZermelo_strictCountProfile_fullSupport
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} {R : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : IsFullSupportLottery ρ) :
    IsFullSupportLottery
      (RTBTFromStrength β ρ
        (selectedBTOfFordZermelo hFord (strictCount R)
          (strictCount_isFordCountMatrix hR) hconn)) :=
  RTBTFromStrength_fullSupport β hρ.1
    (selectedBTOfFordZermelo_pos hFord
      (strictCount_isFordCountMatrix hR) hconn)

/-- The Ford/Zermelo normalized-maximum-likelihood selected RTBT profile rule
preserves full support. -/
theorem RTBTFrom_selectedFordBTOfFordZermelo_strictCountProfile_fullSupport
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} {R : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hconn : FordStronglyConnected (strictCount R))
    (hρ : IsFullSupportLottery ρ) :
    IsFullSupportLottery
      (RTBTFromStrength β ρ
        (selectedFordBTOfFordZermelo hFord (strictCount R)
          (strictCount_isFordCountMatrix hR) hconn)) :=
  RTBTFromStrength_fullSupport β hρ.1
    (selectedFordBTOfFordZermelo_isBTStrength hFord
      (strictCount_isFordCountMatrix hR) hconn).1.1

/-- Proposition `RTBTorder`, finite-profile conjunction for proportional Borda
and the normalized Bradley-Terry selector obtained from Ford/Zermelo. -/
theorem RTBTorder_profile_selectedBTOfFordZermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {η β : ℝ} (hβ : 0 < β)
    {R S : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hS : IsIrreflexiveProfile S)
    (hconnR : FordStronglyConnected (strictCount R))
    (hconnS : FordStronglyConnected (strictCount S))
    (hρ : IsFullSupportLottery ρ) :
    proportionalBorda η
        (proportionalBorda η ρ (strictDominationBordaScore R))
        (strictDominationBordaScore S) =
      proportionalBorda η
        (proportionalBorda η ρ (strictDominationBordaScore S))
        (strictDominationBordaScore R) ∧
    RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedBTOfFordZermelo hFord (strictCount R)
            (strictCount_isFordCountMatrix hR) hconnR))
        (selectedBTOfFordZermelo hFord (strictCount S)
          (strictCount_isFordCountMatrix hS) hconnS) =
      RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedBTOfFordZermelo hFord (strictCount S)
            (strictCount_isFordCountMatrix hS) hconnS))
        (selectedBTOfFordZermelo hFord (strictCount R)
          (strictCount_isFordCountMatrix hR) hconnR) :=
  ⟨proportionalBordaProfile_commutative R S hρ,
    RTBTorder_strictCountProfile_selectedBTOfFordZermelo hFord hβ
      hR hS hconnR hconnS hρ⟩

/-- Proposition `RTBTorder`, finite-profile conjunction for proportional Borda
and the normalized maximum-likelihood representative supplied directly by
Ford/Zermelo. -/
theorem RTBTorder_profile_selectedFordBTOfFordZermelo
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype V]
    (hFord : FordZermeloBTTheorem α)
    {η β : ℝ} (hβ : 0 < β)
    {R S : V → α → α → Bool} {ρ : α → ℝ}
    (hR : IsIrreflexiveProfile R)
    (hS : IsIrreflexiveProfile S)
    (hconnR : FordStronglyConnected (strictCount R))
    (hconnS : FordStronglyConnected (strictCount S))
    (hρ : IsFullSupportLottery ρ) :
    proportionalBorda η
        (proportionalBorda η ρ (strictDominationBordaScore R))
        (strictDominationBordaScore S) =
      proportionalBorda η
        (proportionalBorda η ρ (strictDominationBordaScore S))
        (strictDominationBordaScore R) ∧
    RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedFordBTOfFordZermelo hFord (strictCount R)
            (strictCount_isFordCountMatrix hR) hconnR))
        (selectedFordBTOfFordZermelo hFord (strictCount S)
          (strictCount_isFordCountMatrix hS) hconnS) =
      RTBTFromStrength β
        (RTBTFromStrength β ρ
          (selectedFordBTOfFordZermelo hFord (strictCount S)
            (strictCount_isFordCountMatrix hS) hconnS))
        (selectedFordBTOfFordZermelo hFord (strictCount R)
          (strictCount_isFordCountMatrix hR) hconnR) :=
  ⟨proportionalBordaProfile_commutative R S hρ,
    RTBTorder_strictCountProfile_selectedFordBTOfFordZermelo hFord hβ
      hR hS hconnR hconnS hρ⟩

end PaperFormalization
