import PaperFormalization.NLHFExistence
import PaperFormalization.NLHFMonotonicityFinite

open scoped BigOperators

namespace PaperFormalization

/-- The right-to-left direction of Theorem `NLHFmono` for the selected NLHF
rule obtained from the strict-KL fixed-point existence interface. -/
theorem selectedNLHFOfSionStrictKL_largeTau_monotone
    {α : Type*} [Fintype α] [DecidableEq α]
    (hexists : SionStrictKLFixedPointExistence (α := α)) :
    NLHFMonotoneForLargeTau (selectedNLHFOfSionStrictKL hexists) :=
  nlhf_largeTau_monotone_from_fixedPointSelection
    (selectedNLHFOfSionStrictKL_selection hexists)

/-- The right-to-left direction of Theorem `NLHFmono` for the selected NLHF
rule obtained from the proved Sion specialization. -/
theorem selectedNLHF_largeTau_monotone
    {α : Type*} [Fintype α] [DecidableEq α] :
    NLHFMonotoneForLargeTau (selectedNLHF (α := α)) :=
  nlhf_largeTau_monotone_from_fixedPointSelection
    (selectedNLHF_selection (α := α))

/-- The right-to-left direction of Theorem `NLHFmono` for the selected NLHF
rule obtained from the closed-simplex Sion saddle-existence theorem.  At this
point the proof no longer needs a separate variational-characterization input:
the needed endpoint optimality is derived from the selected fixed-point
equation. -/
theorem selectedNLHFOfClosedSion_largeTau_monotone
    {α : Type*} [Fintype α] [DecidableEq α]
    (hsion : SionClosedSaddleExistence (α := α)) :
    NLHFMonotoneForLargeTau (selectedNLHFOfClosedSion hsion) :=
  nlhf_largeTau_monotone_from_fixedPointSelection
    (selectedNLHFOfClosedSion_selection hsion)

/-- The finite-secant low-temperature counterexample for the strict-KL
selected NLHF rule on three alternatives. -/
theorem selectedNLHFOfSionStrictKL_lowTempSecantDropCertificate_fin3
    (hexists : SionStrictKLFixedPointExistence (α := Fin 3)) :
    HasNLHFLowTempSecantDropCertificate
      (selectedNLHFOfSionStrictKL hexists) :=
  nlhfSharpAll_lowTempSecantDropCertificate_fin3
    (selectedNLHFOfSionStrictKL hexists)
    (selectedNLHFOfSionStrictKL_selection hexists)
    (selectedNLHFOfSionStrictKL_isTheNLHF hexists)

/-- The finite-secant low-temperature counterexample for the selected NLHF
rule obtained from the proved Sion specialization. -/
theorem selectedNLHF_lowTempSecantDropCertificate_fin3 :
    HasNLHFLowTempSecantDropCertificate (selectedNLHF (α := Fin 3)) :=
  nlhfSharpAll_lowTempSecantDropCertificate_fin3
    (selectedNLHF (α := Fin 3))
    (selectedNLHF_selection (α := Fin 3))
    (selectedNLHF_isTheNLHF (α := Fin 3))

/-- The finite-secant low-temperature counterexample for the selected
closed-Sion NLHF rule on three alternatives.  This discharges the
low-temperature side of Theorem `NLHFmono` for the concrete three-candidate
counterexample domain. -/
theorem selectedNLHFOfClosedSion_lowTempSecantDropCertificate_fin3
    (hsion : SionClosedSaddleExistence (α := Fin 3)) :
    HasNLHFLowTempSecantDropCertificate (selectedNLHFOfClosedSion hsion) :=
  nlhfSharpAll_lowTempSecantDropCertificate_fin3
    (selectedNLHFOfClosedSion hsion)
    (selectedNLHFOfClosedSion_selection hsion)
    (selectedNLHFOfClosedSion_isTheNLHF hsion)

/-- Three-candidate `3/8` threshold theorem for the strict-KL selected NLHF
rule, proved from the selected fixed-point interface and the concrete
low-temperature certificate. -/
theorem NLHFmono_fin3_from_sionStrictKL
    (hexists : SionStrictKLFixedPointExistence (α := Fin 3))
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity
        ((selectedNLHFOfSionStrictKL hexists) τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_fixedPointSelection_and_lowTemp_certificate
    (selectedNLHFOfSionStrictKL hexists)
    (selectedNLHFOfSionStrictKL_selection hexists)
    (selectedNLHFOfSionStrictKL_lowTempSecantDropCertificate_fin3 hexists)
    hτ

/-- Three-candidate `3/8` threshold theorem for the selected NLHF rule
obtained from the proved Sion specialization. -/
theorem NLHFmono_fin3
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity
        ((selectedNLHF (α := Fin 3)) τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_fixedPointSelection_and_lowTemp_certificate
    (selectedNLHF (α := Fin 3))
    (selectedNLHF_selection (α := Fin 3))
    selectedNLHF_lowTempSecantDropCertificate_fin3
    hτ

/-- Stable alias for the selected NLHF three-candidate `3/8` threshold used in
the all-profiles converse. -/
theorem selectedNLHF_fin3_allProfileThreshold
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity
        ((selectedNLHF (α := Fin 3)) τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_fin3 hτ

/-- Three-candidate `3/8` threshold theorem for the selected closed-Sion NLHF
rule, with both the large-temperature finite comparison and the
low-temperature finite-secant counterexample proved in Lean from the selected
fixed-point interface. -/
theorem NLHFmono_fin3_from_closedSion
    (hsion : SionClosedSaddleExistence (α := Fin 3))
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity
        ((selectedNLHFOfClosedSion hsion) τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_fixedPointSelection_and_lowTemp_certificate
    (selectedNLHFOfClosedSion hsion)
    (selectedNLHFOfClosedSion_selection hsion)
    (selectedNLHFOfClosedSion_lowTempSecantDropCertificate_fin3 hsion)
    hτ

/-- The strict-KL selected NLHF rule satisfies the positive `1/8` bridge for
weighted weak-order profiles. -/
theorem selectedNLHFOfSionStrictKL_weightedScoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {w : V → ℝ} {score : V → α → ℝ}
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hw_nonneg : ∀ v : V, 0 ≤ w v)
    (hw_sum : Finset.univ.sum (fun v : V => w v) = 1)
    (hchange : ∀ a b : α,
      weightedScoreProfileMargin w score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHFOfSionStrictKL hexists τ M ρ x ≤
      selectedNLHFOfSionStrictKL hexists τ
        (weightedScoreProfileMargin w score) ρ x :=
  nlhf_weightedScoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    (hselect := selectedNLHFOfSionStrictKL_selection hexists)
    (hselected :=
      selectedVariationalInequality_of_fixedPointSelection
        (selectedNLHFOfSionStrictKL_selection hexists))
    (hτge := hτge) (hM := hM) (hρ := hρ)
    (hw_nonneg := hw_nonneg) (hw_sum := hw_sum)
    (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- The selected NLHF rule satisfies the positive `1/8` bridge for weighted
weak-order profiles, using the proved Sion specialization. -/
theorem selectedNLHF_weightedScoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {w : V → ℝ} {score : V → α → ℝ}
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hw_nonneg : ∀ v : V, 0 ≤ w v)
    (hw_sum : Finset.univ.sum (fun v : V => w v) = 1)
    (hchange : ∀ a b : α,
      weightedScoreProfileMargin w score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHF (α := α) τ M ρ x ≤
      selectedNLHF (α := α) τ
        (weightedScoreProfileMargin w score) ρ x := by
  simpa [selectedNLHF] using
    selectedNLHFOfSionStrictKL_weightedScoreProfile_block_monotone_one_eighth
      (V := V) (α := α)
      (fixedPointExistence_of_closedSion sionClosedSaddleExistence)
      (hτge := hτge) (hM := hM) (hρ := hρ)
      (hw_nonneg := hw_nonneg) (hw_sum := hw_sum)
      (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- The selected closed-Sion NLHF rule satisfies the positive `1/8` bridge for
weighted weak-order profiles.  This is the formal right-to-left half of the
weak-order/linear-order part of Theorem `NLHFmono`, stated at the margin level
used in the appendix. -/
theorem selectedNLHFOfClosedSion_weightedScoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {w : V → ℝ} {score : V → α → ℝ}
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hw_nonneg : ∀ v : V, 0 ≤ w v)
    (hw_sum : Finset.univ.sum (fun v : V => w v) = 1)
    (hchange : ∀ a b : α,
      weightedScoreProfileMargin w score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHFOfClosedSion hsion τ M ρ x ≤
      selectedNLHFOfClosedSion hsion τ
        (weightedScoreProfileMargin w score) ρ x :=
  nlhf_weightedScoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    (hselect := selectedNLHFOfClosedSion_selection hsion)
    (hselected :=
      selectedVariationalInequality_of_fixedPointSelection
        (selectedNLHFOfClosedSion_selection hsion))
    (hτge := hτge) (hM := hM) (hρ := hρ)
    (hw_nonneg := hw_nonneg) (hw_sum := hw_sum)
    (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- The strict-KL selected NLHF rule satisfies the positive `1/8` bridge for
actual finite weak-order profiles represented by score functions. -/
theorem selectedNLHFOfSionStrictKL_scoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHFOfSionStrictKL hexists τ M ρ x ≤
      selectedNLHFOfSionStrictKL hexists τ (scoreProfileMargin score) ρ x :=
  nlhf_scoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    (hselect := selectedNLHFOfSionStrictKL_selection hexists)
    (hselected :=
      selectedVariationalInequality_of_fixedPointSelection
        (selectedNLHFOfSionStrictKL_selection hexists))
    (hτge := hτge) (hM := hM) (hρ := hρ)
    (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- The selected NLHF rule satisfies the positive `1/8` bridge for actual
finite weak-order profiles represented by score functions. -/
theorem selectedNLHF_scoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHF (α := α) τ M ρ x ≤
      selectedNLHF (α := α) τ (scoreProfileMargin score) ρ x := by
  simpa [selectedNLHF] using
    selectedNLHFOfSionStrictKL_scoreProfile_block_monotone_one_eighth
      (V := V) (α := α)
      (fixedPointExistence_of_closedSion sionClosedSaddleExistence)
      (hτge := hτge) (hM := hM) (hρ := hρ)
      (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- The selected closed-Sion NLHF rule satisfies the positive `1/8` bridge for
actual finite weak-order profiles represented by score functions. -/
theorem selectedNLHFOfClosedSion_scoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHFOfClosedSion hsion τ M ρ x ≤
      selectedNLHFOfClosedSion hsion τ (scoreProfileMargin score) ρ x :=
  nlhf_scoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    (hselect := selectedNLHFOfClosedSion_selection hsion)
    (hselected :=
      selectedVariationalInequality_of_fixedPointSelection
        (selectedNLHFOfClosedSion_selection hsion))
    (hτge := hτge) (hM := hM) (hρ := hρ)
    (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- Linear-order specialization of the strict-KL selected `1/8` bridge. -/
theorem selectedNLHFOfSionStrictKL_linearScoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (hlinear : IsLinearScoreProfile score)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHFOfSionStrictKL hexists τ M ρ x ≤
      selectedNLHFOfSionStrictKL hexists τ (scoreProfileMargin score) ρ x :=
  nlhf_linearScoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    (_hlinear := hlinear)
    (hselect := selectedNLHFOfSionStrictKL_selection hexists)
    (hselected :=
      selectedVariationalInequality_of_fixedPointSelection
        (selectedNLHFOfSionStrictKL_selection hexists))
    (hτge := hτge) (hM := hM) (hρ := hρ)
    (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- Linear-order specialization of the selected NLHF `1/8` bridge, using the
proved Sion specialization. -/
theorem selectedNLHF_linearScoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (hlinear : IsLinearScoreProfile score)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHF (α := α) τ M ρ x ≤
      selectedNLHF (α := α) τ (scoreProfileMargin score) ρ x := by
  simpa [selectedNLHF] using
    selectedNLHFOfSionStrictKL_linearScoreProfile_block_monotone_one_eighth
      (V := V) (α := α)
      (fixedPointExistence_of_closedSion sionClosedSaddleExistence)
      (hlinear := hlinear) (hτge := hτge) (hM := hM) (hρ := hρ)
      (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- Linear-order specialization of the selected closed-Sion `1/8` bridge. -/
theorem selectedNLHFOfClosedSion_linearScoreProfile_block_monotone_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α]
    (hsion : SionClosedSaddleExistence (α := α))
    {τ δ : ℝ}
    {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
    {B : Finset {z : α // z ≠ x}}
    {score : V → α → ℝ}
    (hlinear : IsLinearScoreProfile score)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    (hchange : ∀ a b : α,
      scoreProfileMargin score a b - M a b =
        blockImprovementChange x
          (B.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
          δ a b)
    (hBne : B.Nonempty)
    (hδpos : 0 < δ) :
    selectedNLHFOfClosedSion hsion τ M ρ x ≤
      selectedNLHFOfClosedSion hsion τ (scoreProfileMargin score) ρ x :=
  nlhf_linearScoreProfile_block_improvement_monotone_of_tau_ge_one_eighth_selected
    (_hlinear := hlinear)
    (hselect := selectedNLHFOfClosedSion_selection hsion)
    (hselected :=
      selectedVariationalInequality_of_fixedPointSelection
        (selectedNLHFOfClosedSion_selection hsion))
    (hτge := hτge) (hM := hM) (hρ := hρ)
    (hchange := hchange) (hBne := hBne) (hδpos := hδpos)

/-- The strict-KL selected NLHF rule has the linear-order `1/8`
low-temperature counterexample, in the weighted finite-profile form used in
the appendix. -/
theorem selectedNLHFOfSionStrictKL_linear_lowTempWeightedProfileDrop_fin3
    (hexists : SionStrictKLFixedPointExistence (α := Fin 3)) :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ b η δ : ℝ,
        0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
        0 < δ ∧ δ ≤ η ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfSharpSymLottery3 b)) ∧
        selectedNLHFOfSionStrictKL hexists τ
            (weightedScoreProfileMargin
              (nlhfSharpLinearWeights3Improved η δ)
              nlhfSharpLinearScore3)
            (nlhfBacksolvedReference τ
              (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
                nlhfSharpLinearScore3)
              (nlhfSharpSymLottery3 b)) 0 <
          selectedNLHFOfSionStrictKL hexists τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfBacksolvedReference τ
              (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
                nlhfSharpLinearScore3)
              (nlhfSharpSymLottery3 b)) 0 :=
  nlhfSharpLinear_lowTempWeightedProfileDrop_fin3
    (selectedNLHFOfSionStrictKL hexists)
    (selectedNLHFOfSionStrictKL_selection hexists)
    (selectedNLHFOfSionStrictKL_isTheNLHF hexists)

/-- The selected NLHF rule has the linear-order `1/8` low-temperature
counterexample, in the weighted finite-profile form used in the appendix. -/
theorem selectedNLHF_linear_lowTempWeightedProfileDrop_fin3 :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ b η δ : ℝ,
        0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
        0 < δ ∧ δ ≤ η ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfSharpSymLottery3 b)) ∧
        selectedNLHF (α := Fin 3) τ
            (weightedScoreProfileMargin
              (nlhfSharpLinearWeights3Improved η δ)
              nlhfSharpLinearScore3)
            (nlhfBacksolvedReference τ
              (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
                nlhfSharpLinearScore3)
              (nlhfSharpSymLottery3 b)) 0 <
          selectedNLHF (α := Fin 3) τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfBacksolvedReference τ
              (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
                nlhfSharpLinearScore3)
              (nlhfSharpSymLottery3 b)) 0 :=
  nlhfSharpLinear_lowTempWeightedProfileDrop_fin3
    (selectedNLHF (α := Fin 3))
    (selectedNLHF_selection (α := Fin 3))
    (selectedNLHF_isTheNLHF (α := Fin 3))

/-- The selected NLHF rule has the linear-order `1/8` low-temperature
counterexample in denominator-cleared finite-profile form: both old and new
margins are induced by actual finite profiles of linear orders. -/
theorem selectedNLHF_linear_lowTempFiniteProfileDrop_fin3 :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ N m : ℕ, ∃ b : ℝ,
        0 < N ∧ 0 < b ∧ b < 1 ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) ∧
        IsLinearScoreProfile (nlhfSharpLinearReplicatedOldScore3 N m) ∧
        IsLinearScoreProfile (nlhfSharpLinearReplicatedMovedScore3 N m) ∧
        IsImprovementOf
          (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
          (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
          0 ∧
        selectedNLHF (α := Fin 3) τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
            (nlhfBacksolvedReference τ
              (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
              (nlhfSharpSymLottery3 b)) 0 <
          selectedNLHF (α := Fin 3) τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfBacksolvedReference τ
              (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
              (nlhfSharpSymLottery3 b)) 0 :=
  nlhfSharpLinear_lowTempFiniteProfileDrop_fin3
    (selectedNLHF (α := Fin 3))
    (selectedNLHF_selection (α := Fin 3))
    (selectedNLHF_isTheNLHF (α := Fin 3))

/-- The selected NLHF linear-order counterexample with the exact singleton
block-change equation required by
`SelectedNLHFLinearOrderProfileMonotonicity`.  This is the paper-facing
finite-profile converse witness: the old and new margins come from actual
finite profiles of linear orders, and the change is exactly the improvement of
candidate `0` against the singleton block `{1}`. -/
theorem selectedNLHF_linear_lowTempFiniteProfileBlockDrop_fin3 :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ N m : ℕ, ∃ b δ : ℝ,
      ∃ B : Finset {z : Fin 3 // z ≠ 0},
        0 < N ∧ 0 < b ∧ b < 1 ∧ 0 < δ ∧ B.Nonempty ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) ∧
        IsLinearScoreProfile (nlhfSharpLinearReplicatedOldScore3 N m) ∧
        IsLinearScoreProfile (nlhfSharpLinearReplicatedMovedScore3 N m) ∧
        IsImprovementOf
          (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
          (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
          0 ∧
        (∀ a b' : Fin 3,
          scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m) a b' -
              scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m) a b' =
            blockImprovementChange 0
              (B.map (Function.Embedding.subtype
                (fun z : Fin 3 => z ≠ 0))) δ a b') ∧
        selectedNLHF (α := Fin 3) τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
            (nlhfBacksolvedReference τ
              (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
              (nlhfSharpSymLottery3 b)) 0 <
          selectedNLHF (α := Fin 3) τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfBacksolvedReference τ
              (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
              (nlhfSharpSymLottery3 b)) 0 := by
  intro τ hτ hτlt
  rcases selectedNLHF_linear_lowTempFiniteProfileDrop_fin3 τ hτ hτlt with
    ⟨N, m, b, hN, hb0, hb1, hρ, holdLinear, hnewLinear,
      himprove, hdrop⟩
  let δ : ℝ := 2 / ((N : ℝ) * ((m : ℝ) + 1))
  let B : Finset {z : Fin 3 // z ≠ 0} := {⟨1, by decide⟩}
  have hNreal : (0 : ℝ) < (N : ℕ) := by exact_mod_cast hN
  have hmreal : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hNreal hmreal)
  have hold :
      scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m) =
        nlhfSharpLinearMargin3 (2 / (N : ℝ)) :=
    nlhfSharpLinearMargin3_eq_replicatedOldScoreProfile N m hN
  have hnew :
      scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m) =
        improvePairMargin (nlhfSharpLinearMargin3 (2 / (N : ℝ))) 0 1 δ := by
    dsimp [δ]
    exact nlhfSharpLinearImproved_eq_replicatedMovedScoreProfile N m hN
  have hchange : ∀ a b' : Fin 3,
      scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m) a b' -
          scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m) a b' =
        blockImprovementChange 0
          (B.map (Function.Embedding.subtype
            (fun z : Fin 3 => z ≠ 0))) δ a b' := by
    intro a b'
    rw [hnew, hold]
    simpa [B] using
      improvePairMargin_change_eq_blockImprovementChange_singleton
        (nlhfSharpLinearMargin3 (2 / (N : ℝ))) δ
        (by decide : (1 : Fin 3) ≠ 0) a b'
  have hBne : B.Nonempty :=
    ⟨⟨1, by decide⟩, by simp [B]⟩
  exact ⟨N, m, b, δ, B, hN, hb0, hb1, hδpos, hBne, hρ,
    holdLinear, hnewLinear, himprove, hchange, hdrop⟩

/-- The selected closed-Sion NLHF rule has the linear-order `1/8`
low-temperature counterexample, in the weighted finite-profile form used in
the appendix. -/
theorem selectedNLHFOfClosedSion_linear_lowTempWeightedProfileDrop_fin3
    (hsion : SionClosedSaddleExistence (α := Fin 3)) :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ b η δ : ℝ,
        0 < b ∧ b < 1 ∧ 0 < η ∧ η < 1 ∧
        0 < δ ∧ δ ≤ η ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfSharpSymLottery3 b)) ∧
        selectedNLHFOfClosedSion hsion τ
            (weightedScoreProfileMargin
              (nlhfSharpLinearWeights3Improved η δ)
              nlhfSharpLinearScore3)
            (nlhfBacksolvedReference τ
              (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
                nlhfSharpLinearScore3)
              (nlhfSharpSymLottery3 b)) 0 <
          selectedNLHFOfClosedSion hsion τ
            (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
              nlhfSharpLinearScore3)
            (nlhfBacksolvedReference τ
              (weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
                nlhfSharpLinearScore3)
              (nlhfSharpSymLottery3 b)) 0 :=
  nlhfSharpLinear_lowTempWeightedProfileDrop_fin3
    (selectedNLHFOfClosedSion hsion)
    (selectedNLHFOfClosedSion_selection hsion)
    (selectedNLHFOfClosedSion_isTheNLHF hsion)

/-- `3/8` threshold theorem for the strict-KL selected NLHF rule, parameterized
by the concrete low-temperature strict-drop construction. -/
theorem NLHFmono_from_sionStrictKL_and_lowTemp_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (hexists : SionStrictKLFixedPointExistence (α := α))
    (hlow :
      HasNLHFLowTempSecantDropCertificate
        (selectedNLHFOfSionStrictKL hexists))
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity
        ((selectedNLHFOfSionStrictKL hexists) τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_fixedPointSelection_and_lowTemp_certificate
    (selectedNLHFOfSionStrictKL hexists)
    (selectedNLHFOfSionStrictKL_selection hexists)
    hlow hτ

/-- `3/8` threshold theorem for the selected NLHF rule obtained from the
proved Sion specialization, with the low-temperature strict-drop construction
supplied as an explicit input. -/
theorem NLHFmono_from_lowTemp_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (hlow : HasNLHFLowTempSecantDropCertificate (selectedNLHF (α := α)))
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity
        ((selectedNLHF (α := α)) τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_fixedPointSelection_and_lowTemp_certificate
    (selectedNLHF (α := α))
    (selectedNLHF_selection (α := α))
    hlow hτ

/-- `3/8` threshold theorem for the selected NLHF rule, parameterized by the
closed-Sion existence theorem and the concrete small-`τ` counterexample
certificate. -/
theorem NLHFmono_from_closedSion_and_lowTemp_certificate
    {α : Type*} [Fintype α] [DecidableEq α]
    (hsion : SionClosedSaddleExistence (α := α))
    (hlow :
      HasNLHFLowTempSecantDropCertificate (selectedNLHFOfClosedSion hsion))
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity
        ((selectedNLHFOfClosedSion hsion) τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_fixedPointSelection_and_lowTemp_certificate
    (selectedNLHFOfClosedSion hsion)
    (selectedNLHFOfClosedSion_selection hsion)
    hlow hτ

/-- Paper-facing formalization of the phrase in Theorem `NLHFmono`:
`NLHF_tau` satisfies probabilistic monotonicity over all finite profiles.  At
the matrix level, "all profiles" is represented by all finite normalized
margin matrices. -/
def SelectedNLHFAllProfileMonotonicity (τ : ℝ) : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α],
    SatisfiesProbabilisticMonotonicity ((selectedNLHF (α := α)) τ)

/-!
### Auxiliary weighted profile clauses

The following weighted score-profile statements are proof infrastructure for
the appendix route and trace the rational-weighted counterexample.  The
bundled theorem `PaperStatements.NLHFmono` uses the actual finite-profile
clauses below.
-/

/-- Auxiliary weighted weak-order profile monotonicity.  Weak orders are
represented by real-valued score functions; ties in a score function encode
indifference. -/
def SelectedNLHFWeightedWeakOrderProfileMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Fintype α] [DecidableEq α],
    ∀ {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
      {B : Finset {z : α // z ≠ x}} {δ : ℝ}
      {w : V → ℝ} {score : V → α → ℝ},
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ →
          (∀ v : V, 0 ≤ w v) →
            Finset.univ.sum (fun v : V => w v) = 1 →
              (∀ a b : α,
                weightedScoreProfileMargin w score a b - M a b =
                  blockImprovementChange x
                    (B.map (Function.Embedding.subtype
                      (fun z : α => z ≠ x))) δ a b) →
                B.Nonempty →
                  0 < δ →
                    selectedNLHF (α := α) τ M ρ x ≤
                      selectedNLHF (α := α) τ
                        (weightedScoreProfileMargin w score) ρ x

/-- Auxiliary weighted linear-order profile monotonicity, as the no-ties
specialization of weighted score profiles. -/
def SelectedNLHFWeightedLinearOrderProfileMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Fintype α] [DecidableEq α],
    ∀ {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
      {B : Finset {z : α // z ≠ x}} {δ : ℝ}
      {w : V → ℝ} {score : V → α → ℝ},
      IsLinearScoreProfile score →
        IsNormalizedMarginMatrix M →
          IsFullSupportLottery ρ →
            (∀ v : V, 0 ≤ w v) →
              Finset.univ.sum (fun v : V => w v) = 1 →
                (∀ a b : α,
                  weightedScoreProfileMargin w score a b - M a b =
                    blockImprovementChange x
                      (B.map (Function.Embedding.subtype
                        (fun z : α => z ≠ x))) δ a b) →
                  B.Nonempty →
                    0 < δ →
                      selectedNLHF (α := α) τ M ρ x ≤
                        selectedNLHF (α := α) τ
                          (weightedScoreProfileMargin w score) ρ x

/-!
### Paper-facing actual finite-profile clauses

These are the weak-order and linear-order profile predicates used by
`PaperStatements.NLHFmono`.  Voters are finite and counted uniformly by
`scoreProfileMargin`.
-/

/-- Actual finite weak-order profile monotonicity for the `1/8` clause of
Theorem `NLHFmono`.  A score function represents weak orders; equal scores
represent ties. -/
def SelectedNLHFWeakOrderProfileMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α],
    ∀ {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
      {B : Finset {z : α // z ≠ x}} {δ : ℝ}
      {score : V → α → ℝ},
      IsNormalizedMarginMatrix M →
        IsFullSupportLottery ρ →
          (∀ a b : α,
            scoreProfileMargin score a b - M a b =
              blockImprovementChange x
                (B.map (Function.Embedding.subtype
                  (fun z : α => z ≠ x))) δ a b) →
            B.Nonempty →
              0 < δ →
                selectedNLHF (α := α) τ M ρ x ≤
                  selectedNLHF (α := α) τ
                    (scoreProfileMargin score) ρ x

/-- Actual finite linear-order profile specialization of the positive `1/8`
clause of Theorem `NLHFmono`. -/
def SelectedNLHFLinearOrderProfileMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Nonempty V] [Fintype α] [DecidableEq α],
    ∀ {M : α → α → ℝ} {ρ : α → ℝ} {x : α}
      {B : Finset {z : α // z ≠ x}} {δ : ℝ}
      {score : V → α → ℝ},
      IsLinearScoreProfile score →
        IsNormalizedMarginMatrix M →
          IsFullSupportLottery ρ →
            (∀ a b : α,
              scoreProfileMargin score a b - M a b =
                blockImprovementChange x
                  (B.map (Function.Embedding.subtype
                    (fun z : α => z ≠ x))) δ a b) →
              B.Nonempty →
                0 < δ →
                  selectedNLHF (α := α) τ M ρ x ≤
                    selectedNLHF (α := α) τ
                      (scoreProfileMargin score) ρ x

/-- The `3/8` clause of Theorem `NLHFmono`, stated over all finite normalized
margin profiles. -/
theorem NLHFmono_all_profiles
    {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFAllProfileMonotonicity τ ↔ (3 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    exact (selectedNLHF_fin3_allProfileThreshold (τ := τ) hτ).mp
      (hmono (α := Fin 3))
  · intro hτge α _fintype _decidable
    exact (selectedNLHF_largeTau_monotone (α := α)) τ hτge

/-!
### Weighted proof scaffolding

The next weighted iff clauses are internal proof steps.  The
paper-facing iff clauses over actual finite profiles are stated later as
`NLHFmono_weak_order_profiles` and `NLHFmono_linear_order_profiles`.
-/

/-- The positive `1/8` half of Theorem `NLHFmono` for weighted weak-order
profiles. -/
theorem selectedNLHF_weightedWeakOrderProfileMonotone_of_tau_ge_one_eighth
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFWeightedWeakOrderProfileMonotonicity τ := by
  intro V α _fintypeV _fintypeα _decidableα
    M ρ x B δ w score hM hρ hw_nonneg hw_sum hchange hBne hδpos
  exact selectedNLHF_weightedScoreProfile_block_monotone_one_eighth
    (V := V) (α := α) (τ := τ) (δ := δ)
    (M := M) (ρ := ρ) (x := x) (B := B) (w := w) (score := score)
    hτge hM hρ hw_nonneg hw_sum hchange hBne hδpos

/-- Linear-order monotonicity follows from the weighted weak-order clause. -/
theorem SelectedNLHFWeightedWeakOrderProfileMonotonicity.toLinear
    {τ : ℝ}
    (hweak : SelectedNLHFWeightedWeakOrderProfileMonotonicity τ) :
    SelectedNLHFWeightedLinearOrderProfileMonotonicity τ := by
  intro V α _fintypeV _fintypeα _decidableα
    M ρ x B δ w score _hlinear hM hρ hw_nonneg hw_sum hchange hBne hδpos
  exact hweak (V := V) (α := α) (M := M) (ρ := ρ) (x := x)
    (B := B) (δ := δ) (w := w) (score := score)
    hM hρ hw_nonneg hw_sum hchange hBne hδpos

/-- Actual finite linear-order monotonicity is the no-ties specialization of
actual finite weak-order monotonicity. -/
theorem SelectedNLHFWeakOrderProfileMonotonicity.toLinear
    {τ : ℝ}
    (hweak : SelectedNLHFWeakOrderProfileMonotonicity τ) :
    SelectedNLHFLinearOrderProfileMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _fintypeα _decidableα
    M ρ x B δ score _hlinear hM hρ hchange hBne hδpos
  exact hweak (V := V) (α := α) (M := M) (ρ := ρ) (x := x)
    (B := B) (δ := δ) (score := score)
    hM hρ hchange hBne hδpos

/-- The positive `1/8` half of Theorem `NLHFmono` for weighted linear-order
profiles. -/
theorem selectedNLHF_weightedLinearOrderProfileMonotone_of_tau_ge_one_eighth
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFWeightedLinearOrderProfileMonotonicity τ :=
  SelectedNLHFWeightedWeakOrderProfileMonotonicity.toLinear
    (selectedNLHF_weightedWeakOrderProfileMonotone_of_tau_ge_one_eighth hτge)

/-- The positive `1/8` half of Theorem `NLHFmono` for actual finite weak-order
profiles represented by score functions. -/
theorem selectedNLHF_weakOrderProfileMonotone_of_tau_ge_one_eighth
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFWeakOrderProfileMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _fintypeα _decidableα
    M ρ x B δ score hM hρ hchange hBne hδpos
  exact selectedNLHF_scoreProfile_block_monotone_one_eighth
    (V := V) (α := α) (τ := τ) (δ := δ)
    (M := M) (ρ := ρ) (x := x) (B := B) (score := score)
    hτge hM hρ hchange hBne hδpos

/-- The positive `1/8` half of Theorem `NLHFmono` for actual finite
linear-order profiles represented by score functions. -/
theorem selectedNLHF_linearOrderProfileMonotone_of_tau_ge_one_eighth
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFLinearOrderProfileMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _fintypeα _decidableα
    M ρ x B δ score hlinear hM hρ hchange hBne hδpos
  exact selectedNLHF_linearScoreProfile_block_monotone_one_eighth
    (V := V) (α := α) (τ := τ) (δ := δ)
    (M := M) (ρ := ρ) (x := x) (B := B) (score := score)
    hlinear hτge hM hρ hchange hBne hδpos

/-- The linear-order weighted-profile witness gives the converse of the
`1/8` clause. -/
theorem not_selectedNLHF_weightedLinearOrderProfileMonotone_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
    ¬ SelectedNLHFWeightedLinearOrderProfileMonotonicity τ := by
  intro hmono
  rcases selectedNLHF_linear_lowTempWeightedProfileDrop_fin3 τ hτpos hτlt with
    ⟨b, η, δ, _hb0, _hb1, hη0, hη1, hδpos, hδleη, hρ, hdrop⟩
  let oldM : Fin 3 → Fin 3 → ℝ :=
    weightedScoreProfileMargin (nlhfSharpLinearWeights3 η)
      nlhfSharpLinearScore3
  let newW : Fin 2 → ℝ := nlhfSharpLinearWeights3Improved η δ
  let newM : Fin 3 → Fin 3 → ℝ :=
    weightedScoreProfileMargin newW nlhfSharpLinearScore3
  let ρ : Fin 3 → ℝ :=
    nlhfBacksolvedReference τ oldM (nlhfSharpSymLottery3 b)
  let B : Finset {z : Fin 3 // z ≠ 0} := {⟨1, by decide⟩}
  have hη2 : η ≤ 2 := by linarith
  have hδnonneg : 0 ≤ δ := hδpos.le
  have hold : oldM = nlhfSharpLinearMargin3 η := by
    dsimp [oldM]
    exact nlhfSharpLinearMargin3_eq_weightedProfile η
  have hnew :
      newM = improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ := by
    dsimp [newM, newW]
    exact nlhfSharpLinearImproved_eq_improvePairMargin η δ
  have hM : IsNormalizedMarginMatrix oldM := by
    rw [hold]
    exact nlhfSharpLinearMargin3_normalized hη0.le hη2
  have hnewW_nonneg : ∀ v : Fin 2, 0 ≤ newW v := by
    dsimp [newW]
    exact nlhfSharpLinearWeights3Improved_nonneg hη2 hδnonneg hδleη
  have hnewW_sum : Finset.univ.sum (fun v : Fin 2 => newW v) = 1 := by
    dsimp [newW]
    exact nlhfSharpLinearWeights3Improved_sum η δ
  have hchange : ∀ a b' : Fin 3,
      newM a b' - oldM a b' =
        blockImprovementChange 0
          (B.map (Function.Embedding.subtype
            (fun z : Fin 3 => z ≠ 0))) δ a b' := by
    intro a b'
    rw [hnew, hold]
    simpa [B] using
      improvePairMargin_change_eq_blockImprovementChange_singleton
        (nlhfSharpLinearMargin3 η) δ (by decide : (1 : Fin 3) ≠ 0) a b'
  have hBne : B.Nonempty := by
    exact ⟨⟨1, by decide⟩, by simp [B]⟩
  have hle :
      selectedNLHF (α := Fin 3) τ oldM ρ 0 ≤
        selectedNLHF (α := Fin 3) τ newM ρ 0 :=
    hmono (V := Fin 2) (α := Fin 3) (M := oldM) (ρ := ρ)
      (x := 0) (B := B) (δ := δ) (w := newW)
      (score := nlhfSharpLinearScore3)
      nlhfSharpLinearScore3_linear hM hρ hnewW_nonneg hnewW_sum
      hchange hBne hδpos
  exact not_lt_of_ge hle hdrop

/-- The linear-order witness also gives the weak-order converse, since linear
orders are weak orders with no ties. -/
theorem not_selectedNLHF_weightedWeakOrderProfileMonotone_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
    ¬ SelectedNLHFWeightedWeakOrderProfileMonotonicity τ := by
  intro hweak
  exact not_selectedNLHF_weightedLinearOrderProfileMonotone_of_tau_lt_one_eighth
    hτpos hτlt
    (SelectedNLHFWeightedWeakOrderProfileMonotonicity.toLinear hweak)

/-- The denominator-cleared finite-profile witness gives the converse of the
actual finite linear-order `1/8` clause. -/
theorem not_selectedNLHF_linearOrderProfileMonotone_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
    ¬ SelectedNLHFLinearOrderProfileMonotonicity τ := by
  intro hmono
  rcases selectedNLHF_linear_lowTempFiniteProfileBlockDrop_fin3 τ hτpos hτlt with
    ⟨N, m, b, δ, B, _hN, _hb0, _hb1, hδpos, hBne, hρ,
      _holdLinear, hnewLinear, _himprove, hchange, hdrop⟩
  let V : Type :=
    Sum (Fin (((N - 1) * (m + 1)) + 1)) (Fin ((m + 1) - 1))
  haveI : Nonempty V := inferInstance
  have hM :
      IsNormalizedMarginMatrix
        (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m)) :=
    scoreProfileMargin_normalized (nlhfSharpLinearReplicatedOldScore3 N m)
  have hle :
      selectedNLHF (α := Fin 3) τ
          (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) 0 ≤
        selectedNLHF (α := Fin 3) τ
          (scoreProfileMargin (nlhfSharpLinearReplicatedMovedScore3 N m))
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
            (nlhfSharpSymLottery3 b)) 0 :=
    hmono (V := V) (α := Fin 3)
      (M := scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
      (ρ := nlhfBacksolvedReference τ
        (scoreProfileMargin (nlhfSharpLinearReplicatedOldScore3 N m))
        (nlhfSharpSymLottery3 b))
      (x := 0) (B := B) (δ := δ)
      (score := nlhfSharpLinearReplicatedMovedScore3 N m)
      hnewLinear hM hρ hchange hBne hδpos
  exact not_lt_of_ge hle hdrop

/-- The same finite linear-order witness gives the converse of the actual
finite weak-order `1/8` clause. -/
theorem not_selectedNLHF_weakOrderProfileMonotone_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
    ¬ SelectedNLHFWeakOrderProfileMonotonicity τ := by
  intro hweak
  exact not_selectedNLHF_linearOrderProfileMonotone_of_tau_lt_one_eighth
    hτpos hτlt
    (SelectedNLHFWeakOrderProfileMonotonicity.toLinear hweak)

/-- The weak-order `1/8` clause of Theorem `NLHFmono`, in the weighted
score-profile formalization used by the appendix proof. -/
theorem NLHFmono_weighted_weak_order_profiles
    {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFWeightedWeakOrderProfileMonotonicity τ ↔
      (1 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    by_contra hnot
    exact not_selectedNLHF_weightedWeakOrderProfileMonotone_of_tau_lt_one_eighth
      hτ (lt_of_not_ge hnot) hmono
  · intro hτge
    exact selectedNLHF_weightedWeakOrderProfileMonotone_of_tau_ge_one_eighth
      hτge

/-- The linear-order `1/8` clause of Theorem `NLHFmono`, in the weighted
score-profile formalization used by the appendix proof. -/
theorem NLHFmono_weighted_linear_order_profiles
    {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFWeightedLinearOrderProfileMonotonicity τ ↔
      (1 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    by_contra hnot
    exact not_selectedNLHF_weightedLinearOrderProfileMonotone_of_tau_lt_one_eighth
      hτ (lt_of_not_ge hnot) hmono
  · intro hτge
    exact selectedNLHF_weightedLinearOrderProfileMonotone_of_tau_ge_one_eighth
      hτge

/-!
### Final finite-profile `1/8` clauses
-/

/-- The weak-order `1/8` clause of Theorem `NLHFmono`, stated over actual
finite profiles represented by score functions and interpreted by uniform
voter counting. -/
theorem NLHFmono_weak_order_profiles
    {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFWeakOrderProfileMonotonicity τ ↔
      (1 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    by_contra hnot
    exact not_selectedNLHF_weakOrderProfileMonotone_of_tau_lt_one_eighth
      hτ (lt_of_not_ge hnot) hmono
  · intro hτge
    exact selectedNLHF_weakOrderProfileMonotone_of_tau_ge_one_eighth hτge

/-- The linear-order `1/8` clause of Theorem `NLHFmono`, stated over actual
finite profiles represented by score functions and interpreted by uniform
voter counting. -/
theorem NLHFmono_linear_order_profiles
    {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFLinearOrderProfileMonotonicity τ ↔
      (1 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    by_contra hnot
    exact not_selectedNLHF_linearOrderProfileMonotone_of_tau_lt_one_eighth
      hτ (lt_of_not_ge hnot) hmono
  · intro hτge
    exact selectedNLHF_linearOrderProfileMonotone_of_tau_ge_one_eighth hτge

end PaperFormalization
