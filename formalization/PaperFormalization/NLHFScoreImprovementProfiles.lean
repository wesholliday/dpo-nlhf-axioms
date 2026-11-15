import PaperFormalization.NLHFScoreImprovementChaining
import PaperFormalization.NLHFWeakProfileMonotonicity

open scoped BigOperators

namespace PaperFormalization

/-! # The `1/8` clauses of Theorem `NLHFmono` under the paper's conditions

`SelectedNLHFWeakOrderProfileMonotonicity` hypothesizes a *single uniform
block improvement* of the margin matrix.  The predicates below instead
hypothesize the paper's improvement conditions (i)–(iii) between two actual
score-represented weak-order profiles over a common electorate; the positive
direction is then the paper's chaining argument, formalized in
`NLHFScoreImprovementChaining`. -/

/-- Probabilistic monotonicity of selected NLHF over actual finite weak-order
profiles (score-represented), with the paper's improvement conditions
(i)–(iii). -/
def SelectedNLHFWeakOrderImprovementMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype α] [DecidableEq α],
    ∀ (score score' : V → α → ℝ) (ρ : α → ℝ) (x : α),
      IsFullSupportLottery ρ →
        IsWeakProfileImprovement (scoreWeakProfile score)
            (scoreWeakProfile score') x →
          selectedNLHF (α := α) τ (scoreProfileMargin score) ρ x ≤
            selectedNLHF (α := α) τ (scoreProfileMargin score') ρ x

/-- Linear-order specialization: both profiles are tie-free. -/
def SelectedNLHFLinearOrderImprovementMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype α] [DecidableEq α],
    ∀ (score score' : V → α → ℝ) (ρ : α → ℝ) (x : α),
      IsLinearScoreProfile score →
        IsLinearScoreProfile score' →
          IsFullSupportLottery ρ →
            IsWeakProfileImprovement (scoreWeakProfile score)
                (scoreWeakProfile score') x →
              selectedNLHF (α := α) τ (scoreProfileMargin score) ρ x ≤
                selectedNLHF (α := α) τ (scoreProfileMargin score') ρ x

/-- Pointwise `1/8` monotonicity of selected NLHF for the paper's improvement
conditions on score-represented weak orders. -/
theorem selectedNLHF_scoreProfile_improvement_monotone_of_tau_ge_one_eighth
    {V α : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype α] [DecidableEq α]
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ)
    {score score' : V → α → ℝ} {ρ : α → ℝ} {x : α}
    (hρ : IsFullSupportLottery ρ)
    (himp : IsWeakProfileImprovement (scoreWeakProfile score)
      (scoreWeakProfile score') x) :
    selectedNLHF (α := α) τ (scoreProfileMargin score) ρ x ≤
      selectedNLHF (α := α) τ (scoreProfileMargin score') ρ x :=
  nlhf_scoreProfile_improvement_monotone_of_tau_ge_one_eighth_selected
    (selectedNLHF_selection (α := α))
    (selectedVariationalInequality_of_fixedPointSelection
      (selectedNLHF_selection (α := α)))
    hτge hρ himp

theorem selectedNLHF_weakOrderImprovementMonotone_of_tau_ge_one_eighth
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFWeakOrderImprovementMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _decidableV _fintypeα _decidableα
    score score' ρ x hρ himp
  exact selectedNLHF_scoreProfile_improvement_monotone_of_tau_ge_one_eighth
    hτge hρ himp

theorem SelectedNLHFWeakOrderImprovementMonotonicity.toLinear
    {τ : ℝ} (hweak : SelectedNLHFWeakOrderImprovementMonotonicity τ) :
    SelectedNLHFLinearOrderImprovementMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _decidableV _fintypeα _decidableα
    score score' ρ x _hlin _hlin' hρ himp
  exact hweak (V := V) (α := α) score score' ρ x hρ himp

theorem selectedNLHF_linearOrderImprovementMonotone_of_tau_ge_one_eighth
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFLinearOrderImprovementMonotonicity τ :=
  SelectedNLHFWeakOrderImprovementMonotonicity.toLinear
    (selectedNLHF_weakOrderImprovementMonotone_of_tau_ge_one_eighth hτge)

/-! ## The common-electorate linear-order converse witness

The old and improved profiles below live on the *same* electorate `Fin K` and
differ at exactly one voter, who moves from the ballot `yxz` to the ballot
`xyz`.  This is the paper's move, and it satisfies conditions (i)–(iii). -/

/-- Threshold linear-order profile: the first `j` voters have the ballot
`xyz`, the rest have `yxz`. -/
noncomputable def nlhfSharpLinearThresholdScore3 (K j : ℕ) : Fin K → Fin 3 → ℝ :=
  fun u => nlhfSharpLinearScore3 (if (u : ℕ) < j then 0 else 1)

lemma nlhfSharpLinearThresholdScore3_linear (K j : ℕ) :
    IsLinearScoreProfile (nlhfSharpLinearThresholdScore3 K j) :=
  nlhfSharpLinearScore3_assigned_linear
    (fun u : Fin K => if (u : ℕ) < j then 0 else 1)

lemma nlhfSharpLinearThresholdScore3_fiber_card_zero (K j : ℕ) (hj : j ≤ K) :
    (Finset.univ.filter (fun u : Fin K =>
      (if (u : ℕ) < j then (0 : Fin 2) else 1) = 0)).card = j := by
  classical
  have hcongr : (Finset.univ.filter (fun u : Fin K =>
      (if (u : ℕ) < j then (0 : Fin 2) else 1) = 0)) =
      Finset.univ.filter (fun u : Fin K => (u : ℕ) < j) := by
    refine Finset.filter_congr ?_
    intro u _hu
    by_cases h : (u : ℕ) < j <;> simp [h]
  rw [hcongr, card_filter_fin_lt K j hj]

lemma card_filter_fin_not_lt (K j : ℕ) (hj : j ≤ K) :
    (Finset.univ.filter (fun u : Fin K => ¬ ((u : ℕ) < j))).card = K - j := by
  classical
  have himg :
      Finset.image (fun u : Fin K => (u : ℕ))
          (Finset.univ.filter (fun u : Fin K => ¬ ((u : ℕ) < j))) =
        Finset.Ico j K := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨u, hu, hun⟩
      rw [← hun]
      exact Finset.mem_Ico.mpr
        ⟨le_of_not_gt (Finset.mem_filter.mp hu).2, u.isLt⟩
    · intro hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
      refine Finset.mem_image.mpr ⟨⟨n, hn2⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mpr hn1⟩
  have hinj : Set.InjOn (fun u : Fin K => (u : ℕ))
      ↑(Finset.univ.filter (fun u : Fin K => ¬ ((u : ℕ) < j))) := by
    intro a _ha b _hb hab
    exact Fin.val_injective hab
  rw [← Finset.card_image_of_injOn hinj, himg, Nat.card_Ico]

lemma nlhfSharpLinearThresholdScore3_fiber_card_one (K j : ℕ) (hj : j ≤ K) :
    (Finset.univ.filter (fun u : Fin K =>
      (if (u : ℕ) < j then (0 : Fin 2) else 1) = 1)).card = K - j := by
  classical
  have hcongr : (Finset.univ.filter (fun u : Fin K =>
      (if (u : ℕ) < j then (0 : Fin 2) else 1) = 1)) =
      Finset.univ.filter (fun u : Fin K => ¬ ((u : ℕ) < j)) := by
    refine Finset.filter_congr ?_
    intro u _hu
    by_cases h : (u : ℕ) < j <;> simp [h]
  rw [hcongr, card_filter_fin_not_lt K j hj]

lemma scoreProfileMargin_nlhfSharpLinearThresholdScore3
    (K j : ℕ) (hj : j ≤ K) (hK : 0 < K) :
    scoreProfileMargin (nlhfSharpLinearThresholdScore3 K j) =
      nlhfSharpLinearMargin3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) := by
  classical
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKR
  refine nlhfSharpLinearMargin3_eq_scoreProfile_of_fiber_weights
    (fun u : Fin K => if (u : ℕ) < j then (0 : Fin 2) else 1) ?_
  intro v
  fin_cases v
  · show nlhfSharpLinearWeights3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 0 =
      ((Finset.univ.filter (fun u : Fin K =>
        (if (u : ℕ) < j then (0 : Fin 2) else 1) = 0)).card : ℝ) /
        (Fintype.card (Fin K) : ℝ)
    rw [nlhfSharpLinearThresholdScore3_fiber_card_zero K j hj, Fintype.card_fin]
    show (1 : ℝ) - (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) / 2 = (j : ℝ) / (K : ℝ)
    field_simp
    ring
  · show nlhfSharpLinearWeights3 (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) 1 =
      ((Finset.univ.filter (fun u : Fin K =>
        (if (u : ℕ) < j then (0 : Fin 2) else 1) = 1)).card : ℝ) /
        (Fintype.card (Fin K) : ℝ)
    rw [nlhfSharpLinearThresholdScore3_fiber_card_one K j hj, Fintype.card_fin,
      Nat.cast_sub hj]
    show (2 * ((K : ℝ) - (j : ℝ)) / (K : ℝ)) / 2 = ((K : ℝ) - (j : ℝ)) / (K : ℝ)
    field_simp

/-- Moving the single voter at index `j` from `yxz` to `xyz` satisfies the
paper's improvement conditions (i)–(iii) for `x = 0`. -/
lemma nlhfSharpLinearThresholdScore3_improvement (K j : ℕ) :
    IsWeakProfileImprovement
      (scoreWeakProfile (nlhfSharpLinearThresholdScore3 K j))
      (scoreWeakProfile (nlhfSharpLinearThresholdScore3 K (j + 1)))
      (0 : Fin 3) := by
  have hsame : ∀ (u : Fin K) (a b : Fin 3),
      ¬ ((u : ℕ) = j) →
      scoreWeakProfile (nlhfSharpLinearThresholdScore3 K (j + 1)) u a b =
        scoreWeakProfile (nlhfSharpLinearThresholdScore3 K j) u a b := by
    intro u a b hu
    have hiff : ((u : ℕ) < j + 1) = ((u : ℕ) < j) := by
      by_cases h : (u : ℕ) < j
      · simp [h, Nat.lt_succ_of_lt h]
      · have : ¬ ((u : ℕ) < j + 1) := by omega
        simp [h, this]
    simp only [scoreWeakProfile, nlhfSharpLinearThresholdScore3, hiff]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro u y hy hR
    by_cases hu : (u : ℕ) = j
    · have hold : ¬ ((u : ℕ) < j) := by omega
      have hnew : (u : ℕ) < j + 1 := by omega
      simp only [scoreWeakProfile, nlhfSharpLinearThresholdScore3, hold,
        hnew, if_false, if_true, decide_eq_true_eq] at hR ⊢
      fin_cases y <;>
        simp_all [nlhfSharpLinearScore3] <;> norm_num
    · rw [hsame u 0 y hu]
      exact hR
  · intro u y hy hR
    by_cases hu : (u : ℕ) = j
    · have hold : ¬ ((u : ℕ) < j) := by omega
      have hnew : (u : ℕ) < j + 1 := by omega
      simp only [scoreWeakProfile, nlhfSharpLinearThresholdScore3, hold,
        hnew, if_false, if_true, decide_eq_false_iff_not, not_le] at hR ⊢
      fin_cases y <;>
        simp_all [nlhfSharpLinearScore3] <;> norm_num
    · rw [hsame u y 0 hu]
      exact hR
  · intro u y z hy hz
    by_cases hu : (u : ℕ) = j
    · have hold : ¬ ((u : ℕ) < j) := by omega
      have hnew : (u : ℕ) < j + 1 := by omega
      simp only [scoreWeakProfile, nlhfSharpLinearThresholdScore3, hold,
        hnew, if_false, if_true]
      fin_cases y <;> fin_cases z <;>
        simp_all [nlhfSharpLinearScore3] <;> norm_num
    · exact hsame u y z hu

/-- A one-pair improvement of the linear sharpness matrix is again a linear
sharpness matrix with a smaller parameter. -/
lemma improvePairMargin_nlhfSharpLinearMargin3 (η δ : ℝ) :
    improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 δ =
      nlhfSharpLinearMargin3 (η - δ) := by
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp [improvePairMargin, nlhfSharpLinearMargin3] <;> ring

/-- Low-temperature converse for the paper-conditions `1/8` clause, on a
common electorate: two actual finite linear-order profiles differing at one
voter, related by the paper's conditions (i)–(iii), with a strict drop. -/
theorem nlhfSharpLinearThreshold_lowTempProfileDrop_fin3
    (F : ℝ → MatrixRule (Fin 3))
    (hselect : IsNLHFFixedPointSelection F)
    (hunique : IsTheNLHF F) :
    ∀ τ : ℝ, 0 < τ → τ < (1 : ℝ) / 8 →
      ∃ N m : ℕ, ∃ b : ℝ,
        0 < N ∧ 0 < b ∧ b < 1 ∧
        IsLinearScoreProfile
          (nlhfSharpLinearThresholdScore3 (N * (m + 1)) ((N - 1) * (m + 1))) ∧
        IsLinearScoreProfile
          (nlhfSharpLinearThresholdScore3 (N * (m + 1))
            ((N - 1) * (m + 1) + 1)) ∧
        IsWeakProfileImprovement
          (scoreWeakProfile (nlhfSharpLinearThresholdScore3 (N * (m + 1))
            ((N - 1) * (m + 1))))
          (scoreWeakProfile (nlhfSharpLinearThresholdScore3 (N * (m + 1))
            ((N - 1) * (m + 1) + 1)))
          (0 : Fin 3) ∧
        IsFullSupportLottery
          (nlhfBacksolvedReference τ
            (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
              ((N - 1) * (m + 1))))
            (nlhfSharpSymLottery3 b)) ∧
        F τ
            (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
              ((N - 1) * (m + 1) + 1)))
            (nlhfBacksolvedReference τ
              (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
                ((N - 1) * (m + 1))))
              (nlhfSharpSymLottery3 b)) 0 <
          F τ
            (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
              ((N - 1) * (m + 1))))
            (nlhfBacksolvedReference τ
              (scoreProfileMargin (nlhfSharpLinearThresholdScore3 (N * (m + 1))
                ((N - 1) * (m + 1))))
              (nlhfSharpSymLottery3 b)) 0 := by
  intro τ hτ hτlt
  rcases exists_linearOrderFiniteEtaSharpnessScalar_of_tau_lt_one_eighth
      hτ hτlt with
    ⟨N, b, η, a, d, hN, hb0, hb1, hηeq, hη0, hη1, ha, hd,
      ha0, hd0, _hnorm, hlimitneg⟩
  let sseq : ℕ → ℝ := fun n => η * (1 / ((n : ℝ) + 1))
  have hspos : ∀ n : ℕ, 0 < sseq n := by
    intro n
    dsimp [sseq]
    positivity
  have hsle : ∀ n : ℕ, sseq n ≤ η := by
    intro n
    have hdenpos : 0 < (n : ℝ) + 1 := by positivity
    have hone : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith
    dsimp [sseq]
    exact mul_le_of_le_one_right hη0.le hone
  have hone_tendsto :
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hstendsto : Filter.Tendsto sseq Filter.atTop (nhds 0) := by
    simpa [sseq] using
      (tendsto_const_nhds.mul hone_tendsto :
        Filter.Tendsto
          (fun n : ℕ => η * (1 / ((n : ℝ) + 1)))
          Filter.atTop (nhds (η * 0)))
  rcases exists_nlhfSharpLinear_secant_drop_of_small_sequence
      F hselect hunique hτ hb0 hb1 hη0 hη1 ha hd ha0 hd0 hlimitneg
      hspos hsle hstendsto with
    ⟨m, _hsmpos, _hsmle, hdrop⟩
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
  have hmne : ((m : ℝ) + 1) ≠ 0 := ne_of_gt hmpos
  have hsplit : N * (m + 1) = (N - 1) * (m + 1) + (m + 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hn : n + 1 - 1 = n := by omega
    rw [hn]
    ring
  have hj : (N - 1) * (m + 1) ≤ N * (m + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le N 1)
  have hj1 : (N - 1) * (m + 1) + 1 ≤ N * (m + 1) := by
    rw [hsplit]
    exact Nat.add_le_add_left (by omega : 1 ≤ m + 1) _
  have hKpos : 0 < N * (m + 1) := Nat.mul_pos hN (Nat.succ_pos m)
  have hcastsplit : ((N * (m + 1) : ℕ) : ℝ) =
      (((N - 1) * (m + 1) : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  have hmcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hKj : ((N * (m + 1) : ℕ) : ℝ) - (((N - 1) * (m + 1) : ℕ) : ℝ) =
      (m : ℝ) + 1 := by
    rw [hmcast] at hcastsplit
    linarith
  have hKj1 : ((N * (m + 1) : ℕ) : ℝ) -
      (((N - 1) * (m + 1) + 1 : ℕ) : ℝ) = (m : ℝ) := by
    have hstep : (((N - 1) * (m + 1) + 1 : ℕ) : ℝ) =
        (((N - 1) * (m + 1) : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hstep]
    linarith
  have hKR : ((N * (m + 1) : ℕ) : ℝ) = (N : ℝ) * ((m : ℝ) + 1) := by
    push_cast
    ring
  have hold :
      scoreProfileMargin
          (nlhfSharpLinearThresholdScore3 (N * (m + 1)) ((N - 1) * (m + 1))) =
        nlhfSharpLinearMargin3 η := by
    rw [scoreProfileMargin_nlhfSharpLinearThresholdScore3 _ _ hj hKpos]
    congr 1
    rw [hKj, hKR, hηeq]
    field_simp
  have hnew :
      scoreProfileMargin
          (nlhfSharpLinearThresholdScore3 (N * (m + 1))
            ((N - 1) * (m + 1) + 1)) =
        improvePairMargin (nlhfSharpLinearMargin3 η) 0 1 (sseq m) := by
    rw [improvePairMargin_nlhfSharpLinearMargin3,
      scoreProfileMargin_nlhfSharpLinearThresholdScore3 _ _ hj1 hKpos]
    congr 1
    rw [hKj1, hKR]
    dsimp [sseq]
    rw [hηeq]
    field_simp
    ring
  have hρ :
      IsFullSupportLottery
        (nlhfBacksolvedReference τ
          (scoreProfileMargin
            (nlhfSharpLinearThresholdScore3 (N * (m + 1)) ((N - 1) * (m + 1))))
          (nlhfSharpSymLottery3 b)) :=
    nlhfBacksolvedReference_fullSupport
      (nlhfSharpSymLottery3_fullSupport hb0 hb1)
  refine ⟨N, m, b, hN, hb0, hb1,
    nlhfSharpLinearThresholdScore3_linear _ _,
    nlhfSharpLinearThresholdScore3_linear _ _,
    nlhfSharpLinearThresholdScore3_improvement _ _, hρ, ?_⟩
  rw [hold, hnew]
  exact hdrop

theorem not_selectedNLHF_linearOrderImprovementMonotone_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
    ¬ SelectedNLHFLinearOrderImprovementMonotonicity τ := by
  intro hmono
  rcases nlhfSharpLinearThreshold_lowTempProfileDrop_fin3
      (selectedNLHF (α := Fin 3))
      (selectedNLHF_selection (α := Fin 3))
      (selectedNLHF_isTheNLHF (α := Fin 3)) τ hτpos hτlt with
    ⟨N, m, b, hN, _hb0, _hb1, hlin, hlin', himp, hρ, hdrop⟩
  haveI : Nonempty (Fin (N * (m + 1))) :=
    ⟨⟨0, Nat.mul_pos hN (Nat.succ_pos m)⟩⟩
  have hle := hmono (V := Fin (N * (m + 1))) (α := Fin 3)
    (nlhfSharpLinearThresholdScore3 (N * (m + 1)) ((N - 1) * (m + 1)))
    (nlhfSharpLinearThresholdScore3 (N * (m + 1)) ((N - 1) * (m + 1) + 1))
    (nlhfBacksolvedReference τ
      (scoreProfileMargin
        (nlhfSharpLinearThresholdScore3 (N * (m + 1)) ((N - 1) * (m + 1))))
      (nlhfSharpSymLottery3 b))
    0 hlin hlin' hρ himp
  exact not_lt_of_ge hle hdrop

theorem not_selectedNLHF_weakOrderImprovementMonotone_of_tau_lt_one_eighth
    {τ : ℝ} (hτpos : 0 < τ) (hτlt : τ < (1 : ℝ) / 8) :
    ¬ SelectedNLHFWeakOrderImprovementMonotonicity τ := by
  intro hweak
  exact not_selectedNLHF_linearOrderImprovementMonotone_of_tau_lt_one_eighth
    hτpos hτlt (SelectedNLHFWeakOrderImprovementMonotonicity.toLinear hweak)

/-- The weak-order `1/8` clause of Theorem `NLHFmono`, under the paper's
improvement conditions (i)–(iii) on actual finite profiles. -/
theorem NLHFmono_weak_order_improvements {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFWeakOrderImprovementMonotonicity τ ↔ (1 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    by_contra hnot
    exact not_selectedNLHF_weakOrderImprovementMonotone_of_tau_lt_one_eighth
      hτ (lt_of_not_ge hnot) hmono
  · intro hτge
    exact selectedNLHF_weakOrderImprovementMonotone_of_tau_ge_one_eighth hτge

/-- The linear-order `1/8` clause of Theorem `NLHFmono`, under the paper's
improvement conditions (i)–(iii) on actual finite profiles. -/
theorem NLHFmono_linear_order_improvements {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFLinearOrderImprovementMonotonicity τ ↔ (1 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    by_contra hnot
    exact not_selectedNLHF_linearOrderImprovementMonotone_of_tau_lt_one_eighth
      hτ (lt_of_not_ge hnot) hmono
  · intro hτge
    exact selectedNLHF_linearOrderImprovementMonotone_of_tau_ge_one_eighth hτge

end PaperFormalization
