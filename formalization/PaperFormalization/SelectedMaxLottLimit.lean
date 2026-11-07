import PaperFormalization.MaximalLotteryLimit
import PaperFormalization.NLHFExistence

/-!
# The maximal-lottery limit for the selected NLHF rule

Completes the formalization of Proposition `MaxLottProp` in
`paper/main.tex`: the abstract limiting-saddle theorem
`PaperFormalization.MaxLottProp` is instantiated with the actual
`selectedNLHF` outputs.  The saddle hypothesis is discharged via
`regularizedClosedSaddle_of_fixedPoint`, and the paper's
convergent-subsequence clause is obtained from compactness of the lottery
simplex (`isCompact_setOf_isLottery`).
-/

open scoped BigOperators
open scoped Topology
open Filter

namespace PaperFormalization

variable {α : Type*} [Fintype α]

/-- The selected NLHF output is a lottery on the paper's valid domain. -/
lemma selectedNLHF_isLottery
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ) (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    IsLottery (selectedNLHF τ M ρ) :=
  ((selectedNLHF_selection hτ hM hρ).2.2.1).toLottery

/-- The selected NLHF output is a diagonal regularized closed saddle: the
bridge from the fixed-point selection to the saddle property. -/
lemma selectedNLHF_regularizedClosedSaddle
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ) (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    IsNLHFRegularizedClosedSaddle τ M ρ
      (selectedNLHF τ M ρ) (selectedNLHF τ M ρ) :=
  regularizedClosedSaddle_of_fixedPoint hM (selectedNLHF_selection hτ hM hρ)

/-- A diagonal regularized closed saddle satisfies the `2τ(KL − KL) ≤ value`
inequality required by `PaperFormalization.MaxLottProp`. -/
lemma closedSaddle_diag_margin_bound
    {τ : ℝ} {M : α → α → ℝ} {ρ π : α → ℝ}
    (hM : IsNormalizedMarginMatrix M)
    (hsaddle : IsNLHFRegularizedClosedSaddle τ M ρ π π)
    {ν : α → ℝ} (hν : IsLottery ν) :
    2 * τ * (KL π ρ - KL ν ρ) ≤ marginValue M π ν := by
  have h := hsaddle.2.2.2 ν hν
  have hlam : (1 : ℝ) / nlhfLambda τ = 2 * τ := by
    unfold nlhfLambda
    exact one_div_one_div _
  have hself : marginValue M π π = 0 :=
    marginValue_self_eq_zero_of_normalized π hM
  unfold nlhfSionValue at h
  rw [hself, hlam] at h
  linarith

/-- The saddle hypothesis of `PaperFormalization.MaxLottProp`, discharged
for `selectedNLHF` outputs. -/
lemma selectedNLHF_saddle_margin_bound
    {τ : ℝ} {M : α → α → ℝ} {ρ : α → ℝ}
    (hτ : 0 < τ) (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    {ν : α → ℝ} (hν : IsLottery ν) :
    2 * τ * (KL (selectedNLHF τ M ρ) ρ - KL ν ρ) ≤
      marginValue M (selectedNLHF τ M ρ) ν :=
  closedSaddle_diag_margin_bound hM
    (selectedNLHF_regularizedClosedSaddle hτ hM hρ) hν

/-- Every convergent subsequence of selected NLHF outputs with `τ_n → 0`
converges to a maximal lottery; lottery-hood of the limit is derived from
closedness of the simplex rather than assumed. -/
theorem maximalLottery_of_selectedNLHF_subseq_tendsto
    {M : α → α → ℝ} {ρ : α → ℝ} {τn : ℕ → ℝ}
    (hτpos : ∀ n : ℕ, 0 < τn n)
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {π : α → ℝ}
    (hπn : ∀ x : α,
      Tendsto (fun n => selectedNLHF (τn (φ n)) M ρ x) atTop (𝓝 (π x))) :
    IsMaximalLottery M π := by
  have hπlot : IsLottery π := by
    have hfull :
        Tendsto (fun n => selectedNLHF (τn (φ n)) M ρ) atTop (𝓝 π) :=
      tendsto_pi_nhds.mpr hπn
    exact isClosed_setOf_isLottery.mem_of_tendsto hfull
      (Eventually.of_forall fun n =>
        selectedNLHF_isLottery (hτpos (φ n)) hM hρ)
  have hτφ : Tendsto (fun n => τn (φ n)) atTop (𝓝 (0 : ℝ)) :=
    hτ.comp hφ.tendsto_atTop
  exact PaperFormalization.MaxLottProp hπlot hρ hπn hτφ
    (fun n ν hν => selectedNLHF_saddle_margin_bound (hτpos (φ n)) hM hρ hν)

/-- Existence half of the paper's `MaxLottProp`: some subsequence of the
selected NLHF outputs converges, and its limit is a maximal lottery. -/
theorem exists_subseq_selectedNLHF_tendsto_maximalLottery
    {M : α → α → ℝ} {ρ : α → ℝ} {τn : ℕ → ℝ}
    (hτpos : ∀ n : ℕ, 0 < τn n)
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hM : IsNormalizedMarginMatrix M)
    (hρ : IsFullSupportLottery ρ) :
    ∃ π : α → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ x : α,
        Tendsto (fun n => selectedNLHF (τn (φ n)) M ρ x) atTop (𝓝 (π x))) ∧
      IsMaximalLottery M π := by
  classical
  set u : ℕ → α → ℝ := fun n => selectedNLHF (τn n) M ρ with hu
  have hu_mem : ∀ n : ℕ, u n ∈ {p : α → ℝ | IsLottery p} := fun n =>
    selectedNLHF_isLottery (hτpos n) hM hρ
  rcases isCompact_setOf_isLottery.tendsto_subseq hu_mem with
    ⟨π, _hπmem, φ, hφmono, hφlim⟩
  have hcoord : ∀ x : α,
      Tendsto (fun n => selectedNLHF (τn (φ n)) M ρ x) atTop (𝓝 (π x)) := by
    intro x
    simpa [u, Function.comp_def] using (tendsto_pi_nhds.1 hφlim x)
  exact ⟨π, φ, hφmono, hcoord,
    maximalLottery_of_selectedNLHF_subseq_tendsto hτpos hτ hM hρ hφmono hcoord⟩

end PaperFormalization
