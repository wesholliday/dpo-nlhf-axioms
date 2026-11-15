import PaperFormalization.Core

open scoped BigOperators
open scoped Topology
open Filter

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- Proposition `MaxLottProp`, in the exact abstract form used by the appendix:
if the regularized saddle inequality gives `penalty_n ≤ value(π_n,ν)`,
`π_n → π`, and the penalty vanishes, then the limit is a maximal lottery. -/
theorem maximalLottery_of_regularized_saddle_limit
    {M : α → α → ℝ} {π : α → ℝ} {πn : ℕ → α → ℝ}
    {penalty : ℕ → ℝ}
    (hπlot : IsLottery π)
    (hπn : ∀ x : α, Tendsto (fun n => πn n x) atTop (𝓝 (π x)))
    (hpenalty : Tendsto penalty atTop (𝓝 (0 : ℝ)))
    (hsaddle : ∀ n : ℕ, ∀ ν : α → ℝ, IsLottery ν →
      penalty n ≤ marginValue M (πn n) ν) :
    IsMaximalLottery M π := by
  refine ⟨hπlot, ?_⟩
  intro ν hν
  have hmargin :
      Tendsto (fun n => marginValue M (πn n) ν) atTop
        (𝓝 (marginValue M π ν)) := by
    unfold marginValue
    refine tendsto_finset_sum Finset.univ ?_
    intro x hx
    refine tendsto_finset_sum Finset.univ ?_
    intro y hy
    exact ((hπn x).mul tendsto_const_nhds).mul tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' hpenalty hmargin (fun n => hsaddle n ν hν)

omit [DecidableEq α] in
/-- A version of `MaxLottProp` closer to the appendix proof: the regularization
penalty may depend on the comparison lottery `ν`, and only needs to vanish
pointwise for each lottery. -/
theorem maximalLottery_of_regularized_saddle_limit_pointwise_penalty
    {M : α → α → ℝ} {π : α → ℝ} {πn : ℕ → α → ℝ}
    {penalty : (α → ℝ) → ℕ → ℝ}
    (hπlot : IsLottery π)
    (hπn : ∀ x : α, Tendsto (fun n => πn n x) atTop (𝓝 (π x)))
    (hpenalty : ∀ ν : α → ℝ, IsLottery ν →
      Tendsto (penalty ν) atTop (𝓝 (0 : ℝ)))
    (hsaddle : ∀ n : ℕ, ∀ ν : α → ℝ, IsLottery ν →
      penalty ν n ≤ marginValue M (πn n) ν) :
    IsMaximalLottery M π := by
  refine ⟨hπlot, ?_⟩
  intro ν hν
  have hmargin :
      Tendsto (fun n => marginValue M (πn n) ν) atTop
        (𝓝 (marginValue M π ν)) := by
    unfold marginValue
    refine tendsto_finset_sum Finset.univ ?_
    intro x hx
    refine tendsto_finset_sum Finset.univ ?_
    intro y hy
    exact ((hπn x).mul tendsto_const_nhds).mul tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' (hpenalty ν hν) hmargin
    (fun n => hsaddle n ν hν)

omit [Fintype α] [DecidableEq α] in
/-- The KL-style regularization penalty in `MaxLottProp` vanishes when
`τ_n → 0` and the KL values of `π_n` have a finite limit. -/
lemma regularizedPenalty_tendsto_zero
    {τn Kπn : ℕ → ℝ} {Kπ Kν : ℝ}
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hK : Tendsto Kπn atTop (𝓝 Kπ)) :
    Tendsto (fun n => 2 * τn n * (Kπn n - Kν)) atTop (𝓝 (0 : ℝ)) := by
  have htwoτ : Tendsto (fun n => 2 * τn n) atTop (𝓝 (2 * 0)) :=
    tendsto_const_nhds.mul hτ
  have hdiff : Tendsto (fun n => Kπn n - Kν) atTop (𝓝 (Kπ - Kν)) :=
    hK.sub tendsto_const_nhds
  simpa using htwoτ.mul hdiff

omit [DecidableEq α] in
/-- Continuity of one finite KL coordinate, including the boundary point
`x = 0`.  The only analytic input is Mathlib's theorem that
`x ↦ x * log x` is continuous at zero. -/
lemma continuous_klCoordinate (r : ℝ) (hr : r ≠ 0) :
    Continuous (fun x : ℝ => x * Real.log (x / r)) := by
  have hrewrite :
      (fun x : ℝ => x * Real.log (x / r)) =
        fun x : ℝ => x * Real.log x - x * Real.log r := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_div hx hr]
      ring
  rw [hrewrite]
  exact Real.continuous_mul_log.sub (continuous_id.mul continuous_const)

omit [DecidableEq α] in
/-- Full finite-simplex continuity of KL under a full-support reference:
coordinatewise convergence implies convergence of KL even when the limiting
lottery has zero coordinates. -/
lemma KL_tendsto_of_coordinatewise_limit
    {πn : ℕ → α → ℝ} {π ρ : α → ℝ}
    (hπn : ∀ x : α, Tendsto (fun n => πn n x) atTop (𝓝 (π x)))
    (hρ : IsFullSupportLottery ρ) :
    Tendsto (fun n => KL (πn n) ρ) atTop (𝓝 (KL π ρ)) := by
  classical
  unfold KL
  refine tendsto_finset_sum Finset.univ ?_
  intro x hx
  exact ((continuous_klCoordinate (ρ x) (hρ.1 x).ne').continuousAt).tendsto.comp
    (hπn x)

omit [DecidableEq α] in
/-- `MaxLottProp` with the regularization penalty written in the KL-style form
from the appendix proof.  Continuity/boundedness of KL is isolated as the
convergence hypothesis `hKπ`. -/
theorem maximalLottery_of_regularized_saddle_limit_KLstyle
    {M : α → α → ℝ} {π : α → ℝ} {πn : ℕ → α → ℝ}
    {τn Kπn : ℕ → ℝ} {Kπ : ℝ} {Kν : (α → ℝ) → ℝ}
    (hπlot : IsLottery π)
    (hπn : ∀ x : α, Tendsto (fun n => πn n x) atTop (𝓝 (π x)))
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hKπ : Tendsto Kπn atTop (𝓝 Kπ))
    (hsaddle : ∀ n : ℕ, ∀ ν : α → ℝ, IsLottery ν →
      2 * τn n * (Kπn n - Kν ν) ≤ marginValue M (πn n) ν) :
    IsMaximalLottery M π :=
  maximalLottery_of_regularized_saddle_limit_pointwise_penalty
    (penalty := fun ν n => 2 * τn n * (Kπn n - Kν ν))
    hπlot hπn
    (fun _ν _hν => regularizedPenalty_tendsto_zero hτ hKπ)
    hsaddle

omit [DecidableEq α] in
/-- Full version of `MaxLottProp` using the actual finite KL divergence.  The
KL penalty vanishes because finite KL is continuous on the whole simplex when
the reference lottery has full support. -/
theorem maximalLottery_of_regularized_saddle_limit_KL
    {M : α → α → ℝ} {π : α → ℝ} {πn : ℕ → α → ℝ}
    {τn : ℕ → ℝ} {ρ : α → ℝ}
    (hπlot : IsLottery π)
    (hρ : IsFullSupportLottery ρ)
    (hπn : ∀ x : α, Tendsto (fun n => πn n x) atTop (𝓝 (π x)))
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hsaddle : ∀ n : ℕ, ∀ ν : α → ℝ, IsLottery ν →
      2 * τn n * (KL (πn n) ρ - KL ν ρ) ≤ marginValue M (πn n) ν) :
    IsMaximalLottery M π :=
  maximalLottery_of_regularized_saddle_limit_KLstyle
    (Kπn := fun n => KL (πn n) ρ)
    (Kπ := KL π ρ)
    (Kν := fun ν => KL ν ρ)
    hπlot hπn hτ
    (KL_tendsto_of_coordinatewise_limit hπn hρ)
    hsaddle

omit [DecidableEq α] in
/-- Proposition `MaxLottProp`, in the paper-facing form: if `τ_n → 0`, the
regularized NLHF saddle inequality holds for the corresponding lotteries
`π_n`, and `π_n` converges coordinatewise to `π`, then `π` is a maximal
lottery. -/
theorem MaxLottProp
    {M : α → α → ℝ} {π : α → ℝ} {πn : ℕ → α → ℝ}
    {τn : ℕ → ℝ} {ρ : α → ℝ}
    (hπlot : IsLottery π)
    (hρ : IsFullSupportLottery ρ)
    (hπn : ∀ x : α, Tendsto (fun n => πn n x) atTop (𝓝 (π x)))
    (hτ : Tendsto τn atTop (𝓝 (0 : ℝ)))
    (hsaddle : ∀ n : ℕ, ∀ ν : α → ℝ, IsLottery ν →
      2 * τn n * (KL (πn n) ρ - KL ν ρ) ≤ marginValue M (πn n) ν) :
    IsMaximalLottery M π :=
  maximalLottery_of_regularized_saddle_limit_KL hπlot hρ hπn hτ hsaddle

end PaperFormalization
