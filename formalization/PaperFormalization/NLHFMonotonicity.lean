import PaperFormalization.Axioms

namespace PaperFormalization

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The assembly step for theorem `NLHFmono`: a large-temperature proof and a
low-temperature counterexample family combine into the sharp iff statement. -/
theorem NLHFmono_from_threshold_parts
    (NLHF : ℝ → MatrixRule α)
    (hlarge :
      ∀ τ : ℝ, (3 : ℝ) / 8 ≤ τ →
        SatisfiesProbabilisticMonotonicity (NLHF τ))
    (hlow :
      ∀ τ : ℝ, 0 < τ → τ < (3 : ℝ) / 8 →
        ViolatesProbabilisticMonotonicity (NLHF τ))
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity (NLHF τ) ↔
      (3 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    by_contra hnot
    have hlt : τ < (3 : ℝ) / 8 := lt_of_not_ge hnot
    exact (hlow τ hτ hlt) hmono
  · intro hge
    exact hlarge τ hge

/-- The formal target of the response-inequality part of the proof notes. -/
def NLHFMonotoneForLargeTau
    (NLHF : ℝ → MatrixRule α) : Prop :=
  ∀ τ : ℝ, (3 : ℝ) / 8 ≤ τ →
    SatisfiesProbabilisticMonotonicity (NLHF τ)

/-- The formal target of the three-candidate construction in the proof notes. -/
def NLHFViolatesForSmallTau
    (NLHF : ℝ → MatrixRule α) : Prop :=
  ∀ τ : ℝ, 0 < τ → τ < (3 : ℝ) / 8 →
    ViolatesProbabilisticMonotonicity (NLHF τ)

omit [DecidableEq α] in
theorem NLHFmono_from_named_parts
    (NLHF : ℝ → MatrixRule α)
    (hlarge : NLHFMonotoneForLargeTau NLHF)
    (hlow : NLHFViolatesForSmallTau NLHF)
    {τ : ℝ} (hτ : 0 < τ) :
    SatisfiesProbabilisticMonotonicity (NLHF τ) ↔
      (3 : ℝ) / 8 ≤ τ :=
  NLHFmono_from_threshold_parts NLHF hlarge hlow hτ

end PaperFormalization
