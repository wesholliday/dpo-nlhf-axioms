import PaperFormalization.NLHFScoreImprovementProfiles

open scoped BigOperators

namespace PaperFormalization

/-! # Finite weak orders are exactly score-representable

The analytic `1/8` proof for Theorem `NLHFmono` is carried out for weak
orders represented by real-valued scores.  The paper, however, quantifies
over arbitrary finite complete and transitive Boolean relations.  This file
provides the exact representation needed to connect those formulations.

For a finite weak order `R`, assign to `a` the cardinality of its weak lower
contour set `{z | R a z}`.  Transitivity makes these contour sets nested
along `R`.  If `R a b` fails, completeness gives `R b a`, and reflexivity
puts `b` in the lower contour set of `b` but not that of `a`; hence the
cardinality inequality is strict.  Consequently

`R a b ↔ score b ≤ score a`.

The construction is voterwise, preserves the profile and its normalized
margin exactly, and therefore transports the existing score-profile
chaining theorem to the paper's native relation-valued profiles. -/

/-- Every voter submits a weak order in the paper's sense: a reflexive,
complete, and transitive Boolean relation.  `IsCompleteProfile` only states
completeness on distinct candidates; reflexivity supplies the diagonal. -/
def IsWeakOrderProfile {V α : Type*}
    (R : V → α → α → Bool) : Prop :=
  IsReflexiveProfile R ∧ IsCompleteProfile R ∧ IsTransitiveProfile R

/-- Every voter relation is antisymmetric. -/
def IsAntisymmetricProfile {V α : Type*}
    (R : V → α → α → Bool) : Prop :=
  ∀ i a b, R i a b = true → R i b a = true → a = b

/-- A paper-style linear-order profile is a weak-order profile whose voter
relations are antisymmetric. -/
def IsLinearOrderProfile {V α : Type*}
    (R : V → α → α → Bool) : Prop :=
  IsWeakOrderProfile R ∧ IsAntisymmetricProfile R

/-- The canonical real score of a candidate is the cardinality of its weak
lower contour set. -/
noncomputable def weakOrderScoreProfile
    {V α : Type*} [Fintype α]
    (R : V → α → α → Bool) (i : V) (a : α) : ℝ :=
  ((Finset.univ.filter (fun z : α => R i a z = true)).card : ℝ)

lemma weakOrderScoreProfile_le_of_rel
    {V α : Type*} [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsWeakOrderProfile R)
    (i : V) {a b : α} (hab : R i a b = true) :
    weakOrderScoreProfile R i b ≤ weakOrderScoreProfile R i a := by
  unfold weakOrderScoreProfile
  exact_mod_cast Finset.card_le_card (by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hR.2.2 i a b z hab hz)

lemma rel_of_weakOrderScoreProfile_le
    {V α : Type*} [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsWeakOrderProfile R)
    (i : V) {a b : α}
    (hscore :
      weakOrderScoreProfile R i b ≤ weakOrderScoreProfile R i a) :
    R i a b = true := by
  by_contra hnot
  have hab_ne : a ≠ b := by
    intro hab
    subst b
    exact hnot (hR.1 i a)
  have hba : R i b a = true := by
    rcases hR.2.1 i a b hab_ne with hab | hba
    · exact (hnot hab).elim
    · exact hba
  let Sa : Finset α := Finset.univ.filter (fun z : α => R i a z = true)
  let Sb : Finset α := Finset.univ.filter (fun z : α => R i b z = true)
  have hsub : Sa ⊆ Sb := by
    intro z hz
    simp only [Sa, Sb, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hR.2.2 i b a z hba hz
  have hbSb : b ∈ Sb := by
    simp only [Sb, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hR.1 i b
  have hbSa : b ∉ Sa := by
    simp only [Sa, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnot
  have hne : Sa ≠ Sb := by
    intro heq
    apply hbSa
    rw [heq]
    exact hbSb
  have hcard : Sa.card < Sb.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hlt :
      weakOrderScoreProfile R i a < weakOrderScoreProfile R i b := by
    change (Sa.card : ℝ) < (Sb.card : ℝ)
    exact_mod_cast hcard
  exact (not_lt_of_ge hscore) hlt

/-- The canonical score represents the original weak relation exactly. -/
theorem weakOrderScoreProfile_rel_iff
    {V α : Type*} [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsWeakOrderProfile R)
    (i : V) (a b : α) :
    R i a b = true ↔
      weakOrderScoreProfile R i b ≤ weakOrderScoreProfile R i a :=
  ⟨weakOrderScoreProfile_le_of_rel hR i,
    rel_of_weakOrderScoreProfile_le hR i⟩

/-- Exact profile-level score representation of every finite weak order. -/
theorem scoreWeakProfile_weakOrderScoreProfile
    {V α : Type*} [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsWeakOrderProfile R) :
    scoreWeakProfile (weakOrderScoreProfile R) = R := by
  funext i a b
  apply Bool.eq_iff_iff.mpr
  simp only [scoreWeakProfile, decide_eq_true_eq]
  exact (weakOrderScoreProfile_rel_iff hR i a b).symm

/-- Exact representation also transports the paper's voterwise improvement
relation in both directions. -/
theorem weakOrderScoreProfile_improvement_iff
    {V α : Type*} [Fintype α] [DecidableEq α]
    {R R' : V → α → α → Bool}
    (hR : IsWeakOrderProfile R) (hR' : IsWeakOrderProfile R') (x : α) :
    IsWeakProfileImprovement
        (scoreWeakProfile (weakOrderScoreProfile R))
        (scoreWeakProfile (weakOrderScoreProfile R')) x ↔
      IsWeakProfileImprovement R R' x := by
  rw [scoreWeakProfile_weakOrderScoreProfile hR,
    scoreWeakProfile_weakOrderScoreProfile hR']

/-- Every real score profile induces a paper-style weak-order profile. -/
theorem isWeakOrderProfile_scoreWeakProfile
    {V α : Type*} (score : V → α → ℝ) :
    IsWeakOrderProfile (scoreWeakProfile score) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i a
    simp [scoreWeakProfile]
  · intro i a b _hab
    simp only [scoreWeakProfile, decide_eq_true_eq]
    exact le_total (score i b) (score i a)
  · intro i a b c hab hbc
    simp only [scoreWeakProfile, decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hbc hab

/-- A tie-free real score profile induces a paper-style linear-order
profile. -/
theorem isLinearOrderProfile_scoreWeakProfile
    {V α : Type*} {score : V → α → ℝ}
    (hscore : IsLinearScoreProfile score) :
    IsLinearOrderProfile (scoreWeakProfile score) := by
  refine ⟨isWeakOrderProfile_scoreWeakProfile score, ?_⟩
  intro i a b hab hba
  simp only [scoreWeakProfile, decide_eq_true_eq] at hab hba
  exact hscore i (le_antisymm hba hab)

/-- Antisymmetry makes the canonical representing score tie-free. -/
theorem weakOrderScoreProfile_linear
    {V α : Type*} [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R) :
    IsLinearScoreProfile (weakOrderScoreProfile R) := by
  intro i a b hab
  apply hR.2 i a b
  · apply rel_of_weakOrderScoreProfile_le hR.1 i
    exact le_of_eq hab.symm
  · apply rel_of_weakOrderScoreProfile_le hR.1 i
    exact le_of_eq hab

/-! ## Exact margin transport -/

/-- The score margin is the normalized strict-part margin of the Boolean
weak relation induced by that score. -/
theorem scoreProfileMargin_eq_normalizedStrictMargin_scoreWeakProfile
    {V α : Type*} [Fintype V]
    (score : V → α → ℝ) :
    scoreProfileMargin score =
      normalizedStrictMargin (strictPart (scoreWeakProfile score)) := by
  funext a b
  unfold scoreProfileMargin normalizedStrictMargin strictMargin strictCount
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  unfold scoreMarginSign strictPart strictPrefRel scoreWeakProfile prefIndicator
  rcases lt_trichotomy (score i a) (score i b) with hab | hab | hba
  · rw [scoreMarginSignReal_of_lt hab]
    have hab_le : score i a ≤ score i b := hab.le
    have hnot : ¬ score i b ≤ score i a := not_le.mpr hab
    simp [hab_le, hnot]
  · rw [scoreMarginSignReal_of_eq hab]
    have hab_le : score i a ≤ score i b := le_of_eq hab
    have hba_le : score i b ≤ score i a := le_of_eq hab.symm
    simp [hab_le, hba_le]
  · rw [scoreMarginSignReal_of_gt hba]
    have hba_le : score i b ≤ score i a := hba.le
    have hnot : ¬ score i a ≤ score i b := not_le.mpr hba
    simp [hba_le, hnot]

/-- On a paper-style weak-order profile, the paper's pair-normalized margin
is exactly the score margin of the canonical representation. -/
theorem paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsWeakOrderProfile R) :
    paperNormalizedMargin R =
      scoreProfileMargin (weakOrderScoreProfile R) := by
  rw [paperNormalizedMargin_eq_normalizedStrictMargin_strictPart_of_complete
    hR.2.1]
  rw [scoreProfileMargin_eq_normalizedStrictMargin_scoreWeakProfile]
  rw [scoreWeakProfile_weakOrderScoreProfile hR]

/-- Relation-valued form of the appendix lemma `swo-bound`: the tighter
coordinate bound holds for every arbitrary finite paper-style weak-order
profile, not only for one supplied together with scores. -/
theorem paperNormalizedMargin_coordinate_abs_le_one_of_weakOrderProfile
    {V α : Type*} [Fintype V] [Nonempty V]
    [Fintype α] [DecidableEq α]
    {R : V → α → α → Bool} (hR : IsWeakOrderProfile R)
    (x i j : α) :
    |paperNormalizedMargin R i j +
      paperNormalizedMargin R x i -
      paperNormalizedMargin R x j| ≤ (1 : ℝ) := by
  rw [paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile hR]
  exact scoreProfileMargin_coordinate_abs_le_one
    (weakOrderScoreProfile R) x i j

/-- The paper's pair-normalized margin of a score-induced weak relation is
the original score-profile margin. -/
theorem paperNormalizedMargin_scoreWeakProfile_eq_scoreProfileMargin
    {V α : Type*} [Fintype V] [Fintype α] [DecidableEq α]
    (score : V → α → ℝ) :
    paperNormalizedMargin (scoreWeakProfile score) =
      scoreProfileMargin score := by
  rw [paperNormalizedMargin_eq_normalizedStrictMargin_strictPart_of_complete
    (isWeakOrderProfile_scoreWeakProfile score).2.1]
  exact
    (scoreProfileMargin_eq_normalizedStrictMargin_scoreWeakProfile score).symm

/-! ## Paper-native `1/8` NLHF monotonicity -/

/-- Selected-NLHF monotonicity on arbitrary finite weak-order profiles,
stated directly with the paper's Boolean relations, pair-normalized margins,
and improvement conditions (i)–(iii). -/
def SelectedNLHFPaperWeakOrderImprovementMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype α] [DecidableEq α],
    ∀ (R R' : V → α → α → Bool) (ρ : α → ℝ) (x : α),
      IsWeakOrderProfile R →
        IsWeakOrderProfile R' →
          IsFullSupportLottery ρ →
            IsWeakProfileImprovement R R' x →
              selectedNLHF (α := α) τ (paperNormalizedMargin R) ρ x ≤
                selectedNLHF (α := α) τ (paperNormalizedMargin R') ρ x

/-- Linear-order specialization of the paper-native profile predicate. -/
def SelectedNLHFPaperLinearOrderImprovementMonotonicity (τ : ℝ) : Prop :=
  ∀ {V α : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype α] [DecidableEq α],
    ∀ (R R' : V → α → α → Bool) (ρ : α → ℝ) (x : α),
      IsLinearOrderProfile R →
        IsLinearOrderProfile R' →
          IsFullSupportLottery ρ →
            IsWeakProfileImprovement R R' x →
              selectedNLHF (α := α) τ (paperNormalizedMargin R) ρ x ≤
                selectedNLHF (α := α) τ (paperNormalizedMargin R') ρ x

/-- A score-profile monotonicity theorem transports to arbitrary paper-style
weak-order relations through the canonical exact representation. -/
theorem SelectedNLHFWeakOrderImprovementMonotonicity.toPaperWeakOrder
    {τ : ℝ} (hscore : SelectedNLHFWeakOrderImprovementMonotonicity τ) :
    SelectedNLHFPaperWeakOrderImprovementMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _decidableV _fintypeα _decidableα
    R R' ρ x hR hR' hρ himp
  have hscoreImp :
      IsWeakProfileImprovement
        (scoreWeakProfile (weakOrderScoreProfile R))
        (scoreWeakProfile (weakOrderScoreProfile R')) x := by
    exact (weakOrderScoreProfile_improvement_iff hR hR' x).mpr himp
  have hmono := hscore
    (weakOrderScoreProfile R) (weakOrderScoreProfile R') ρ x hρ hscoreImp
  rw [← paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile hR,
    ← paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile hR']
    at hmono
  exact hmono

/-- The existing score-profile chaining theorem transported to arbitrary
paper-style weak-order relations. -/
theorem selectedNLHF_paperWeakOrderImprovementMonotone_of_tau_ge_one_eighth
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFPaperWeakOrderImprovementMonotonicity τ :=
  SelectedNLHFWeakOrderImprovementMonotonicity.toPaperWeakOrder
    (selectedNLHF_weakOrderImprovementMonotone_of_tau_ge_one_eighth hτge)

/-- Paper-style linear orders are a subclass of paper-style weak orders. -/
theorem
    SelectedNLHFPaperWeakOrderImprovementMonotonicity.toPaperLinearOrder
    {τ : ℝ} (hweak : SelectedNLHFPaperWeakOrderImprovementMonotonicity τ) :
    SelectedNLHFPaperLinearOrderImprovementMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _decidableV _fintypeα _decidableα
    R R' ρ x hR hR' hρ himp
  exact hweak R R' ρ x hR.1 hR'.1 hρ himp

theorem selectedNLHF_paperLinearOrderImprovementMonotone_of_tau_ge_one_eighth
    {τ : ℝ} (hτge : (1 : ℝ) / 8 ≤ τ) :
    SelectedNLHFPaperLinearOrderImprovementMonotonicity τ :=
  SelectedNLHFPaperWeakOrderImprovementMonotonicity.toPaperLinearOrder
    (selectedNLHF_paperWeakOrderImprovementMonotone_of_tau_ge_one_eighth hτge)

/-- Any monotonicity theorem over arbitrary paper-style weak orders applies
in particular to score-induced weak orders.  This implication transports the
existing finite low-temperature witness to the paper-native predicate. -/
theorem
    SelectedNLHFPaperWeakOrderImprovementMonotonicity.toScoreWeakOrder
    {τ : ℝ} (hpaper :
      SelectedNLHFPaperWeakOrderImprovementMonotonicity τ) :
    SelectedNLHFWeakOrderImprovementMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _decidableV _fintypeα _decidableα
    score score' ρ x hρ himp
  have hmono := hpaper
    (scoreWeakProfile score) (scoreWeakProfile score') ρ x
    (isWeakOrderProfile_scoreWeakProfile score)
    (isWeakOrderProfile_scoreWeakProfile score') hρ himp
  simpa only [
    paperNormalizedMargin_scoreWeakProfile_eq_scoreProfileMargin] using hmono

/-- The analogous specialization for tie-free scores and paper-style linear
orders. -/
theorem
    SelectedNLHFPaperLinearOrderImprovementMonotonicity.toScoreLinearOrder
    {τ : ℝ} (hpaper :
      SelectedNLHFPaperLinearOrderImprovementMonotonicity τ) :
    SelectedNLHFLinearOrderImprovementMonotonicity τ := by
  intro V α _fintypeV _nonemptyV _decidableV _fintypeα _decidableα
    score score' ρ x hscore hscore' hρ himp
  have hmono := hpaper
    (scoreWeakProfile score) (scoreWeakProfile score') ρ x
    (isLinearOrderProfile_scoreWeakProfile hscore)
    (isLinearOrderProfile_scoreWeakProfile hscore') hρ himp
  simpa only [
    paperNormalizedMargin_scoreWeakProfile_eq_scoreProfileMargin] using hmono

/-- Exact equivalence between the internal score-profile predicate and the
paper-native arbitrary weak-order predicate, at every temperature. -/
theorem selectedNLHFPaperWeakOrderImprovementMonotonicity_iff_score
    {τ : ℝ} :
    SelectedNLHFPaperWeakOrderImprovementMonotonicity τ ↔
      SelectedNLHFWeakOrderImprovementMonotonicity τ :=
  ⟨fun h => h.toScoreWeakOrder, fun h => h.toPaperWeakOrder⟩

/-- Exact equivalence between the internal tie-free score predicate and the
paper-native arbitrary linear-order predicate, at every temperature. -/
theorem selectedNLHFPaperLinearOrderImprovementMonotonicity_iff_score
    {τ : ℝ} :
    SelectedNLHFPaperLinearOrderImprovementMonotonicity τ ↔
      SelectedNLHFLinearOrderImprovementMonotonicity τ := by
  constructor
  · exact fun h => h.toScoreLinearOrder
  · intro hscore V α _fintypeV _nonemptyV _decidableV _fintypeα _decidableα
      R R' ρ x hR hR' hρ himp
    have hmono := hscore
      (weakOrderScoreProfile R) (weakOrderScoreProfile R') ρ x
      (weakOrderScoreProfile_linear hR)
      (weakOrderScoreProfile_linear hR') hρ
      ((weakOrderScoreProfile_improvement_iff hR.1 hR'.1 x).mpr himp)
    rw [← paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile
        hR.1,
      ← paperNormalizedMargin_eq_scoreProfileMargin_weakOrderScoreProfile
        hR'.1] at hmono
    exact hmono

/-- Exact paper-native weak-order `1/8` clause of Theorem `NLHFmono`,
including the converse below the threshold. -/
theorem NLHFmono_paper_weak_order_improvements
    {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFPaperWeakOrderImprovementMonotonicity τ ↔
      (1 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    exact (NLHFmono_weak_order_improvements hτ).mp hmono.toScoreWeakOrder
  · exact selectedNLHF_paperWeakOrderImprovementMonotone_of_tau_ge_one_eighth

/-- Exact paper-native linear-order `1/8` clause of Theorem `NLHFmono`,
including the converse below the threshold. -/
theorem NLHFmono_paper_linear_order_improvements
    {τ : ℝ} (hτ : 0 < τ) :
    SelectedNLHFPaperLinearOrderImprovementMonotonicity τ ↔
      (1 : ℝ) / 8 ≤ τ := by
  constructor
  · intro hmono
    exact (NLHFmono_linear_order_improvements hτ).mp hmono.toScoreLinearOrder
  · exact selectedNLHF_paperLinearOrderImprovementMonotone_of_tau_ge_one_eighth

end PaperFormalization
