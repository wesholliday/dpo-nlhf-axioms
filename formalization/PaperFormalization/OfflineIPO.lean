import PaperFormalization.BordaIPO
import PaperFormalization.WeakOrderScoreRepresentation

open scoped BigOperators

namespace PaperFormalization

/-! # Offline IPO on linear-order profiles

This follows the second proposition of Appendix `IPOApp`: establish the
three preference/Borda identities, expand the two quadratic objectives,
cancel their mixed terms, and apply `BIPOandPB`. In particular, the proof
does not replace the author's argument with an optimization theorem.
-/

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Sum over all ordered pairs of distinct candidates. -/
noncomputable def ipoPairSum (f : α → α → ℝ) : ℝ :=
  ∑ x : α, ∑ y ∈ Finset.univ.erase x, f x y

omit [Nonempty α] in
lemma ipoPairSum_swap (f : α → α → ℝ) :
    ipoPairSum (fun x y => f y x) = ipoPairSum f := by
  unfold ipoPairSum
  rw [sum_univ_erase_eq_sum_offDiag, sum_univ_erase_eq_sum_offDiag]
  exact sum_offDiag_swap f

omit [Nonempty α] in
lemma ipoPairSum_sub (f g : α → α → ℝ) :
    ipoPairSum (fun x y => f x y - g x y) = ipoPairSum f - ipoPairSum g := by
  simp [ipoPairSum, Finset.sum_sub_distrib]

omit [Nonempty α] in
lemma ipoPairSum_add (f g : α → α → ℝ) :
    ipoPairSum (fun x y => f x y + g x y) = ipoPairSum f + ipoPairSum g := by
  simp [ipoPairSum, Finset.sum_add_distrib]

omit [Nonempty α] in
/-- Explicitly collect the coefficient of each log coordinate, by swapping
the two indices in the terms involving the second coordinate. -/
lemma ipoPairSum_difference_mul (l : α → ℝ) (q : α → α → ℝ) :
    ipoPairSum (fun x y => (l x - l y) * q x y) =
      ∑ x : α, l x * ∑ y ∈ Finset.univ.erase x, (q x y - q y x) := by
  calc
    _ = ipoPairSum (fun x y => l x * q x y) -
        ipoPairSum (fun x y => l y * q x y) := by
      simp [ipoPairSum, sub_mul, Finset.sum_sub_distrib]
    _ = ipoPairSum (fun x y => l x * q x y) -
        ipoPairSum (fun x y => l x * q y x) := by
      rw [ipoPairSum_swap (fun x y => l x * q y x)]
    _ = _ := by
      simp [ipoPairSum, Finset.sum_sub_distrib, Finset.mul_sum, mul_sub]

/-- A quadratic log-ratio loss with a supplied pairwise target. -/
noncomputable def pairwiseIPOLoss (t : α → α → ℝ) (ρ π : α → ℝ) : ℝ :=
  ipoPairSum (fun x y => (Real.log (π x / ρ x) - Real.log (π y / ρ y) - t x y) ^ 2)

omit [Nonempty α] in
/-- Expansion of the squares: equal antisymmetric row sums of the targets
make the difference of the two losses independent of the lottery. -/
lemma pairwiseIPOLoss_sub_eq_constant (a b : α → α → ℝ) (ρ π : α → ℝ)
    (hbalance : ∀ x : α, ∑ y ∈ Finset.univ.erase x,
      ((b x y - a x y) - (b y x - a y x)) = 0) :
    pairwiseIPOLoss a ρ π - pairwiseIPOLoss b ρ π =
      ipoPairSum (fun x y => (a x y) ^ 2 - (b x y) ^ 2) := by
  have hexpand : pairwiseIPOLoss a ρ π - pairwiseIPOLoss b ρ π =
      ipoPairSum (fun x y => (a x y) ^ 2 - (b x y) ^ 2) +
        2 * ipoPairSum (fun x y =>
          (Real.log (π x / ρ x) - Real.log (π y / ρ y)) * (b x y - a x y)) := by
    calc
      _ = ipoPairSum (fun x y =>
          (Real.log (π x / ρ x) - Real.log (π y / ρ y) - a x y) ^ 2 -
          (Real.log (π x / ρ x) - Real.log (π y / ρ y) - b x y) ^ 2) := by
        exact (ipoPairSum_sub _ _).symm
      _ = ipoPairSum (fun x y => ((a x y) ^ 2 - (b x y) ^ 2) +
          2 * ((Real.log (π x / ρ x) - Real.log (π y / ρ y)) * (b x y - a x y))) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by simp [ipoPairSum, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hexpand, ipoPairSum_difference_mul]
  simp [hbalance]

omit [DecidableEq α] [Nonempty α] in
lemma fullSupportArgminSet_eq_of_sub_eq_const
    (L₁ L₂ : (α → ℝ) → ℝ) (C : ℝ)
    (h : ∀ π : α → ℝ, L₁ π - L₂ π = C) :
    fullSupportArgminSet L₁ = fullSupportArgminSet L₂ := by
  ext π
  constructor
  · rintro ⟨hπ, hm⟩
    refine ⟨hπ, fun q hq => ?_⟩
    have := hm q hq
    linarith [h π, h q]
  · rintro ⟨hπ, hm⟩
    refine ⟨hπ, fun q hq => ?_⟩
    have := hm q hq
    linarith [h π, h q]

section Profiles

variable {V : Type*} [Fintype V]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma indiffCount_eq_zero_of_linearOrderProfile
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {x y : α} (hxy : x ≠ y) : indiffCount R x y = 0 := by
  unfold indiffCount
  apply Finset.sum_eq_zero
  intro i _
  have hnot : ¬ (R i x y = true ∧ R i y x = true) :=
    fun h => hxy (hR.2 i x y h.1 h.2)
  cases ha : R i x y <;> cases hb : R i y x <;>
    simp_all [prefIndicator, indiffRel]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma noCompCount_eq_zero_of_completeProfile
    {R : V → α → α → Bool} (hR : IsCompleteProfile R)
    {x y : α} (hxy : x ≠ y) : noCompCount R x y = 0 := by
  unfold noCompCount
  apply Finset.sum_eq_zero
  intro i _
  rcases hR i x y hxy with h | h <;> simp [prefIndicator, noCompRel, h]

omit [Nonempty α] in
/-- On linear orders, the paper's partial-Borda score is the row sum of
strict preference counts; no missing or indifferent comparisons remain. -/
lemma partialBordaScoreP_eq_sum_strictPrefCount_of_linearOrderProfile
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R) (x : α) :
    partialBordaScoreP R x = ∑ y ∈ Finset.univ.erase x, strictPrefCount R x y := by
  rw [partialBordaScoreP_eq_counts]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hxy : x ≠ y := Ne.symm (Finset.mem_erase.mp hy).1
  rw [indiffCount_eq_zero_of_linearOrderProfile hR hxy,
    noCompCount_eq_zero_of_completeProfile hR.1.2.1 hxy]
  ring

omit [Nonempty α] in
/-- The paper's partial-Borda score has the familiar total. With half
credit for missing comparisons, this holds even before imposing linearity. -/
lemma sum_partialBordaScoreP (R : V → α → α → Bool) :
    (∑ x : α, partialBordaScoreP R x) =
      (Fintype.card V : ℝ) * (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) / 2 := by
  have hmargin : ipoPairSum (fun x y => strictPrefCount R x y - strictPrefCount R y x) = 0 := by
    rw [ipoPairSum_sub, ipoPairSum_swap]
    ring
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset α)) rfl
    (fun x _ => two_mul_partialBordaScoreP R x)
  change (∑ x : α, 2 * partialBordaScoreP R x) =
    ∑ x : α, ((∑ y ∈ Finset.univ.erase x,
      (strictPrefCount R x y - strictPrefCount R y x)) +
      ((Fintype.card α : ℝ) - 1) * (Fintype.card V : ℝ)) at hs
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  change 2 * (∑ x : α, partialBordaScoreP R x) =
    ipoPairSum (fun x y => strictPrefCount R x y - strictPrefCount R y x) + _ at hs
  rw [hmargin] at hs
  simp only [zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith

omit [Nonempty α] in
lemma paperNormalizedCbar_add_reverse (R : V → α → α → Bool) (x y : α) :
    paperNormalizedCbar R x y + paperNormalizedCbar R y x = 1 := by
  have hxy := paperNormalizedMargin_eq_two_mul_paperNormalizedCbar_sub_one R x y
  have hyx := paperNormalizedMargin_eq_two_mul_paperNormalizedCbar_sub_one R y x
  have hskew := (paperNormalizedMargin_isNormalizedMarginMatrix R).2.1 x y
  linarith

omit [Fintype α] [DecidableEq α] [Nonempty α] in
lemma paperNormalizedCbar_eq_strictPrefCount_div_card [Nonempty V]
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {x y : α} (hxy : x ≠ y) :
    paperNormalizedCbar R x y = strictPrefCount R x y / (Fintype.card V : ℝ) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold paperNormalizedCbar
  rw [comparedCount_eq_card_of_complete hR.1.2.1 hxy, if_neg hn,
    indiffCount_eq_zero_of_linearOrderProfile hR hxy]
  simp

omit [Nonempty α] in
lemma sum_paperNormalizedCbar_eq_partialBordaScoreP_div_card [Nonempty V]
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R) (x : α) :
    (∑ y ∈ Finset.univ.erase x, paperNormalizedCbar R x y) =
      partialBordaScoreP R x / (Fintype.card V : ℝ) := by
  calc
    _ = ∑ y ∈ Finset.univ.erase x, strictPrefCount R x y / (Fintype.card V : ℝ) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      exact paperNormalizedCbar_eq_strictPrefCount_div_card hR
        (Ne.symm (Finset.mem_erase.mp hy).1)
    _ = _ := by
      rw [← Finset.sum_div, ← partialBordaScoreP_eq_sum_strictPrefCount_of_linearOrderProfile hR x]

/-- The objective `IPO_τ(R,ρ)(π)` in Remark `IPOremark`, using the actual
paper-normalized preference frequencies and ordered distinct pairs. -/
noncomputable def offlineIPOObjective (τ : ℝ)
    (R : V → α → α → Bool) (ρ π : α → ℝ) : ℝ :=
  pairwiseIPOLoss (fun x y => paperNormalizedCbar R x y / τ) ρ π

/-- The three identities cited in the English proof make every log-ratio
coefficient in the difference of the losses zero. -/
lemma offlineIPO_target_balance [Nonempty V]
    {τ η : ℝ} (hτ : 0 < τ)
    (hη : η = 1 / (τ * (Fintype.card α : ℝ) * (Fintype.card V : ℝ)))
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R) (x : α) :
    (∑ y ∈ Finset.univ.erase x,
      ((η * (partialBordaScoreP R x - partialBordaScoreP R y) -
          paperNormalizedCbar R x y / τ) -
        (η * (partialBordaScoreP R y - partialBordaScoreP R x) -
          paperNormalizedCbar R y x / τ))) = 0 := by
  have hcard : ((Finset.univ.erase x : Finset α).card : ℝ) =
      (Fintype.card α : ℝ) - 1 := by
    rw [Finset.cast_card_erase_of_mem (R := ℝ) (by simp)]
    simp
  have hB : (∑ y ∈ Finset.univ.erase x,
      (partialBordaScoreP R x - partialBordaScoreP R y)) =
      (Fintype.card α : ℝ) * partialBordaScoreP R x -
        ∑ z : α, partialBordaScoreP R z := by
    have hsplit := Finset.add_sum_erase (s := Finset.univ)
      (f := partialBordaScoreP R) (by simp : x ∈ (Finset.univ : Finset α))
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    nlinarith
  have hc : (∑ y ∈ Finset.univ.erase x,
      (paperNormalizedCbar R x y - paperNormalizedCbar R y x)) =
      2 * (partialBordaScoreP R x / (Fintype.card V : ℝ)) -
        ((Fintype.card α : ℝ) - 1) := by
    calc
      _ = ∑ y ∈ Finset.univ.erase x, (2 * paperNormalizedCbar R x y - 1) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have h := paperNormalizedCbar_add_reverse R x y
        linarith
      _ = 2 * (∑ y ∈ Finset.univ.erase x, paperNormalizedCbar R x y) -
          ((Finset.univ.erase x : Finset α).card : ℝ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp
      _ = _ := by rw [sum_paperNormalizedCbar_eq_partialBordaScoreP_div_card hR x, hcard]
  calc
    _ = ∑ y ∈ Finset.univ.erase x,
        (2 * η * (partialBordaScoreP R x - partialBordaScoreP R y) -
          (paperNormalizedCbar R x y - paperNormalizedCbar R y x) / τ) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    _ = 2 * η * ((Fintype.card α : ℝ) * partialBordaScoreP R x -
          ∑ z : α, partialBordaScoreP R z) -
        (2 * (partialBordaScoreP R x / (Fintype.card V : ℝ)) -
          ((Fintype.card α : ℝ) - 1)) / τ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div, hB, hc]
    _ = 0 := by
      rw [sum_partialBordaScoreP, hη]
      have hm : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp [ne_of_gt hτ, hm, hn]
      ring

/-- Exactly the constant-difference identity displayed in the English
offline-IPO proof. It is proved by expansion, not assumed as a hypothesis. -/
theorem offlineIPOObjective_sub_bordaIPOObjective [Nonempty V]
    {τ η : ℝ} (hτ : 0 < τ)
    (hη : η = 1 / (τ * (Fintype.card α : ℝ) * (Fintype.card V : ℝ)))
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R) (ρ π : α → ℝ) :
    offlineIPOObjective τ R ρ π - bordaIPOObjective η R ρ π =
      ipoPairSum (fun x y => (paperNormalizedCbar R x y) ^ 2 / τ ^ 2 -
        η ^ 2 * (partialBordaScoreP R x - partialBordaScoreP R y) ^ 2) := by
  change pairwiseIPOLoss (fun x y => paperNormalizedCbar R x y / τ) ρ π -
      pairwiseIPOLoss (fun x y => η * (partialBordaScoreP R x - partialBordaScoreP R y)) ρ π = _
  rw [pairwiseIPOLoss_sub_eq_constant _ _ _ _ (offlineIPO_target_balance hτ hη hR)]
  simp only [div_pow, mul_pow]

/-- The second proposition of Appendix `IPOApp`, on the paper's native
reflexive linear-order profiles and its actual normalized frequencies. -/
theorem offlineIPOObjective_argmin [Nonempty V]
    {τ : ℝ} (hτ : 0 < τ)
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (offlineIPOObjective τ R ρ) =
      ({proportionalBorda
        (1 / (τ * (Fintype.card α : ℝ) * (Fintype.card V : ℝ)))
        ρ (partialBordaScoreP R)} : Set (α → ℝ)) := by
  let η : ℝ := 1 / (τ * (Fintype.card α : ℝ) * (Fintype.card V : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hsame := fullSupportArgminSet_eq_of_sub_eq_const
    (offlineIPOObjective τ R ρ) (bordaIPOObjective η R ρ)
    (ipoPairSum (fun x y => (paperNormalizedCbar R x y) ^ 2 / τ ^ 2 -
      η ^ 2 * (partialBordaScoreP R x - partialBordaScoreP R y) ^ 2))
    (fun π => offlineIPOObjective_sub_bordaIPOObjective hτ rfl hR ρ π)
  rw [hsame]
  exact (bordaIPOObjective_argmin_and_zero hη R hρ).1

/-! ### Population offline IPO (first paragraph of Appendix `IPOApp`)

The paper writes the population IPO loss of Azar et al. (2024, §5.2,
Eq. (16)) in its own notation as

  `E[ ( log (π(x)ρ(y) / (π(y)ρ(x))) - I(x,y)/τ )^2 ]`,

where `(x,y)` is a uniformly drawn ordered pair of distinct completions and
`I(x,y)` is `1` if a uniformly drawn annotator prefers `x` to `y` and `0`
otherwise.  Over a finite profile the expectation is a finite average, so we
define it as such: the inner average is over the annotators `V`, the outer
one over the `m(m-1)` ordered pairs.  The English argument is then followed
literally: the expected squared error against a random label is the squared
error against its mean plus a variance term (`avg_sq_sub_eq`), the label's
mean is `c̄_{x,y}(𝐑)` on linear-order profiles, the log of the fraction is the
difference of log-ratios (`log_ratio_div_eq_sub`), and averaging over pairs
gives `IPO_τ/(m(m-1))` plus a constant, hence the same minimizers.
-/

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The displayed log of a fraction equals the difference of log-ratios on
positive lotteries. -/
lemma log_ratio_div_eq_sub {π ρ : α → ℝ}
    (hπ : ∀ z, 0 < π z) (hρ : ∀ z, 0 < ρ z) (x y : α) :
    Real.log (π x * ρ y / (π y * ρ x)) =
      Real.log (π x / ρ x) - Real.log (π y / ρ y) := by
  rw [Real.log_div (mul_pos (hπ x) (hρ y)).ne' (mul_pos (hπ y) (hρ x)).ne',
    Real.log_mul (hπ x).ne' (hρ y).ne', Real.log_mul (hπ y).ne' (hρ x).ne',
    Real.log_div (hπ x).ne' (hρ x).ne', Real.log_div (hπ y).ne' (hρ y).ne']
  ring

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The bias--variance decomposition for a finite average: the mean squared
deviation from `a` is the squared deviation of `a` from the mean plus the
mean squared deviation from the mean. -/
lemma avg_sq_sub_eq [Nonempty V] (a : ℝ) (b : V → ℝ) :
    (∑ i : V, (a - b i) ^ 2) / (Fintype.card V : ℝ) =
      (a - (∑ j : V, b j) / (Fintype.card V : ℝ)) ^ 2 +
        (∑ i : V, ((∑ j : V, b j) / (Fintype.card V : ℝ) - b i) ^ 2) /
          (Fintype.card V : ℝ) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hμ : (Fintype.card V : ℝ) * ((∑ j : V, b j) / (Fintype.card V : ℝ)) =
      ∑ j : V, b j := by
    first | (field_simp; ring) | field_simp
  have hzero : ∑ i : V, ((∑ j : V, b j) / (Fintype.card V : ℝ) - b i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hμ,
      sub_self]
  have hexp : ∑ i : V, (a - b i) ^ 2 =
      (Fintype.card V : ℝ) * (a - (∑ j : V, b j) / (Fintype.card V : ℝ)) ^ 2 +
        ∑ i : V, ((∑ j : V, b j) / (Fintype.card V : ℝ) - b i) ^ 2 := by
    have hterm : ∀ i : V, (a - b i) ^ 2 =
        (a - (∑ j : V, b j) / (Fintype.card V : ℝ)) ^ 2 +
          2 * (a - (∑ j : V, b j) / (Fintype.card V : ℝ)) *
            ((∑ j : V, b j) / (Fintype.card V : ℝ) - b i) +
          ((∑ j : V, b j) / (Fintype.card V : ℝ) - b i) ^ 2 := by
      intro i
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, hzero, mul_zero, add_zero]
  rw [hexp]
  first | (field_simp; ring) | field_simp

/-- Annotator `i`'s preference label for the ordered pair `(x,y)`: `1` if `i`
strictly prefers `x` to `y`, and `0` otherwise. -/
noncomputable def voterPreferenceLabel (R : V → α → α → Bool) (i : V) (x y : α) : ℝ :=
  prefIndicator (strictPrefRel (R i) x y)

/-- The `π`-independent variance term `V_{x,y}` of Appendix `IPOApp`. -/
noncomputable def pairLabelVariance (τ : ℝ) (R : V → α → α → Bool) (x y : α) : ℝ :=
  (∑ i : V, (paperNormalizedCbar R x y / τ - voterPreferenceLabel R i x y / τ) ^ 2) /
    (Fintype.card V : ℝ)

/-- The population offline IPO loss of Remark `IPOremark`, written as the
paper writes it (a log of a fraction minus the scaled label), with the
expectation taken as the uniform average over annotators and over ordered
pairs of distinct completions. -/
noncomputable def populationIPOLoss (τ : ℝ)
    (R : V → α → α → Bool) (ρ π : α → ℝ) : ℝ :=
  ipoPairSum (fun x y =>
      (∑ i : V, (Real.log (π x * ρ y / (π y * ρ x)) -
          voterPreferenceLabel R i x y / τ) ^ 2) / (Fintype.card V : ℝ)) /
    ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))

/-- The per-pair identity of Appendix `IPOApp`: for a fixed ordered pair of
distinct completions, the expected squared loss is the `IPO_τ` summand plus
`V_{x,y}`.  The label's mean is `c̄_{x,y}(𝐑)` because on linear-order profiles
every annotator compares the pair strictly. -/
theorem pairPopulationIPOLoss_eq [Nonempty V]
    {τ : ℝ} {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ π : α → ℝ} (hρ : ∀ z, 0 < ρ z) (hπ : ∀ z, 0 < π z)
    {x y : α} (hxy : x ≠ y) :
    (∑ i : V, (Real.log (π x * ρ y / (π y * ρ x)) -
        voterPreferenceLabel R i x y / τ) ^ 2) / (Fintype.card V : ℝ) =
      (Real.log (π x / ρ x) - Real.log (π y / ρ y) -
          paperNormalizedCbar R x y / τ) ^ 2 +
        pairLabelVariance τ R x y := by
  have hmean : (∑ j : V, voterPreferenceLabel R j x y / τ) / (Fintype.card V : ℝ) =
      paperNormalizedCbar R x y / τ := by
    rw [← Finset.sum_div, paperNormalizedCbar_eq_strictPrefCount_div_card hR hxy]
    unfold strictPrefCount voterPreferenceLabel
    ring
  unfold pairLabelVariance
  rw [avg_sq_sub_eq, hmean, log_ratio_div_eq_sub hπ hρ x y]

/-- The whole population loss is `IPO_τ` plus a `π`-independent constant,
divided by the number `m(m-1)` of ordered pairs. -/
theorem populationIPOLoss_eq [Nonempty V]
    {τ : ℝ} {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ π : α → ℝ} (hρ : ∀ z, 0 < ρ z) (hπ : ∀ z, 0 < π z) :
    populationIPOLoss τ R ρ π =
      (offlineIPOObjective τ R ρ π + ipoPairSum (pairLabelVariance τ R)) /
        ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) := by
  unfold populationIPOLoss offlineIPOObjective pairwiseIPOLoss
  rw [← ipoPairSum_add]
  congr 1
  unfold ipoPairSum
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y hy => ?_
  exact pairPopulationIPOLoss_eq hR hρ hπ (Ne.symm (Finset.mem_erase.mp hy).1)

omit [DecidableEq α] [Nonempty α] in
/-- A positive rescaling plus a constant, valid on the full-support domain,
preserves the full-support minimizer set. -/
lemma fullSupportArgminSet_eq_of_eq_mul_add_const_on
    (L₁ L₂ : (α → ℝ) → ℝ) {c k : ℝ} (hc : 0 < c)
    (h : ∀ π : α → ℝ, IsFullSupportLottery π → L₁ π = c * L₂ π + k) :
    fullSupportArgminSet L₁ = fullSupportArgminSet L₂ := by
  ext π
  constructor
  · rintro ⟨hπ, hm⟩
    refine ⟨hπ, fun q hq => ?_⟩
    have h1 := hm q hq
    rw [h π hπ, h q hq] at h1
    exact le_of_mul_le_mul_left (by linarith) hc
  · rintro ⟨hπ, hm⟩
    refine ⟨hπ, fun q hq => ?_⟩
    have h1 := hm q hq
    rw [h π hπ, h q hq]
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    linarith

/-- The population offline IPO loss and `IPO_τ` have the same full-support
minimizers (profiles have at least two candidates). -/
theorem populationIPOLoss_argmin_eq_offline [Nonempty V]
    (hm : 2 ≤ Fintype.card α)
    {τ : ℝ} {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (populationIPOLoss τ R ρ) =
      fullSupportArgminSet (offlineIPOObjective τ R ρ) := by
  have hm' : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hm
  have hM : 0 < (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) :=
    mul_pos (by linarith) (by linarith)
  refine fullSupportArgminSet_eq_of_eq_mul_add_const_on _ _
    (c := 1 / ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)))
    (k := ipoPairSum (pairLabelVariance τ R) /
      ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)))
    (one_div_pos.mpr hM) ?_
  intro π hπ
  rw [populationIPOLoss_eq hR hρ.1 hπ.1]
  ring

/-- Remark `IPOremark`, first claim, via Appendix `IPOApp`: the population
offline IPO loss is uniquely minimized over `Δ°` by PB with parameter
`1/(τmn)`. -/
theorem populationIPOLoss_argmin [Nonempty V]
    (hm : 2 ≤ Fintype.card α)
    {τ : ℝ} (hτ : 0 < τ)
    {R : V → α → α → Bool} (hR : IsLinearOrderProfile R)
    {ρ : α → ℝ} (hρ : IsFullSupportLottery ρ) :
    fullSupportArgminSet (populationIPOLoss τ R ρ) =
      ({proportionalBorda
        (1 / (τ * (Fintype.card α : ℝ) * (Fintype.card V : ℝ)))
        ρ (partialBordaScoreP R)} : Set (α → ℝ)) := by
  rw [populationIPOLoss_argmin_eq_offline hm hR hρ]
  exact offlineIPOObjective_argmin hτ hR hρ

end Profiles

end PaperFormalization
