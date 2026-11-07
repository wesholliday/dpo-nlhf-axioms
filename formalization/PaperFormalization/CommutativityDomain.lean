import PaperFormalization.Commutativity
import PaperFormalization.WeakProfileBorda
import PaperFormalization.NLHFExistence

open scoped BigOperators

namespace PaperFormalization

/-! # Commutativity with the paper's domain-closure clauses

`paper/main.tex`, Section `CommSec`, defines commutativity as follows:

> A rule `F` is *commutative* if for any `(𝐑,ρ) ∈ dom(F)` and
> `(𝐑', F(𝐑,ρ)) ∈ dom(F)`, we have `(𝐑',ρ), (𝐑, F(𝐑',ρ)) ∈ dom(F)` and
> `F(𝐑', F(𝐑,ρ)) = F(𝐑, F(𝐑',ρ))`.

`SatisfiesCommutativity` (`Axioms.lean`) records only the final equation, and
quantifies `ρ` over full-support lotteries only.  This module adds the
domain-parameterized predicate `SatisfiesCommutativityOn`, which states the
paper's definition verbatim — hypotheses `(M,ρ) ∈ Dom` and
`(N, F M ρ) ∈ Dom`, conclusions `(N,ρ) ∈ Dom`, `(M, F N ρ) ∈ Dom` *and* the
equation — and proves it for the two rules of Proposition `RTBTorder` on
their paper domains:

* `PB_η^p`: `dom(PB_η) = {(𝐑,ρ) | ρ ∈ Δ}` (`paper/main.tex`, the
  proportional-Borda example), i.e. *all* lotteries, including boundary ones.
  This requires generalizing the tilt lemmas of `Multiplicative.lean` from
  full-support `ρ` to arbitrary lotteries, which is done below.
* `RTBT_β`: `dom(RTBT_β) = 𝒟`, whose reference component is `Δ°`; the
  matrix component is left as an arbitrary predicate `P` (instantiated by
  the Ford strong-connectedness condition), and Bradley–Terry positivity is
  only required on `P`.

Finally, `satisfiesCommutativity_of_commutativityOn_of_preserves` transfers a
`SatisfiesCommutativityOn` fact on the full-support domain to the
equation-only predicate, so the `NLHFcomm` counterexample gives a
violation of the paper's full definition. -/

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ## Tilt lemmas for arbitrary lotteries

Mechanical generalizations of `Multiplicative.lean`: the only role of
`∀ x, 0 < ρ x` there is to make the normalizing denominator positive, and
`IsLottery ρ` already suffices for that (some coordinate must be positive
because the coordinates sum to `1`). -/

omit [Nonempty α] in
/-- The tilt denominator is positive for *any* lottery reference, not only
full-support ones. -/
lemma tiltDen_pos_of_lottery {ρ ℓ : α → ℝ}
    (hρ : IsLottery ρ) (hℓ : ∀ x : α, 0 < ℓ x) :
    0 < tiltDen ρ ℓ := by
  classical
  obtain ⟨x0, -, hx0⟩ : ∃ x0 ∈ (Finset.univ : Finset α), 0 < ρ x0 := by
    by_contra hcon
    push_neg at hcon
    have hzero : Finset.sum Finset.univ (fun x => ρ x) = 0 :=
      Finset.sum_eq_zero (fun x hx => le_antisymm (hcon x hx) (hρ.1 x))
    rw [hρ.2] at hzero
    exact absurd hzero one_ne_zero
  have hterm : 0 < ρ x0 * ℓ x0 := mul_pos hx0 (hℓ x0)
  have hrest : 0 ≤ Finset.sum (Finset.univ.erase x0) (fun x => ρ x * ℓ x) :=
    Finset.sum_nonneg (fun x _hx => mul_nonneg (hρ.1 x) (hℓ x).le)
  have hsplit :
      tiltDen ρ ℓ =
        ρ x0 * ℓ x0 +
          Finset.sum (Finset.univ.erase x0) (fun x => ρ x * ℓ x) := by
    unfold tiltDen
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun x => ρ x * ℓ x) (by simp)]
  rw [hsplit]
  linarith

omit [Nonempty α] in
/-- Tilting a lottery by a positive likelihood vector gives a lottery. -/
lemma tilt_isLottery_of_lottery {ρ ℓ : α → ℝ}
    (hρ : IsLottery ρ) (hℓ : ∀ x : α, 0 < ℓ x) :
    IsLottery (tilt ρ ℓ) := by
  have hden : 0 < tiltDen ρ ℓ := tiltDen_pos_of_lottery hρ hℓ
  refine ⟨fun x => ?_, ?_⟩
  · unfold tilt
    exact div_nonneg (mul_nonneg (hρ.1 x) (hℓ x).le) hden.le
  · calc
      Finset.sum Finset.univ (fun x => tilt ρ ℓ x)
          = Finset.sum Finset.univ (fun x => ρ x * ℓ x) / tiltDen ρ ℓ := by
            simp [tilt, Finset.sum_div]
      _ = 1 := by
            change tiltDen ρ ℓ / tiltDen ρ ℓ = 1
            exact div_self hden.ne'

omit [Nonempty α] in
lemma tiltDen_tilt_of_lottery {ρ ℓ₁ ℓ₂ : α → ℝ}
    (hρ : IsLottery ρ) (hℓ₁ : ∀ x : α, 0 < ℓ₁ x) :
    tiltDen (tilt ρ ℓ₁) ℓ₂ =
      tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x) / tiltDen ρ ℓ₁ := by
  have hden : tiltDen ρ ℓ₁ ≠ 0 := (tiltDen_pos_of_lottery hρ hℓ₁).ne'
  have hsum : (Finset.sum Finset.univ (fun x => ρ x * ℓ₁ x)) ≠ 0 := by
    simpa [tiltDen] using hden
  calc
    tiltDen (tilt ρ ℓ₁) ℓ₂
        = Finset.sum Finset.univ
            (fun x => (ρ x * (ℓ₁ x * ℓ₂ x)) / tiltDen ρ ℓ₁) := by
              unfold tiltDen tilt
              refine Finset.sum_congr rfl ?_
              intro x hx
              field_simp [hsum]
              simp [tiltDen]
              ring
    _ = tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x) / tiltDen ρ ℓ₁ := by
          simp [tiltDen, Finset.sum_div]

omit [Nonempty α] in
lemma tilt_tilt_mul_of_lottery {ρ ℓ₁ ℓ₂ : α → ℝ}
    (hρ : IsLottery ρ)
    (hℓ₁ : ∀ x : α, 0 < ℓ₁ x) (hℓ₂ : ∀ x : α, 0 < ℓ₂ x) :
    tilt (tilt ρ ℓ₁) ℓ₂ = tilt ρ (fun x => ℓ₁ x * ℓ₂ x) := by
  funext x
  have hden₁ : tiltDen ρ ℓ₁ ≠ 0 := (tiltDen_pos_of_lottery hρ hℓ₁).ne'
  have hden₁₂ : tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x) ≠ 0 :=
    (tiltDen_pos_of_lottery hρ (fun x => mul_pos (hℓ₁ x) (hℓ₂ x))).ne'
  have hden_tilt :
      tiltDen (tilt ρ ℓ₁) ℓ₂ =
        tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x) / tiltDen ρ ℓ₁ :=
    tiltDen_tilt_of_lottery hρ hℓ₁
  change (tilt ρ ℓ₁ x * ℓ₂ x / tiltDen (tilt ρ ℓ₁) ℓ₂) =
    (ρ x * (ℓ₁ x * ℓ₂ x) / tiltDen ρ (fun x => ℓ₁ x * ℓ₂ x))
  rw [hden_tilt]
  unfold tilt
  field_simp [hden₁, hden₁₂]

omit [Nonempty α] in
/-- Field's reformulated update commutes on the *whole* simplex, not only on
its interior. -/
theorem tilt_commutative_of_lottery {ρ ℓ₁ ℓ₂ : α → ℝ}
    (hρ : IsLottery ρ)
    (hℓ₁ : ∀ x : α, 0 < ℓ₁ x) (hℓ₂ : ∀ x : α, 0 < ℓ₂ x) :
    tilt (tilt ρ ℓ₁) ℓ₂ = tilt (tilt ρ ℓ₂) ℓ₁ := by
  rw [tilt_tilt_mul_of_lottery hρ hℓ₁ hℓ₂, tilt_tilt_mul_of_lottery hρ hℓ₂ hℓ₁]
  funext x
  simp [tilt, mul_comm]

/-! ## Proportional Borda on its full paper domain -/

omit [Nonempty α] in
/-- `PB_η` maps `Δ` into `Δ`: the domain-closure clause for the paper's
proportional-Borda domain. -/
theorem proportionalBorda_isLottery_of_lottery {η : ℝ} {ρ B : α → ℝ}
    (hρ : IsLottery ρ) :
    IsLottery (proportionalBorda η ρ B) := by
  unfold proportionalBorda
  exact tilt_isLottery_of_lottery hρ (fun _ => Real.exp_pos _)

omit [Nonempty α] in
/-- Proposition `RTBTorder`, proportional-Borda half, for arbitrary (possibly
boundary) reference lotteries. -/
theorem proportionalBorda_commutative_of_lottery {η : ℝ} {ρ B₁ B₂ : α → ℝ}
    (hρ : IsLottery ρ) :
    proportionalBorda η (proportionalBorda η ρ B₁) B₂ =
      proportionalBorda η (proportionalBorda η ρ B₂) B₁ := by
  unfold proportionalBorda
  exact tilt_commutative_of_lottery hρ
    (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _)

/-! ## The paper's commutativity predicate, with domain closure -/

/-- A reference-dependent rule whose first input has type `ι`.  Taking
`ι = α → α → ℝ` recovers the matrix rules used elsewhere; taking `ι` to be
a bundled finite profile lets the same definition state the paper's
profile-level proposition while allowing the two profiles to have different
electorate sizes. -/
abbrev ReferenceRule (ι α : Type*) := ι → (α → ℝ) → α → ℝ

/-- The domain of a reference-dependent rule: which pairs `(I, ρ)` lie in
`dom(F)`. -/
abbrev ReferenceRuleDomain (ι α : Type*) := ι → (α → ℝ) → Prop

/-- Matrix-level specialization for the NLHF statements. -/
abbrev MatrixRuleDomain (α : Type*) :=
  ReferenceRuleDomain (α → α → ℝ) α

/-- Commutativity exactly as defined in `paper/main.tex`, Section `CommSec`,
*including* the domain-closure clauses: if `(M,ρ) ∈ dom(F)` and
`(N, F(M,ρ)) ∈ dom(F)`, then `(N,ρ) ∈ dom(F)`, `(M, F(N,ρ)) ∈ dom(F)`, and
`F(N, F(M,ρ)) = F(M, F(N,ρ))`. -/
def SatisfiesCommutativityOn {ι α : Type*}
    (Dom : ReferenceRuleDomain ι α) (F : ReferenceRule ι α) : Prop :=
  ∀ (I J : ι) (ρ : α → ℝ),
    Dom I ρ → Dom J (F I ρ) →
      Dom J ρ ∧ Dom I (F J ρ) ∧ F J (F I ρ) = F I (F J ρ)

/-- Failure of the paper's commutativity property on a given domain. -/
def ViolatesCommutativityOn {ι α : Type*}
    (Dom : ReferenceRuleDomain ι α) (F : ReferenceRule ι α) : Prop :=
  ¬ SatisfiesCommutativityOn Dom F

omit [Nonempty α] in
/-- Any multiplicative proportional-Borda update is commutative on the whole
simplex, independently of the type used to carry profile data. -/
theorem proportionalBordaRule_commutativityOn
    {ι : Type*} (η : ℝ) (B : ι → α → ℝ) :
    SatisfiesCommutativityOn (fun _ ρ => IsLottery ρ)
      (fun I ρ => proportionalBorda η ρ (B I)) := by
  intro I J ρ hρ _hIρ
  exact ⟨hρ, proportionalBorda_isLottery_of_lottery hρ,
    proportionalBorda_commutative_of_lottery hρ⟩

omit [Nonempty α] in
/-- Variant retaining any input-side well-formedness predicate in the domain.
This is used below for the paper's nonempty reflexive-profile requirement. -/
theorem proportionalBordaRule_commutativityOn_of_inputPred
    {ι : Type*} (η : ℝ) (B : ι → α → ℝ) (P : ι → Prop) :
    SatisfiesCommutativityOn (fun I ρ => P I ∧ IsLottery ρ)
      (fun I ρ => proportionalBorda η ρ (B I)) := by
  rintro I J ρ ⟨hPI, hρ⟩ ⟨hPJ, -⟩
  exact ⟨⟨hPJ, hρ⟩,
    ⟨hPI, proportionalBorda_isLottery_of_lottery hρ⟩,
    proportionalBorda_commutative_of_lottery hρ⟩

omit [Nonempty α] in
/-- Proposition `RTBTorder`, proportional-Borda half, in the paper's full
sense: `PB_η` is commutative on its paper domain `{(𝐑,ρ) | ρ ∈ Δ}`, and the
domain-closure clauses hold. -/
theorem proportionalBordaMatrixRule_commutativityOn
    (η : ℝ) (B : (α → α → ℝ) → α → ℝ) :
    SatisfiesCommutativityOn (fun _ ρ => IsLottery ρ)
      (fun M ρ => proportionalBorda η ρ (B M)) :=
  proportionalBordaRule_commutativityOn η B

/-- Proposition `RTBTorder`, RTBT half, in the paper's full sense: on a domain
whose matrix component is any predicate `P` (in the paper: Ford strong
connectedness) and whose reference component is `Δ°`, `RTBT_β` satisfies the
domain-closure clauses and the commutativity equation.  Bradley–Terry
positivity is only assumed on `P`. -/
theorem RTBTFromStrength_commutativityOn
    {ι : Type*} {β : ℝ} (hβ : 0 < β) (P : ι → Prop)
    {BT : ι → α → ℝ}
    (hBTpos : ∀ I : ι, P I → ∀ x : α, 0 < BT I x) :
    SatisfiesCommutativityOn (fun I ρ => P I ∧ IsFullSupportLottery ρ)
      (fun I ρ => RTBTFromStrength β ρ (BT I)) := by
  rintro I J ρ ⟨hPI, hρ⟩ ⟨hPJ, -⟩
  exact ⟨⟨hPJ, hρ⟩,
    ⟨hPI, RTBTFromStrength_fullSupport β hρ.1 (hBTpos J hPJ)⟩,
    RTBTFromStrength_commutative hβ hρ.1 (hBTpos I hPI) (hBTpos J hPJ)⟩

/-! ## Concrete finite-profile domains for Proposition `RTBTorder` -/

/-- A finite weak-relation profile with its electorate size bundled into the
input.  Two values of this type may have different `voterCount`s, exactly as
the paper's commutativity definition permits for `𝐑` and `𝐑'`. -/
structure FiniteProfile (α : Type*) where
  voterCount : ℕ
  relation : Fin voterCount → α → α → Bool

/-- The paper's profile well-formedness conditions: a nonempty finite
electorate and a reflexive relation for every voter. -/
def FiniteProfile.IsPaperProfile (I : FiniteProfile α) : Prop :=
  0 < I.voterCount ∧ IsReflexiveProfile I.relation

/-- The paper's partial-Borda score `B^p` of a bundled finite profile. -/
noncomputable def finiteProfilePartialBordaScore
    (I : FiniteProfile α) : α → ℝ :=
  partialBordaScoreP I.relation

/-- The strict-win count matrix `c_{x,y}` of a bundled weak-relation profile. -/
noncomputable def finiteProfileStrictCount
    (I : FiniteProfile α) : α → α → ℝ :=
  strictCount (strictPart I.relation)

/-- The count-graph side of the paper's RTBT domain `𝒟`. -/
def FiniteProfile.fordConnected (I : FiniteProfile α) : Prop :=
  FordStronglyConnected (finiteProfileStrictCount I)

/-- A total extension of the actual Ford/Zermelo-selected BT strength map.
On Ford-connected profiles this is exactly `selectedBTOfFordZermelo` applied
to the profile's strict counts.  Outside RTBT's domain it returns the positive
constant vector `1`; that branch is operationally irrelevant but makes the
reference-dependent rule a total Lean function. -/
noncomputable def finiteProfileSelectedBTOfFordZermelo
    (hFord : FordZermeloBTTheorem α) (I : FiniteProfile α) : α → ℝ := by
  classical
  exact if hconn : I.fordConnected then
    selectedBTOfFordZermelo hFord (finiteProfileStrictCount I)
      (strictCount_isFordCountMatrix
        (isIrreflexiveProfile_strictPart I.relation))
      hconn
  else
    fun _ => 1

/-- On its Ford-connected domain, the total extension is definitionally the
actual Ford/Zermelo-selected Bradley--Terry vector. -/
theorem finiteProfileSelectedBTOfFordZermelo_eq_on_domain
    (hFord : FordZermeloBTTheorem α) (I : FiniteProfile α)
    (hconn : I.fordConnected) :
    finiteProfileSelectedBTOfFordZermelo hFord I =
      selectedBTOfFordZermelo hFord (finiteProfileStrictCount I)
        (strictCount_isFordCountMatrix
          (isIrreflexiveProfile_strictPart I.relation))
        hconn := by
  simp [finiteProfileSelectedBTOfFordZermelo, hconn]

/-- The explicit totalization branch outside the paper's RTBT domain. -/
theorem finiteProfileSelectedBTOfFordZermelo_eq_one_off_domain
    (hFord : FordZermeloBTTheorem α) (I : FiniteProfile α)
    (hconn : ¬ I.fordConnected) :
    finiteProfileSelectedBTOfFordZermelo hFord I = fun _ => 1 := by
  simp [finiteProfileSelectedBTOfFordZermelo, hconn]

/-- Positivity of the actual selected strengths on the RTBT domain. -/
theorem finiteProfileSelectedBTOfFordZermelo_pos
    (hFord : FordZermeloBTTheorem α) (I : FiniteProfile α)
    (hconn : I.fordConnected) :
    ∀ x : α, 0 < finiteProfileSelectedBTOfFordZermelo hFord I x := by
  rw [finiteProfileSelectedBTOfFordZermelo_eq_on_domain hFord I hconn]
  exact selectedBTOfFordZermelo_pos hFord
    (strictCount_isFordCountMatrix
      (isIrreflexiveProfile_strictPart I.relation))
    hconn

/-- The actual proportional-Borda profile rule appearing in the paper. -/
noncomputable def finiteProfileProportionalBordaRule
    (η : ℝ) : ReferenceRule (FiniteProfile α) α :=
  fun I ρ => proportionalBorda η ρ (finiteProfilePartialBordaScore I)

/-- The actual selected-RTBT profile rule, totalized only outside its domain. -/
noncomputable def finiteProfileRTBTRule
    (hFord : FordZermeloBTTheorem α) (β : ℝ) :
    ReferenceRule (FiniteProfile α) α :=
  fun I ρ =>
    RTBTFromStrength β ρ (finiteProfileSelectedBTOfFordZermelo hFord I)

/-- The paper's full proportional-Borda domain: every finite profile and
every reference lottery in `Δ`, including its boundary. -/
def finiteProfileProportionalBordaDomain :
    ReferenceRuleDomain (FiniteProfile α) α :=
  fun I ρ => I.IsPaperProfile ∧ IsLottery ρ

/-- The paper's RTBT domain `𝒟`: Ford-connected strict-count graph and
full-support reference lottery. -/
def finiteProfileRTBTDomain :
    ReferenceRuleDomain (FiniteProfile α) α :=
  fun I ρ =>
    (I.IsPaperProfile ∧ I.fordConnected) ∧ IsFullSupportLottery ρ

/-- Concrete full-domain version of Proposition `RTBTorder`.  There are no
caller-supplied score, domain, or BT-selector parameters: the first conjunct
uses the actual partial-Borda score of bundled weak profiles on all of `Δ`;
the second uses the actual Ford/Zermelo-selected RTBT rule on `𝒟`. -/
theorem finiteProfileRTBTorder_commutativityOn
    (hFord : FordZermeloBTTheorem α)
    (η : ℝ) {β : ℝ} (hβ : 0 < β) :
    SatisfiesCommutativityOn
        (finiteProfileProportionalBordaDomain (α := α))
        (finiteProfileProportionalBordaRule (α := α) η) ∧
      SatisfiesCommutativityOn
        (finiteProfileRTBTDomain (α := α))
        (finiteProfileRTBTRule (α := α) hFord β) :=
  ⟨proportionalBordaRule_commutativityOn_of_inputPred η
      finiteProfilePartialBordaScore FiniteProfile.IsPaperProfile,
    RTBTFromStrength_commutativityOn hβ
      (fun I : FiniteProfile α => I.IsPaperProfile ∧ I.fordConnected)
      (fun I hI =>
        finiteProfileSelectedBTOfFordZermelo_pos hFord I hI.2)⟩

omit [Nonempty α] in
/-- A rule that maps the full-support domain into full-support lotteries and
satisfies the paper's commutativity property there also satisfies the
equation-only predicate `SatisfiesCommutativity`.  Contrapositively, an
equation-level counterexample refutes the paper's property. -/
theorem satisfiesCommutativity_of_commutativityOn_of_preserves
    {F : MatrixRule α}
    (hpres : ∀ (M : α → α → ℝ) (ρ : α → ℝ),
      IsNormalizedMarginMatrix M → IsFullSupportLottery ρ →
        IsFullSupportLottery (F M ρ))
    (h : SatisfiesCommutativityOn
      (fun M ρ => IsNormalizedMarginMatrix M ∧ IsFullSupportLottery ρ) F) :
    SatisfiesCommutativity F := by
  intro M N ρ hM hN hρ
  exact (h M N ρ ⟨hM, hρ⟩ ⟨hN, hpres M ρ hM hρ⟩).2.2

omit [DecidableEq α] [Nonempty α] in
/-- The selected NLHF rule maps the paper's domain into `Δ°`, so it is in
particular closed under iterated application. -/
theorem selectedNLHF_preserves_fullSupport
    {τ : ℝ} (hτ : 0 < τ) (M : α → α → ℝ) (ρ : α → ℝ)
    (hM : IsNormalizedMarginMatrix M) (hρ : IsFullSupportLottery ρ) :
    IsFullSupportLottery (selectedNLHF (α := α) τ M ρ) :=
  (selectedNLHF_selection hτ hM hρ).2.2.1

omit [Nonempty α] in
/-- Proposition `NLHFcomm` against the paper's full commutativity definition:
since `NLHF_τ` never leaves `Δ°`, the domain-closure clauses are automatic,
so the equation-level counterexample refutes the paper's property itself. -/
theorem violatesCommutativityOn_of_violatesCommutativity_selectedNLHF
    {τ : ℝ} (hτ : 0 < τ)
    (h : ViolatesCommutativity ((selectedNLHF (α := α)) τ)) :
    ViolatesCommutativityOn
      (fun (M : α → α → ℝ) (ρ : α → ℝ) =>
        IsNormalizedMarginMatrix M ∧ IsFullSupportLottery ρ)
      ((selectedNLHF (α := α)) τ) := by
  intro hsat
  exact h
    (satisfiesCommutativity_of_commutativityOn_of_preserves
      (fun M ρ hM hρ => selectedNLHF_preserves_fullSupport hτ M ρ hM hρ) hsat)

/-! ## Profile-level proportional Borda on the full simplex -/

/-- Proposition `RTBTorder`, proportional-Borda half, for the paper's `B^p`
on weak-relation profiles and *any* reference lottery `ρ ∈ Δ` (the paper's
domain for `PB_η`). -/
theorem proportionalBordaWeakProfile_commutative_lottery
    {V : Type*} [Fintype V]
    {η : ℝ} {ρ : α → ℝ}
    (R S : V → α → α → Bool)
    (hρ : IsLottery ρ) :
    proportionalBorda η
        (proportionalBorda η ρ (partialBordaScoreP R))
        (partialBordaScoreP S) =
      proportionalBorda η
        (proportionalBorda η ρ (partialBordaScoreP S))
        (partialBordaScoreP R) :=
  proportionalBorda_commutative_of_lottery hρ

/-- The profile-level domain-closure clause for `PB_η^p`. -/
theorem proportionalBordaWeakProfile_isLottery
    {V : Type*} [Fintype V]
    {η : ℝ} {ρ : α → ℝ} (R : V → α → α → Bool)
    (hρ : IsLottery ρ) :
    IsLottery (proportionalBorda η ρ (partialBordaScoreP R)) :=
  proportionalBorda_isLottery_of_lottery hρ

end PaperFormalization
