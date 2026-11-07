import PaperFormalization.FordZermelo
import PaperFormalization.RTBT
import PaperFormalization.WeakOrderScoreRepresentation

open scoped BigOperators

namespace PaperFormalization

/-! The camera-ready RTBT extension footnote.  On a finite comparison graph
with an edge in at least one direction between each pair of distinct vertices,
the vertices reaching every vertex form the unique top strongly connected
component. Fit BT on that component and extend its RTBT lottery by zero.
The extended rule retains the original rule on every strongly connected
profile, including profiles with some pairs never strictly compared. -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every distinct pair is strictly compared at least once. -/
def HasStrictComparisonEachPair (c : α → α → ℝ) : Prop :=
  ∀ x y, x ≠ y → 0 < c x y ∨ 0 < c y x

/-- The top component, characterized without choosing a representative. -/
def fordTopComponent (c : α → α → ℝ) : Set α :=
  {x | ∀ y, Relation.ReflTransGen (fordCountEdge c) x y}

noncomputable instance fordTopComponentFintype (c : α → α → ℝ) :
    Fintype (fordTopComponent c) := Fintype.ofFinite _

def fordTopCount (c : α → α → ℝ) :
    fordTopComponent c → fordTopComponent c → ℝ :=
  fun x y => c x.val y.val

theorem fordTopComponent_nonempty [Nonempty α] {c : α → α → ℝ}
    (hpair : HasStrictComparisonEachPair c) :
    (fordTopComponent c).Nonempty := by
  classical
  have aux : ∀ s : Finset α, ∃ x : α,
      ∀ y ∈ s, Relation.ReflTransGen (fordCountEdge c) x y := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨Classical.arbitrary α, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨x, hx⟩ := ih
      by_cases hxa : Relation.ReflTransGen (fordCountEdge c) x a
      · refine ⟨x, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxa
        · exact hx y hy
      · have hne : a ≠ x := by
          rintro rfl
          exact hxa Relation.ReflTransGen.refl
        have hax : fordCountEdge c a x := by
          rcases hpair a x hne with h | h
          · exact ⟨hne, h⟩
          · exact (hxa (Relation.ReflTransGen.single ⟨hne.symm, h⟩)).elim
        refine ⟨a, ?_⟩
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact Relation.ReflTransGen.refl
        · exact (Relation.ReflTransGen.single hax).trans (hx y hy)
  obtain ⟨x, hx⟩ := aux Finset.univ
  exact ⟨x, fun y => hx y (Finset.mem_univ y)⟩

omit [Fintype α] [DecidableEq α] in
/-- Any vertex that can reach the top component belongs to it. -/
theorem fordTopComponent_of_reaches {c : α → α → ℝ} {x y : α}
    (hxy : Relation.ReflTransGen (fordCountEdge c) x y)
    (hy : y ∈ fordTopComponent c) : x ∈ fordTopComponent c :=
  fun z => hxy.trans (hy z)

theorem fordTopComponent_no_incoming {c : α → α → ℝ} {x y : α}
    (hx : x ∉ fordTopComponent c) (hy : y ∈ fordTopComponent c) :
    ¬ fordCountEdge c x y := by
  intro hxy
  exact hx (fordTopComponent_of_reaches (Relation.ReflTransGen.single hxy) hy)

/-- The top set is exactly one maximal mutual-reachability class. -/
theorem fordTopComponent_eq_scc {c : α → α → ℝ} {x : α}
    (hx : x ∈ fordTopComponent c) :
    fordTopComponent c = {y |
      Relation.ReflTransGen (fordCountEdge c) x y ∧
      Relation.ReflTransGen (fordCountEdge c) y x} := by
  ext y
  exact ⟨fun hy => ⟨hx y, hy x⟩,
    fun hy => fordTopComponent_of_reaches hy.2 hx⟩

theorem fordTopCount_stronglyConnected (c : α → α → ℝ) :
    FordStronglyConnected (fordTopCount c) := by
  have liftPath {a b : α} (h : Relation.ReflTransGen (fordCountEdge c) a b) :
      ∀ ha : a ∈ fordTopComponent c, ∀ hb : b ∈ fordTopComponent c,
        Relation.ReflTransGen (fordCountEdge (fordTopCount c)) ⟨a, ha⟩ ⟨b, hb⟩ := by
    induction h with
    | refl => intro ha hb; exact Relation.ReflTransGen.refl
    | @tail b d hpath hbd ih =>
      intro ha hd
      have hb := fordTopComponent_of_reaches (Relation.ReflTransGen.single hbd) hd
      exact (ih ha hb).tail ⟨fun heq => hbd.1 (congrArg Subtype.val heq), hbd.2⟩
  intro x y
  exact liftPath (x.property y.val) x.property y.property

omit [Fintype α] [DecidableEq α] in
theorem fordTopCount_isFordCountMatrix {c : α → α → ℝ}
    (hc : IsFordCountMatrix c) : IsFordCountMatrix (fordTopCount c) :=
  ⟨fun x => hc.1 x.val, fun x y => hc.2 x.val y.val⟩

omit [Fintype α] [DecidableEq α] in
/-- A nonempty strongly connected set with no incoming edges must be the
top component. This makes the uniqueness in the footnote explicit. -/
theorem fordTopComponent_unique {c : α → α → ℝ}
    (hpair : HasStrictComparisonEachPair c)
    {S : Set α} (hne : S.Nonempty)
    (hconn : ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen (fordCountEdge c) x y)
    (hin : ∀ x ∉ S, ∀ y ∈ S, ¬ fordCountEdge c x y) :
    S = fordTopComponent c := by
  classical
  apply Set.Subset.antisymm
  · intro x hx y
    by_cases hy : y ∈ S
    · exact hconn x hx y hy
    · have hxy : x ≠ y := fun h => hy (h ▸ hx)
      rcases hpair x y hxy with h | h
      · exact Relation.ReflTransGen.single ⟨hxy, h⟩
      · exact (hin y hy x hx ⟨hxy.symm, h⟩).elim
  · intro x hx
    by_contra hxS
    obtain ⟨y, hy⟩ := hne
    obtain ⟨a, ha, b, hb, hab⟩ :=
      exists_edge_crossing_of_reflTransGen hxS hy (hx y)
    exact hin a ha b hb hab

/-- Extend a lottery on a subset by zero outside the subset. -/
noncomputable def lotteryExtendByZero (S : Set α) (p : S → ℝ) : α → ℝ := by
  classical
  exact fun x => if hx : x ∈ S then p ⟨x, hx⟩ else 0

omit [DecidableEq α] in
theorem lotteryExtendByZero_isLottery {S : Set α} [Fintype S]
    {p : S → ℝ} (hp : IsLottery p) :
    IsLottery (lotteryExtendByZero S p) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x
    unfold lotteryExtendByZero
    split_ifs with hx
    · exact hp.1 ⟨x, hx⟩
    · exact le_refl 0
  · rw [show (∑ x, lotteryExtendByZero S p x) = ∑ x : S, p x from ?_]
    · exact hp.2
    · calc
        (∑ x, lotteryExtendByZero S p x) =
            ∑ x ∈ S.toFinset, lotteryExtendByZero S p x := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro x hx hxS
          simp only [Set.mem_toFinset] at hxS
          simp [lotteryExtendByZero, hxS]
        _ = ∑ x : S, lotteryExtendByZero S p x :=
          Finset.sum_subtype S.toFinset (fun _ => Set.mem_toFinset) _
        _ = ∑ x : S, p x := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [lotteryExtendByZero]

/-- RTBT fitted on the top component.  Restricting a positive reference
without renormalizing it gives the same tilt, since its scale cancels. -/
noncomputable def topComponentRTBT (β : ℝ) (ρ : α → ℝ)
    (c : α → α → ℝ) (hc : IsFordCountMatrix c)
    (htop : (fordTopComponent c).Nonempty) : α → ℝ := by
  letI : Nonempty (fordTopComponent c) := htop.to_subtype
  exact lotteryExtendByZero (fordTopComponent c)
    (RTBTFromStrength β (fun x => ρ x.val)
      (selectedBTOfFordZermelo FordZermeloBTTheorem_finite (fordTopCount c)
        (fordTopCount_isFordCountMatrix hc) (fordTopCount_stronglyConnected c)))

theorem topComponentRTBT_isLottery (β : ℝ) {ρ : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (htop : (fordTopComponent c).Nonempty) :
    IsLottery (topComponentRTBT β ρ c hc htop) := by
  letI : Nonempty (fordTopComponent c) := htop.to_subtype
  exact lotteryExtendByZero_isLottery (RTBTFromStrength_fullSupport β
    (fun x => hρ x.val)
    (selectedBTOfFordZermelo_pos FordZermeloBTTheorem_finite
      (fordTopCount_isFordCountMatrix hc) (fordTopCount_stronglyConnected c))).toLottery

theorem topComponentRTBT_pos_iff (β : ℝ) {ρ : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (htop : (fordTopComponent c).Nonempty) (x : α) :
    0 < topComponentRTBT β ρ c hc htop x ↔ x ∈ fordTopComponent c := by
  letI : Nonempty (fordTopComponent c) := htop.to_subtype
  have hp := (RTBTFromStrength_fullSupport β (fun x : fordTopComponent c => hρ x.val)
    (selectedBTOfFordZermelo_pos FordZermeloBTTheorem_finite
      (fordTopCount_isFordCountMatrix hc) (fordTopCount_stronglyConnected c))).1
  classical
  unfold topComponentRTBT lotteryExtendByZero
  split_ifs with hx
  · exact iff_of_true (hp ⟨x, hx⟩) hx
  · simp [hx]

theorem topComponentRTBT_zero_outside (β : ℝ) (ρ : α → ℝ)
    {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (htop : (fordTopComponent c).Nonempty) {x : α}
    (hx : x ∉ fordTopComponent c) :
    topComponentRTBT β ρ c hc htop x = 0 := by
  simp [topComponentRTBT, lotteryExtendByZero, hx]

/-- The construction really uses the BT certificate of Proposition `BTProp`
on the induced component, not an independently chosen distribution. -/
def IsTopComponentRTBT (β : ℝ) (c : α → α → ℝ) (ρ π : α → ℝ) : Prop :=
  ∃ u : fordTopComponent c → ℝ,
    HasBTPropCertificate (fordPairTotal (fordTopCount c)) (fordTopCount c) u ∧
      π = lotteryExtendByZero (fordTopComponent c)
        (RTBTFromStrength β (fun x => ρ x.val) u)

theorem topComponentRTBT_certificate (β : ℝ) (ρ : α → ℝ)
    {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (htop : (fordTopComponent c).Nonempty) :
    IsTopComponentRTBT β c ρ (topComponentRTBT β ρ c hc htop) := by
  letI : Nonempty (fordTopComponent c) := htop.to_subtype
  exact ⟨_, selectedBTOfFordZermelo_certificate FordZermeloBTTheorem_finite
    (fordTopCount_isFordCountMatrix hc) (fordTopCount_stronglyConnected c), rfl⟩

/-- When the original graph is connected, fitting on its top component is
exactly the original fit. The component contains every vertex; BT uniqueness
identifies the two normalized strength vectors. -/
theorem topComponentRTBT_agrees [Nonempty α] (β : ℝ) (ρ : α → ℝ)
    {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (htop : (fordTopComponent c).Nonempty) (hconn : FordStronglyConnected c) :
    topComponentRTBT β ρ c hc htop =
      RTBTFromStrength β ρ
        (selectedBTOfFordZermelo FordZermeloBTTheorem_finite c hc hconn) := by
  classical
  letI : Nonempty (fordTopComponent c) := htop.to_subtype
  let u := selectedBTOfFordZermelo FordZermeloBTTheorem_finite c hc hconn
  have hu := selectedBTOfFordZermelo_isBTStrength FordZermeloBTTheorem_finite hc hconn
  have sumTop (f : α → ℝ) : (∑ x : fordTopComponent c, f x.val) = ∑ x, f x :=
    (Finset.sum_subtype Finset.univ (fun x =>
      iff_of_true (Finset.mem_univ x) (hconn x)) f).symm
  have sumEraseTop (f : α → ℝ) (x : fordTopComponent c) :
      (∑ y ∈ Finset.univ.erase x, f y.val) = ∑ y ∈ Finset.univ.erase x.val, f y := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ x),
      Finset.sum_erase_eq_sub (Finset.mem_univ x.val), sumTop]
  have huTop : IsBTStrength (fordPairTotal (fordTopCount c)) (fordTopCount c)
      (fun x => u x.val) := by
    refine ⟨⟨fun x => hu.1.1 x.val, ?_⟩, ?_⟩
    · rw [sumTop]
      exact hu.1.2
    · intro x
      change (∑ y ∈ Finset.univ.erase x,
        fordPairTotal c x.val y.val * (u x.val / (u x.val + u y.val))) =
          ∑ y ∈ Finset.univ.erase x, c x.val y.val
      rw [sumEraseTop (fun y => fordPairTotal c x.val y *
        (u x.val / (u x.val + u y))) x, sumEraseTop (fun y => c x.val y) x]
      exact hu.2 x.val
  have heq := selectedBTOfFordZermelo_unique_isBTStrength FordZermeloBTTheorem_finite
    (fordTopCount_isFordCountMatrix hc) (fordTopCount_stronglyConnected c) _ huTop
  funext x
  have hx : x ∈ fordTopComponent c := hconn x
  simp only [topComponentRTBT, lotteryExtendByZero, dif_pos hx]
  rw [← heq]
  change ρ x * (u x) ^ (1 / β) / (∑ z : fordTopComponent c, ρ z.val * (u z.val) ^ (1 / β)) = _
  rw [sumTop (fun z => ρ z * (u z) ^ (1 / β))]
  rfl

/-- Keep the whole original domain and add the domain in the footnote. -/
def RTBTExtensionDomain (c : α → α → ℝ) : Prop :=
  FordStronglyConnected c ∨ HasStrictComparisonEachPair c

theorem fordTopComponent_nonempty_of_domain [Nonempty α] {c : α → α → ℝ}
    (hdom : RTBTExtensionDomain c) : (fordTopComponent c).Nonempty := by
  rcases hdom with hconn | hpair
  · exact ⟨Classical.arbitrary α, hconn _⟩
  · exact fordTopComponent_nonempty hpair

noncomputable def extendedRTBT [Nonempty α] (β : ℝ) (ρ : α → ℝ)
    (c : α → α → ℝ) (hc : IsFordCountMatrix c)
    (hdom : RTBTExtensionDomain c) : α → ℝ :=
  topComponentRTBT β ρ c hc (fordTopComponent_nonempty_of_domain hdom)

theorem extendedRTBT_agrees [Nonempty α] (β : ℝ) (ρ : α → ℝ)
    {c : α → α → ℝ} (hc : IsFordCountMatrix c) (hdom : RTBTExtensionDomain c)
    (hconn : FordStronglyConnected c) :
    extendedRTBT β ρ c hc hdom =
      RTBTFromStrength β ρ (selectedBTOfFordZermelo FordZermeloBTTheorem_finite c hc hconn) :=
  topComponentRTBT_agrees β ρ hc _ hconn

theorem extendedRTBT_isLottery [Nonempty α] (β : ℝ) {ρ : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) {c : α → α → ℝ}
    (hc : IsFordCountMatrix c) (hdom : RTBTExtensionDomain c) :
    IsLottery (extendedRTBT β ρ c hc hdom) :=
  topComponentRTBT_isLottery β hρ hc _

/-- With a singleton top component, the construction automatically gives
the point mass; there is no need for a separate BT convention. -/
theorem topComponentRTBT_singleton (β : ℝ) {ρ : α → ℝ}
    (hρ : ∀ x, 0 < ρ x) {c : α → α → ℝ} (hc : IsFordCountMatrix c)
    (htop : (fordTopComponent c).Nonempty) {x : α}
    (hsingle : fordTopComponent c = {x}) :
    topComponentRTBT β ρ c hc htop = fun y => if y = x then 1 else 0 := by
  classical
  let p := topComponentRTBT β ρ c hc htop
  have hzero : ∀ y, y ≠ x → p y = 0 := by
    intro y hy
    exact topComponentRTBT_zero_outside β ρ hc htop (by simpa [hsingle] using hy)
  have hone : p x = 1 := by
    have hsum := (topComponentRTBT_isLottery β hρ hc htop).2
    change (∑ y, p y) = 1 at hsum
    rw [Finset.sum_eq_single x (fun y _ hy => hzero y hy) (by simp)] at hsum
    exact hsum
  funext y
  change p y = _
  by_cases hy : y = x
  · simpa [hy] using hone
  · simp [hy, hzero y hy]

omit [Fintype α] [DecidableEq α] in
/-- Translate the footnote's voterwise condition into positive strict counts. -/
theorem hasStrictComparisonEachPair_of_profile
    {V : Type*} [Fintype V] {R : V → α → α → Bool}
    (hpair : ∀ x y, x ≠ y → ∃ i,
      strictPart R i x y = true ∨ strictPart R i y x = true) :
    HasStrictComparisonEachPair (strictCount (strictPart R)) := by
  classical
  have pos {x y : α} {i : V} (hi : strictPart R i x y = true) :
      0 < strictCount (strictPart R) x y := by
    have hle := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => prefIndicator_nonneg (strictPart R j x y))
      (Finset.mem_univ i)
    have hval : prefIndicator (strictPart R i x y) = 1 := by simp [prefIndicator, hi]
    change prefIndicator (strictPart R i x y) ≤ strictCount (strictPart R) x y at hle
    rw [hval] at hle
    linarith
  intro x y hxy
  obtain ⟨i, hi | hi⟩ := hpair x y hxy
  · exact Or.inl (pos hi)
  · exact Or.inr (pos hi)

/-- All nonempty-electorate linear-order profiles belong to the added domain. -/
theorem hasStrictComparisonEachPair_of_linearProfile
    {V : Type*} [Fintype V] [Nonempty V] {R : V → α → α → Bool}
    (hR : IsLinearOrderProfile R) :
    HasStrictComparisonEachPair (strictCount (strictPart R)) := by
  apply hasStrictComparisonEachPair_of_profile
  intro x y hxy
  let i : V := Classical.arbitrary V
  refine ⟨i, ?_⟩
  rcases hR.1.2.1 i x y hxy with h | h
  · left
    have hrev : R i y x = false := by
      cases heq : R i y x
      · rfl
      · exact (hxy (hR.2 i x y h heq)).elim
    simp [strictPart, strictPrefRel, h, hrev]
  · right
    have hrev : R i x y = false := by
      cases heq : R i x y
      · rfl
      · exact (hxy (hR.2 i x y heq h)).elim
    simp [strictPart, strictPrefRel, h, hrev]

end PaperFormalization
