import PaperFormalization.DPO

namespace PaperFormalization

open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The directed comparison graph used in Ford/Zermelo: there is an edge
`x → y` when `x` has at least one strict win over `y`. -/
def fordCountEdge (c : α → α → ℝ) (x y : α) : Prop :=
  x ≠ y ∧ 0 < c x y

/-- Ford's finite irreducibility hypothesis: every alternative is reachable
from every other alternative in the directed positive-count graph. -/
def FordStronglyConnected (c : α → α → ℝ) : Prop :=
  ∀ x y : α, Relation.ReflTransGen (fordCountEdge c) x y

omit [Fintype α] [DecidableEq α] in
lemma fordCountEdge_mono
    {c d : α → α → ℝ}
    (h : ∀ x y : α, 0 < c x y → 0 < d x y)
    {x y : α} :
    fordCountEdge c x y → fordCountEdge d x y := by
  intro hxy
  exact ⟨hxy.1, h x y hxy.2⟩

omit [Fintype α] [DecidableEq α] in
lemma FordStronglyConnected_mono
    {c d : α → α → ℝ}
    (h : ∀ x y : α, 0 < c x y → 0 < d x y)
    (hconn : FordStronglyConnected c) :
    FordStronglyConnected d := by
  intro x y
  exact Relation.ReflTransGen.mono
    (fun a b hab => fordCountEdge_mono h hab) (hconn x y)

/-- Ford's original partition assumption, oriented to match `fordCountEdge`:
for every nontrivial partition, some object outside the chosen side has at
least one strict win over some object inside it. -/
def FordPartitionAssumption (c : α → α → ℝ) : Prop :=
  ∀ S : Set α, S.Nonempty → Sᶜ.Nonempty →
    ∃ x : α, x ∈ Sᶜ ∧ ∃ y : α, y ∈ S ∧ fordCountEdge c x y

omit [Fintype α] [DecidableEq α] in
lemma exists_edge_crossing_of_reflTransGen
    {edge : α → α → Prop} {S : Set α} {x y : α}
    (hx : x ∈ Sᶜ) (hy : y ∈ S)
    (hpath : Relation.ReflTransGen edge x y) :
    ∃ a : α, a ∈ Sᶜ ∧ ∃ b : α, b ∈ S ∧ edge a b := by
  induction hpath with
  | refl =>
      exact False.elim (hx hy)
  | tail hpath htail ih =>
      rename_i b c
      by_cases hb : b ∈ S
      · exact ih hb
      · exact ⟨b, hb, c, hy, htail⟩

omit [Fintype α] [DecidableEq α] in
lemma FordPartitionAssumption_of_stronglyConnected
    {c : α → α → ℝ}
    (hconn : FordStronglyConnected c) :
    FordPartitionAssumption c := by
  intro S hS hSc
  rcases hSc with ⟨x, hx⟩
  rcases hS with ⟨y, hy⟩
  exact exists_edge_crossing_of_reflTransGen hx hy (hconn x y)

omit [Fintype α] [DecidableEq α] in
lemma FordStronglyConnected_of_partitionAssumption
    {c : α → α → ℝ}
    (hpart : FordPartitionAssumption c) :
    FordStronglyConnected c := by
  intro x y
  let Reach : Set α := {z | Relation.ReflTransGen (fordCountEdge c) x z}
  by_contra hnot
  have hS : Reachᶜ.Nonempty := ⟨y, by simpa [Reach] using hnot⟩
  have hSc : (Reachᶜ)ᶜ.Nonempty := by
    refine ⟨x, ?_⟩
    intro hxNotReach
    exact hxNotReach (show x ∈ Reach from Relation.ReflTransGen.refl)
  rcases hpart Reachᶜ hS hSc with ⟨a, ha, b, hb, hab⟩
  have haReach : Relation.ReflTransGen (fordCountEdge c) x a := by
    simpa [Reach] using ha
  have hbNotReach : ¬ Relation.ReflTransGen (fordCountEdge c) x b := by
    simpa [Reach] using hb
  exact hbNotReach (Relation.ReflTransGen.tail haReach hab)

omit [Fintype α] [DecidableEq α] in
/-- Ford's partition formulation is equivalent to the reachability formulation
used elsewhere in the formalization. -/
theorem FordStronglyConnected_iff_partitionAssumption
    {c : α → α → ℝ} :
    FordStronglyConnected c ↔ FordPartitionAssumption c :=
  ⟨FordPartitionAssumption_of_stronglyConnected,
    FordStronglyConnected_of_partitionAssumption⟩

omit [Fintype α] [DecidableEq α] in
/-- Ford's partition assumption is preserved when positive-count edges are
only added. -/
lemma FordPartitionAssumption_mono
    {c d : α → α → ℝ}
    (h : ∀ x y : α, 0 < c x y → 0 < d x y)
    (hpart : FordPartitionAssumption c) :
    FordPartitionAssumption d :=
  FordPartitionAssumption_of_stronglyConnected
    (FordStronglyConnected_mono h
      (FordStronglyConnected_of_partitionAssumption hpart))

omit [Fintype α] [DecidableEq α] in
/-- Boundary step from Ford's existence proof: along a positive-count path
from a zero-weight object to a positive-weight object, some edge crosses from
zero weight to positive weight. -/
lemma exists_fordCountEdge_zero_to_pos_of_reflTransGen
    {c : α → α → ℝ} {u : α → ℝ} {x y : α}
    (hnonneg : ∀ z : α, 0 ≤ u z)
    (hx : u x = 0)
    (hy : 0 < u y)
    (hpath : Relation.ReflTransGen (fordCountEdge c) x y) :
    ∃ a b : α, fordCountEdge c a b ∧ u a = 0 ∧ 0 < u b := by
  induction hpath with
  | refl =>
      rw [hx] at hy
      norm_num at hy
  | tail hpath htail ih =>
      rename_i b z
      by_cases hb : u b = 0
      · exact ⟨b, z, htail, hb, hy⟩
      · have hbpos : 0 < u b := lt_of_le_of_ne (hnonneg b) (Ne.symm hb)
        exact ih hbpos

omit [Fintype α] [DecidableEq α] in
/-- Ford strong connectivity gives the boundary-crossing edge whenever a
nonnegative vector has one zero coordinate and one positive coordinate. -/
lemma exists_fordCountEdge_zero_to_pos_of_stronglyConnected
    {c : α → α → ℝ} {u : α → ℝ}
    (hconn : FordStronglyConnected c)
    (hnonneg : ∀ z : α, 0 ≤ u z)
    {x y : α}
    (hx : u x = 0)
    (hy : 0 < u y) :
    ∃ a b : α, fordCountEdge c a b ∧ u a = 0 ∧ 0 < u b :=
  exists_fordCountEdge_zero_to_pos_of_reflTransGen hnonneg hx hy (hconn x y)

omit [DecidableEq α] in
/-- Simplex-boundary form of Ford's boundary step: if a nonnegative
sum-one vector has a zero coordinate, strong connectivity supplies a
positive-count edge from a zero coordinate to a positive coordinate. -/
lemma exists_fordCountEdge_zero_to_pos_of_simplex_boundary
    {c : α → α → ℝ} {u : α → ℝ}
    (hconn : FordStronglyConnected c)
    (hnonneg : ∀ z : α, 0 ≤ u z)
    (hsum : Finset.sum Finset.univ (fun z : α => u z) = 1)
    {x : α}
    (hx : u x = 0) :
    ∃ a b : α, fordCountEdge c a b ∧ u a = 0 ∧ 0 < u b := by
  have hypos : ∃ y : α, 0 < u y := by
    by_contra hno
    have hzero : ∀ z : α, u z = 0 := by
      intro z
      have hzle : u z ≤ 0 := by
        exact le_of_not_gt (fun hz => hno ⟨z, hz⟩)
      exact le_antisymm hzle (hnonneg z)
    have hsum_zero : Finset.sum Finset.univ (fun z : α => u z) = 0 := by
      simp [hzero]
    rw [hsum] at hsum_zero
    norm_num at hsum_zero
  rcases hypos with ⟨y, hy⟩
  exact exists_fordCountEdge_zero_to_pos_of_stronglyConnected
    hconn hnonneg hx hy

/-- A compact finite connectivity certificate used for the paper's explicit
profiles: every ordered pair is connected by a directed path of length at most
two. -/
def hasDirectedPathLengthAtMostTwo {α : Type*} (edge : α → α → Prop)
    (x y : α) : Prop :=
  x = y ∨ edge x y ∨ ∃ z : α, edge x z ∧ edge z y

def stronglyConnectedByShortPaths {α : Type*} (edge : α → α → Prop) : Prop :=
  ∀ x y : α, hasDirectedPathLengthAtMostTwo edge x y

lemma stronglyConnectedByShortPaths_congr
    {γ : Type*} {edge edge' : γ → γ → Prop}
    (h : ∀ x y : γ, edge x y ↔ edge' x y)
    (hc : stronglyConnectedByShortPaths edge) :
    stronglyConnectedByShortPaths edge' := by
  intro x y
  rcases hc x y with hxy | hxy | ⟨z, hxz, hzy⟩
  · exact Or.inl hxy
  · exact Or.inr (Or.inl ((h x y).mp hxy))
  · exact Or.inr (Or.inr ⟨z, (h x z).mp hxz, (h z y).mp hzy⟩)

/- A length-at-most-two directed path certificate implies Ford's usual
reflexive-transitive-reachability formulation. -/
omit [Fintype α] [DecidableEq α] in
lemma FordStronglyConnected_of_shortPaths
    {c : α → α → ℝ}
    (hc : stronglyConnectedByShortPaths (fordCountEdge c)) :
    FordStronglyConnected c := by
  intro x y
  rcases hc x y with hxy | hxy | ⟨z, hxz, hzy⟩
  · subst y
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single hxy
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single hxz)
      (Relation.ReflTransGen.single hzy)

/-- Basic count-matrix side conditions for the Ford/Zermelo theorem. -/
def IsFordCountMatrix (c : α → α → ℝ) : Prop :=
  (∀ x : α, c x x = 0) ∧ ∀ x y : α, 0 ≤ c x y

/-- The total number of pairwise comparisons involving each unordered pair. -/
noncomputable def fordPairTotal (c : α → α → ℝ) (x y : α) : ℝ :=
  c x y + c y x

/-- The number of strict wins of `x`, summed over all opponents. -/
noncomputable def fordWinCount (c : α → α → ℝ) (x : α) : ℝ :=
  Finset.sum (Finset.univ.erase x) (fun y => c x y)

omit [Fintype α] [DecidableEq α] in
/-- The Bernoulli log-likelihood with true success probability `p` is maximized
at the fitted success probability `p`. This is the two-outcome analytic
inequality behind Ford's synthetic-matrix uniqueness argument. -/
lemma bernoulliLogLikelihood_le_self
    {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    p * Real.log q + (1 - p) * Real.log (1 - q) ≤
      p * Real.log p + (1 - p) * Real.log (1 - p) := by
  have h1mp : 0 < 1 - p := sub_pos.mpr hp1
  have h1mq : 0 < 1 - q := sub_pos.mpr hq1
  have hlog1 : p * Real.log (q / p) ≤ q - p := by
    calc
      p * Real.log (q / p) ≤ p * (q / p - 1) := by
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hq0 hp0)) hp0.le
      _ = q - p := by
        field_simp [hp0.ne']
  have hlog2 :
      (1 - p) * Real.log ((1 - q) / (1 - p)) ≤ p - q := by
    calc
      (1 - p) * Real.log ((1 - q) / (1 - p)) ≤
          (1 - p) * (((1 - q) / (1 - p)) - 1) := by
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos h1mq h1mp)) h1mp.le
      _ = p - q := by
        field_simp [h1mp.ne']
        ring
  have hdiff :
      p * Real.log q + (1 - p) * Real.log (1 - q) -
          (p * Real.log p + (1 - p) * Real.log (1 - p)) ≤ 0 := by
    calc
      p * Real.log q + (1 - p) * Real.log (1 - q) -
          (p * Real.log p + (1 - p) * Real.log (1 - p)) =
        p * Real.log (q / p) +
          (1 - p) * Real.log ((1 - q) / (1 - p)) := by
          rw [Real.log_div hq0.ne' hp0.ne',
            Real.log_div h1mq.ne' h1mp.ne']
          ring
      _ ≤ (q - p) + (p - q) := add_le_add hlog1 hlog2
      _ = 0 := by ring_nf
  linarith

omit [Fintype α] [DecidableEq α] in
/-- Strict form of the Bernoulli log-likelihood inequality: if the fitted
success probability differs from the generating probability, the
log-likelihood is strictly smaller. -/
lemma bernoulliLogLikelihood_lt_self_of_ne
    {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hpq : p ≠ q) :
    p * Real.log q + (1 - p) * Real.log (1 - q) <
      p * Real.log p + (1 - p) * Real.log (1 - p) := by
  have h1mp : 0 < 1 - p := sub_pos.mpr hp1
  have h1mq : 0 < 1 - q := sub_pos.mpr hq1
  have hqdivp_ne : q / p ≠ 1 := by
    intro h
    have hqp : q = p := by
      field_simp [hp0.ne'] at h
      linarith
    exact hpq hqp.symm
  have h1div_ne : (1 - q) / (1 - p) ≠ 1 := by
    intro h
    have hqp : q = p := by
      field_simp [h1mp.ne'] at h
      linarith
    exact hpq hqp.symm
  have hlog1 : p * Real.log (q / p) < q - p := by
    calc
      p * Real.log (q / p) < p * (q / p - 1) := by
        exact mul_lt_mul_of_pos_left
          (Real.log_lt_sub_one_of_pos (div_pos hq0 hp0) hqdivp_ne) hp0
      _ = q - p := by
        field_simp [hp0.ne']
  have hlog2 :
      (1 - p) * Real.log ((1 - q) / (1 - p)) < p - q := by
    calc
      (1 - p) * Real.log ((1 - q) / (1 - p)) <
          (1 - p) * (((1 - q) / (1 - p)) - 1) := by
        exact mul_lt_mul_of_pos_left
          (Real.log_lt_sub_one_of_pos (div_pos h1mq h1mp) h1div_ne) h1mp
      _ = p - q := by
        field_simp [h1mp.ne']
        ring
  have hdiff :
      p * Real.log q + (1 - p) * Real.log (1 - q) -
          (p * Real.log p + (1 - p) * Real.log (1 - p)) < 0 := by
    calc
      p * Real.log q + (1 - p) * Real.log (1 - q) -
          (p * Real.log p + (1 - p) * Real.log (1 - p)) =
        p * Real.log (q / p) +
          (1 - p) * Real.log ((1 - q) / (1 - p)) := by
          rw [Real.log_div hq0.ne' hp0.ne',
            Real.log_div h1mq.ne' h1mp.ne']
          ring
      _ < (q - p) + (p - q) := add_lt_add hlog1 hlog2
      _ = 0 := by ring_nf
  linarith

omit [Fintype α] [DecidableEq α] in
/-- Equality case of the Bernoulli likelihood inequality. -/
lemma bernoulliLogLikelihood_eq_self_iff
    {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    p * Real.log q + (1 - p) * Real.log (1 - q) =
        p * Real.log p + (1 - p) * Real.log (1 - p) ↔
      p = q := by
  constructor
  · intro h
    by_contra hpq
    have hlt := bernoulliLogLikelihood_lt_self_of_ne
      hp0 hp1 hq0 hq1 hpq
    rw [h] at hlt
    exact (lt_self_iff_false _).mp hlt
  · intro h
    rw [h]

/-- A directed sum over all `x` and all `y ≠ x` is the same as a sum over the
off-diagonal of `univ × univ`. -/
lemma sum_univ_erase_eq_sum_offDiag
    (f : α → α → ℝ) :
    Finset.sum Finset.univ (fun x =>
      Finset.sum (Finset.univ.erase x) (fun y => f x y)) =
      Finset.sum Finset.univ.offDiag (fun p : α × α => f p.1 p.2) := by
  classical
  have hoff : (Finset.univ.offDiag : Finset (α × α)) =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : α × α => p.1 ≠ p.2) := by
    ext p
    simp
  rw [hoff, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [← Finset.sum_filter]
  congr 1
  ext y
  simp [eq_comm]

/-- Product version of `sum_univ_erase_eq_sum_offDiag`. -/
lemma prod_univ_erase_eq_prod_offDiag
    (f : α → α → ℝ) :
    Finset.prod Finset.univ (fun x =>
      Finset.prod (Finset.univ.erase x) (fun y => f x y)) =
      Finset.prod Finset.univ.offDiag (fun p : α × α => f p.1 p.2) := by
  classical
  have hoff : (Finset.univ.offDiag : Finset (α × α)) =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : α × α => p.1 ≠ p.2) := by
    ext p
    simp
  rw [hoff, Finset.prod_filter, Finset.prod_product]
  refine Finset.prod_congr rfl ?_
  intro x _hx
  rw [← Finset.prod_filter]
  congr 1
  ext y
  simp [eq_comm]

/-- Swapping the two coordinates preserves off-diagonal directed sums. -/
lemma sum_offDiag_swap
    (f : α → α → ℝ) :
    Finset.sum Finset.univ.offDiag (fun p : α × α => f p.2 p.1) =
      Finset.sum Finset.univ.offDiag (fun p : α × α => f p.1 p.2) := by
  classical
  simpa using
    (Equiv.Perm.sum_comp (Equiv.prodComm α α) Finset.univ.offDiag
      (fun p : α × α => f p.1 p.2) (by
        intro p hp
        rcases p with ⟨x, y⟩
        simp [Equiv.prodComm] at hp ⊢
        simpa [eq_comm] using hp))

/-- Off-diagonal form of the Bradley--Terry log-likelihood objective. -/
lemma btObjective_eq_sum_offDiag
    (c : α → α → ℝ) (u : α → ℝ) :
    btObjective c u =
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        c p.1 p.2 * Real.log (btFraction u p.1 p.2)) := by
  rw [← sum_univ_erase_eq_sum_offDiag
    (fun x y => c x y * Real.log (btFraction u x y))]
  simp [btObjective, btFraction]

/-- Decompose the Bradley--Terry objective into row-win numerator terms and
pair-denominator terms. This is the algebraic identity that makes Ford's
synthetic matrix interchangeable with the original matrix once row wins and
pair totals agree. -/
lemma btObjective_eq_winCount_log_sub_pairDenom
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    btObjective c u =
      Finset.sum Finset.univ (fun x =>
        fordWinCount c x * Real.log (u x)) -
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        c p.1 p.2 * Real.log (u p.1 + u p.2)) := by
  calc
    btObjective c u =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 * Real.log (btFraction u p.1 p.2)) :=
          btObjective_eq_sum_offDiag c u
    _ =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 *
            (Real.log (u p.1) - Real.log (u p.1 + u p.2))) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          have hsum : 0 < u p.1 + u p.2 := add_pos (hu p.1) (hu p.2)
          rw [show
              Real.log (btFraction u p.1 p.2) =
                Real.log (u p.1) - Real.log (u p.1 + u p.2) by
                unfold btFraction
                rw [Real.log_div (hu p.1).ne' hsum.ne']]
    _ =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 * Real.log (u p.1)) -
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 * Real.log (u p.1 + u p.2)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro p _hp
          ring
    _ =
        Finset.sum Finset.univ (fun x =>
          fordWinCount c x * Real.log (u x)) -
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 * Real.log (u p.1 + u p.2)) := by
          congr 1
          rw [← sum_univ_erase_eq_sum_offDiag
            (fun x y => c x y * Real.log (u x))]
          refine Finset.sum_congr rfl ?_
          intro x _hx
          unfold fordWinCount
          rw [Finset.sum_mul]

/-- The denominator part of the BT objective only depends on unordered pair
totals. -/
lemma pairDenom_sum_eq_of_same_pairTotal
    {c d : α → α → ℝ} {u : α → ℝ}
    (hPair : ∀ x y : α, fordPairTotal c x y = fordPairTotal d x y) :
    Finset.sum Finset.univ.offDiag (fun p : α × α =>
        c p.1 p.2 * Real.log (u p.1 + u p.2)) =
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        d p.1 p.2 * Real.log (u p.1 + u p.2)) := by
  let Dc : ℝ := Finset.sum Finset.univ.offDiag (fun p : α × α =>
    c p.1 p.2 * Real.log (u p.1 + u p.2))
  let Dd : ℝ := Finset.sum Finset.univ.offDiag (fun p : α × α =>
    d p.1 p.2 * Real.log (u p.1 + u p.2))
  have hswapc :
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        c p.2 p.1 * Real.log (u p.1 + u p.2)) = Dc := by
    dsimp [Dc]
    simpa [add_comm] using
      (sum_offDiag_swap (fun x y : α =>
        c x y * Real.log (u x + u y)))
  have hswapd :
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        d p.2 p.1 * Real.log (u p.1 + u p.2)) = Dd := by
    dsimp [Dd]
    simpa [add_comm] using
      (sum_offDiag_swap (fun x y : α =>
        d x y * Real.log (u x + u y)))
  have htwoc :
      (2 : ℝ) * Dc =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          fordPairTotal c p.1 p.2 * Real.log (u p.1 + u p.2)) := by
    calc
      (2 : ℝ) * Dc = Dc + Dc := by ring
      _ =
        Dc + Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.2 p.1 * Real.log (u p.1 + u p.2)) := by
          rw [hswapc]
      _ =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 * Real.log (u p.1 + u p.2) +
            c p.2 p.1 * Real.log (u p.1 + u p.2)) := by
          dsimp [Dc]
          rw [Finset.sum_add_distrib]
      _ =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          fordPairTotal c p.1 p.2 * Real.log (u p.1 + u p.2)) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          unfold fordPairTotal
          ring
  have htwod :
      (2 : ℝ) * Dd =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          fordPairTotal d p.1 p.2 * Real.log (u p.1 + u p.2)) := by
    calc
      (2 : ℝ) * Dd = Dd + Dd := by ring
      _ =
        Dd + Finset.sum Finset.univ.offDiag (fun p : α × α =>
          d p.2 p.1 * Real.log (u p.1 + u p.2)) := by
          rw [hswapd]
      _ =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          d p.1 p.2 * Real.log (u p.1 + u p.2) +
            d p.2 p.1 * Real.log (u p.1 + u p.2)) := by
          dsimp [Dd]
          rw [Finset.sum_add_distrib]
      _ =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          fordPairTotal d p.1 p.2 * Real.log (u p.1 + u p.2)) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          unfold fordPairTotal
          ring
  have hpair_sum :
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
          fordPairTotal c p.1 p.2 * Real.log (u p.1 + u p.2)) =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          fordPairTotal d p.1 p.2 * Real.log (u p.1 + u p.2)) := by
    refine Finset.sum_congr rfl ?_
    intro p _hp
    rw [hPair p.1 p.2]
  have htwo : (2 : ℝ) * Dc = (2 : ℝ) * Dd := by
    rw [htwoc, htwod, hpair_sum]
  dsimp [Dc, Dd] at htwo ⊢
  nlinarith

/-- If two count matrices have the same row win counts and unordered pair
totals, they give the same Bradley--Terry objective at every positive vector. -/
lemma btObjective_eq_of_same_pairTotal_winCount
    {c d : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hPair : ∀ x y : α, fordPairTotal c x y = fordPairTotal d x y)
    (hWin : ∀ x : α, fordWinCount c x = fordWinCount d x) :
    btObjective c u = btObjective d u := by
  have hwin_sum :
      Finset.sum Finset.univ (fun x : α =>
          fordWinCount c x * Real.log (u x)) =
        Finset.sum Finset.univ (fun x : α =>
          fordWinCount d x * Real.log (u x)) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [hWin x]
  have hdenom :=
    pairDenom_sum_eq_of_same_pairTotal (u := u) hPair
  calc
    btObjective c u =
        Finset.sum Finset.univ (fun x : α =>
          fordWinCount c x * Real.log (u x)) -
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 * Real.log (u p.1 + u p.2)) :=
          btObjective_eq_winCount_log_sub_pairDenom hu
    _ =
        Finset.sum Finset.univ (fun x : α =>
          fordWinCount d x * Real.log (u x)) -
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          d p.1 p.2 * Real.log (u p.1 + u p.2)) := by
          rw [hwin_sum, hdenom]
    _ = btObjective d u :=
          (btObjective_eq_winCount_log_sub_pairDenom hu).symm

/-- Ford's synthetic comparison matrix from the uniqueness proof: the original
unordered pair total is redistributed according to the Bradley--Terry
probability generated by `u`. -/
noncomputable def fordSyntheticCount
    (c : α → α → ℝ) (u : α → ℝ) (x y : α) : ℝ :=
  fordPairTotal c x y * btFraction u x y

omit [Fintype α] [DecidableEq α] in
lemma fordPairTotal_comm
    (c : α → α → ℝ) (x y : α) :
    fordPairTotal c y x = fordPairTotal c x y := by
  unfold fordPairTotal
  ring

omit [Fintype α] [DecidableEq α] in
lemma fordPairTotal_pos_of_count_pos
    {c : α → α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    {x y : α}
    (hxy : 0 < c x y) :
    0 < fordPairTotal c x y := by
  unfold fordPairTotal
  exact add_pos_of_pos_of_nonneg hxy (hc y x)

omit [Fintype α] [DecidableEq α] in
/-- Bradley--Terry fractions are monotone in the corresponding strength
ratio. -/
lemma btFraction_le_of_ratio_le
    {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    {x y : α}
    (h : u x / v x ≤ u y / v y) :
    btFraction u x y ≤ btFraction v x y := by
  have huxy : 0 < u x + u y := add_pos (hu x) (hu y)
  have hvxy : 0 < v x + v y := add_pos (hv x) (hv y)
  have hcross : u x * v y ≤ u y * v x := by
    have hmul :
        (v x * v y) * (u x / v x) ≤
          (v x * v y) * (u y / v y) :=
      mul_le_mul_of_nonneg_left h
        (mul_nonneg (hv x).le (hv y).le)
    calc
      u x * v y = (v x * v y) * (u x / v x) := by
        field_simp [(hv x).ne']
      _ ≤ (v x * v y) * (u y / v y) := hmul
      _ = u y * v x := by
        field_simp [(hv y).ne']
  unfold btFraction
  field_simp [huxy.ne', hvxy.ne']
  nlinarith

omit [Fintype α] [DecidableEq α] in
/-- If `x` has weakly larger `u/v` ratio than `y`, then the fitted probability
of `x` under `v` is at most its fitted probability under `u`. -/
lemma btFraction_le_of_ratio_ge
    {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    {x y : α}
    (h : u y / v y ≤ u x / v x) :
    btFraction v x y ≤ btFraction u x y := by
  have huxy : 0 < u x + u y := add_pos (hu x) (hu y)
  have hvxy : 0 < v x + v y := add_pos (hv x) (hv y)
  have hcross : u y * v x ≤ u x * v y := by
    have hmul :
        (v x * v y) * (u y / v y) ≤
          (v x * v y) * (u x / v x) :=
      mul_le_mul_of_nonneg_left h
        (mul_nonneg (hv x).le (hv y).le)
    calc
      u y * v x = (v x * v y) * (u y / v y) := by
        field_simp [(hv y).ne']
      _ ≤ (v x * v y) * (u x / v x) := hmul
      _ = u x * v y := by
        field_simp [(hv x).ne']
  unfold btFraction
  field_simp [huxy.ne', hvxy.ne']
  nlinarith

omit [Fintype α] [DecidableEq α] in
/-- Equality of Bradley--Terry fractions is equality of the corresponding
strength ratios. -/
lemma ratio_eq_of_btFraction_eq
    {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    {x y : α}
    (hfrac : btFraction u x y = btFraction v x y) :
    u x / v x = u y / v y := by
  have huxy : 0 < u x + u y := add_pos (hu x) (hu y)
  have hvxy : 0 < v x + v y := add_pos (hv x) (hv y)
  have hcross : u x * v y = u y * v x := by
    unfold btFraction at hfrac
    field_simp [huxy.ne', hvxy.ne'] at hfrac
    nlinarith
  field_simp [(hv x).ne', (hv y).ne']
  nlinarith

omit [Fintype α] [DecidableEq α] in
/-- Ford's synthetic matrix preserves every unordered pair total. -/
lemma fordPairTotal_fordSyntheticCount
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) (x y : α) :
    fordPairTotal (fordSyntheticCount c u) x y =
      fordPairTotal c x y := by
  unfold fordPairTotal fordSyntheticCount
  calc
    (c x y + c y x) * btFraction u x y +
        (c y x + c x y) * btFraction u y x =
      (c x y + c y x) *
        (btFraction u x y + btFraction u y x) := by
        ring
    _ = c x y + c y x := by
        rw [btFraction_add_swap_eq_one hu x y]
        ring

omit [Fintype α] [DecidableEq α] in
/-- Synthetic matrices generated from the same original count matrix preserve the
same unordered pair totals. -/
lemma fordPairTotal_fordSyntheticCount_eq_of_same_base
    {c : α → α → ℝ} {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    (x y : α) :
    fordPairTotal (fordSyntheticCount c u) x y =
      fordPairTotal (fordSyntheticCount c v) x y := by
  rw [fordPairTotal_fordSyntheticCount hu,
    fordPairTotal_fordSyntheticCount hv]

omit [Fintype α] [DecidableEq α] in
/-- Every synthetic directed count is the Bradley--Terry expected count for the
synthetic matrix's own unordered pair total. -/
lemma fordSyntheticCount_eq_pairTotal_mul_btFraction
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) (x y : α) :
    fordSyntheticCount c u x y =
      fordPairTotal (fordSyntheticCount c u) x y * btFraction u x y := by
  rw [fordPairTotal_fordSyntheticCount hu]
  rfl

omit [Fintype α] [DecidableEq α] in
/-- Ford's synthetic matrix has Bradley--Terry odds ratios for the strength
vector that generated it, stated without division by synthetic counts. -/
lemma fordSyntheticCount_mul_strength_swap
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) (x y : α) :
    fordSyntheticCount c u x y * u y =
      fordSyntheticCount c u y x * u x := by
  unfold fordSyntheticCount fordPairTotal btFraction
  have hxy : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
  field_simp [hxy, add_comm]
  ring

omit [Fintype α] [DecidableEq α] in
/-- For a single unordered pair, Ford's synthetic directed counts generated by
`u` have no larger Bradley--Terry log-likelihood at any other positive vector
`v` than at `u`. -/
lemma fordSyntheticPairLogLikelihood_le_self
    {c : α → α → ℝ} {u v : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    (x y : α) :
    fordSyntheticCount c u x y * Real.log (btFraction v x y) +
        fordSyntheticCount c u y x * Real.log (btFraction v y x) ≤
      fordSyntheticCount c u x y * Real.log (btFraction u x y) +
        fordSyntheticCount c u y x * Real.log (btFraction u y x) := by
  let T : ℝ := fordPairTotal c x y
  let p : ℝ := btFraction u x y
  let q : ℝ := btFraction v x y
  have hT : 0 ≤ T := by
    dsimp [T, fordPairTotal]
    exact add_nonneg (hc x y) (hc y x)
  have hp0 : 0 < p := by
    dsimp [p]
    exact btFraction_pos_of_pos hu x y
  have hp1 : p < 1 := by
    dsimp [p]
    exact btFraction_lt_one_of_pos hu x y
  have hq0 : 0 < q := by
    dsimp [q]
    exact btFraction_pos_of_pos hv x y
  have hq1 : q < 1 := by
    dsimp [q]
    exact btFraction_lt_one_of_pos hv x y
  have hupair : btFraction u y x = 1 - btFraction u x y := by
    have hsum := btFraction_add_swap_eq_one hu x y
    linarith
  have hvpair : btFraction v y x = 1 - btFraction v x y := by
    have hsum := btFraction_add_swap_eq_one hv x y
    linarith
  have hbern := bernoulliLogLikelihood_le_self hp0 hp1 hq0 hq1
  calc
    fordSyntheticCount c u x y * Real.log (btFraction v x y) +
        fordSyntheticCount c u y x * Real.log (btFraction v y x)
        =
      T * (p * Real.log q + (1 - p) * Real.log (1 - q)) := by
        unfold fordSyntheticCount
        dsimp [T, p, q]
        rw [fordPairTotal_comm c x y, hupair, hvpair]
        ring
    _ ≤ T * (p * Real.log p + (1 - p) * Real.log (1 - p)) :=
        mul_le_mul_of_nonneg_left hbern hT
    _ =
      fordSyntheticCount c u x y * Real.log (btFraction u x y) +
        fordSyntheticCount c u y x * Real.log (btFraction u y x) := by
        unfold fordSyntheticCount
        dsimp [T, p]
        rw [fordPairTotal_comm c x y, hupair]
        ring

omit [Fintype α] [DecidableEq α] in
/-- Strict pairwise form of Ford's synthetic likelihood inequality.  A positive
unordered pair total and a different Bradley--Terry fraction force a strict
drop in the pair's likelihood contribution. -/
lemma fordSyntheticPairLogLikelihood_lt_self_of_fraction_ne
    {c : α → α → ℝ} {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    {x y : α}
    (hT : 0 < fordPairTotal c x y)
    (hfrac : btFraction u x y ≠ btFraction v x y) :
    fordSyntheticCount c u x y * Real.log (btFraction v x y) +
        fordSyntheticCount c u y x * Real.log (btFraction v y x) <
      fordSyntheticCount c u x y * Real.log (btFraction u x y) +
        fordSyntheticCount c u y x * Real.log (btFraction u y x) := by
  let T : ℝ := fordPairTotal c x y
  let p : ℝ := btFraction u x y
  let q : ℝ := btFraction v x y
  have hp0 : 0 < p := by
    dsimp [p]
    exact btFraction_pos_of_pos hu x y
  have hp1 : p < 1 := by
    dsimp [p]
    exact btFraction_lt_one_of_pos hu x y
  have hq0 : 0 < q := by
    dsimp [q]
    exact btFraction_pos_of_pos hv x y
  have hq1 : q < 1 := by
    dsimp [q]
    exact btFraction_lt_one_of_pos hv x y
  have hpq : p ≠ q := by
    dsimp [p, q]
    exact hfrac
  have hupair : btFraction u y x = 1 - btFraction u x y := by
    have hsum := btFraction_add_swap_eq_one hu x y
    linarith
  have hvpair : btFraction v y x = 1 - btFraction v x y := by
    have hsum := btFraction_add_swap_eq_one hv x y
    linarith
  have hbern := bernoulliLogLikelihood_lt_self_of_ne
    hp0 hp1 hq0 hq1 hpq
  calc
    fordSyntheticCount c u x y * Real.log (btFraction v x y) +
        fordSyntheticCount c u y x * Real.log (btFraction v y x)
        =
      T * (p * Real.log q + (1 - p) * Real.log (1 - q)) := by
        unfold fordSyntheticCount
        dsimp [T, p, q]
        rw [fordPairTotal_comm c x y, hupair, hvpair]
        ring
    _ < T * (p * Real.log p + (1 - p) * Real.log (1 - p)) :=
        mul_lt_mul_of_pos_left hbern hT
    _ =
      fordSyntheticCount c u x y * Real.log (btFraction u x y) +
        fordSyntheticCount c u y x * Real.log (btFraction u y x) := by
        unfold fordSyntheticCount
        dsimp [T, p]
        rw [fordPairTotal_comm c x y, hupair]
        ring

omit [Fintype α] [DecidableEq α] in
/-- Equality case of the pairwise synthetic likelihood inequality. -/
lemma fordSyntheticPairLogLikelihood_eq_self_iff
    {c : α → α → ℝ} {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    {x y : α}
    (hT : 0 < fordPairTotal c x y) :
    fordSyntheticCount c u x y * Real.log (btFraction v x y) +
        fordSyntheticCount c u y x * Real.log (btFraction v y x) =
        fordSyntheticCount c u x y * Real.log (btFraction u x y) +
          fordSyntheticCount c u y x * Real.log (btFraction u y x) ↔
      btFraction u x y = btFraction v x y := by
  constructor
  · intro h
    by_contra hfrac_eq
    have hfrac : btFraction u x y ≠ btFraction v x y := hfrac_eq
    have hlt := fordSyntheticPairLogLikelihood_lt_self_of_fraction_ne
      hu hv hT hfrac
    rw [h] at hlt
    exact (lt_self_iff_false _).mp hlt
  · intro h
    have hupair : btFraction u y x = 1 - btFraction u x y := by
      have hsum := btFraction_add_swap_eq_one hu x y
      linarith
    have hvpair : btFraction v y x = 1 - btFraction v x y := by
      have hsum := btFraction_add_swap_eq_one hv x y
      linarith
    have hswap : btFraction u y x = btFraction v y x := by
      rw [hupair, hvpair, h]
    rw [h, hswap]

/-- Ford's synthetic count matrix generated by `u` has no larger BT
log-likelihood at any other positive vector `v` than at `u`. This sums the
pairwise Bernoulli inequality over all directed off-diagonal comparisons. -/
theorem btObjective_fordSyntheticCount_le_self
    {c : α → α → ℝ} {u v : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x) :
    btObjective (fordSyntheticCount c u) v ≤
      btObjective (fordSyntheticCount c u) u := by
  let Fv : α → α → ℝ := fun x y =>
    fordSyntheticCount c u x y * Real.log (btFraction v x y)
  let Fu : α → α → ℝ := fun x y =>
    fordSyntheticCount c u x y * Real.log (btFraction u x y)
  have hpair :
      ∀ p ∈ Finset.univ.offDiag,
        Fv p.1 p.2 + Fv p.2 p.1 ≤ Fu p.1 p.2 + Fu p.2 p.1 := by
    intro p _hp
    exact fordSyntheticPairLogLikelihood_le_self hc hu hv p.1 p.2
  have hsum :
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        Fv p.1 p.2 + Fv p.2 p.1) ≤
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        Fu p.1 p.2 + Fu p.2 p.1) :=
    Finset.sum_le_sum hpair
  have hswapv :
      Finset.sum Finset.univ.offDiag (fun p : α × α => Fv p.2 p.1) =
        Finset.sum Finset.univ.offDiag (fun p : α × α => Fv p.1 p.2) :=
    sum_offDiag_swap Fv
  have hswapu :
      Finset.sum Finset.univ.offDiag (fun p : α × α => Fu p.2 p.1) =
        Finset.sum Finset.univ.offDiag (fun p : α × α => Fu p.1 p.2) :=
    sum_offDiag_swap Fu
  have htwo :
      (2 : ℝ) * Finset.sum Finset.univ.offDiag
          (fun p : α × α => Fv p.1 p.2) ≤
        (2 : ℝ) * Finset.sum Finset.univ.offDiag
          (fun p : α × α => Fu p.1 p.2) := by
    calc
      (2 : ℝ) * Finset.sum Finset.univ.offDiag
          (fun p : α × α => Fv p.1 p.2)
          =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          Fv p.1 p.2 + Fv p.2 p.1) := by
          rw [Finset.sum_add_distrib, hswapv]
          ring
      _ ≤
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          Fu p.1 p.2 + Fu p.2 p.1) := hsum
      _ =
        (2 : ℝ) * Finset.sum Finset.univ.offDiag
          (fun p : α × α => Fu p.1 p.2) := by
          rw [Finset.sum_add_distrib, hswapu]
          ring
  have hmain :
      Finset.sum Finset.univ.offDiag (fun p : α × α => Fv p.1 p.2) ≤
        Finset.sum Finset.univ.offDiag (fun p : α × α => Fu p.1 p.2) := by
    nlinarith
  calc
    btObjective (fordSyntheticCount c u) v =
        Finset.sum Finset.univ.offDiag (fun p : α × α => Fv p.1 p.2) := by
          simpa [Fv] using
            btObjective_eq_sum_offDiag (fordSyntheticCount c u) v
    _ ≤ Finset.sum Finset.univ.offDiag (fun p : α × α => Fu p.1 p.2) := hmain
    _ = btObjective (fordSyntheticCount c u) u := by
          simpa [Fu] using
            (btObjective_eq_sum_offDiag (fordSyntheticCount c u) u).symm

/-- Strict synthetic log-likelihood inequality summed over all comparisons:
one positive unordered pair with a different Bradley--Terry fraction forces the
whole synthetic objective to be strictly smaller. -/
theorem btObjective_fordSyntheticCount_lt_self_of_exists_fraction_ne
    {c : α → α → ℝ} {u v : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    (hdiff : ∃ p : α × α, p ∈ Finset.univ.offDiag ∧
      0 < fordPairTotal c p.1 p.2 ∧
        btFraction u p.1 p.2 ≠ btFraction v p.1 p.2) :
    btObjective (fordSyntheticCount c u) v <
      btObjective (fordSyntheticCount c u) u := by
  let Fv : α → α → ℝ := fun x y =>
    fordSyntheticCount c u x y * Real.log (btFraction v x y)
  let Fu : α → α → ℝ := fun x y =>
    fordSyntheticCount c u x y * Real.log (btFraction u x y)
  have hpair :
      ∀ p ∈ Finset.univ.offDiag,
        Fv p.1 p.2 + Fv p.2 p.1 ≤ Fu p.1 p.2 + Fu p.2 p.1 := by
    intro p _hp
    exact fordSyntheticPairLogLikelihood_le_self hc hu hv p.1 p.2
  have hpair_strict :
      ∃ p ∈ Finset.univ.offDiag,
        Fv p.1 p.2 + Fv p.2 p.1 < Fu p.1 p.2 + Fu p.2 p.1 := by
    rcases hdiff with ⟨p, hp, hT, hfrac⟩
    exact ⟨p, hp,
      fordSyntheticPairLogLikelihood_lt_self_of_fraction_ne hu hv hT hfrac⟩
  have hsum :
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        Fv p.1 p.2 + Fv p.2 p.1) <
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
        Fu p.1 p.2 + Fu p.2 p.1) :=
    Finset.sum_lt_sum hpair hpair_strict
  have hswapv :
      Finset.sum Finset.univ.offDiag (fun p : α × α => Fv p.2 p.1) =
        Finset.sum Finset.univ.offDiag (fun p : α × α => Fv p.1 p.2) :=
    sum_offDiag_swap Fv
  have hswapu :
      Finset.sum Finset.univ.offDiag (fun p : α × α => Fu p.2 p.1) =
        Finset.sum Finset.univ.offDiag (fun p : α × α => Fu p.1 p.2) :=
    sum_offDiag_swap Fu
  have htwo :
      (2 : ℝ) * Finset.sum Finset.univ.offDiag
          (fun p : α × α => Fv p.1 p.2) <
        (2 : ℝ) * Finset.sum Finset.univ.offDiag
          (fun p : α × α => Fu p.1 p.2) := by
    calc
      (2 : ℝ) * Finset.sum Finset.univ.offDiag
          (fun p : α × α => Fv p.1 p.2)
          =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          Fv p.1 p.2 + Fv p.2 p.1) := by
          rw [Finset.sum_add_distrib, hswapv]
          ring
      _ <
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          Fu p.1 p.2 + Fu p.2 p.1) := hsum
      _ =
        (2 : ℝ) * Finset.sum Finset.univ.offDiag
          (fun p : α × α => Fu p.1 p.2) := by
          rw [Finset.sum_add_distrib, hswapu]
          ring
  have hmain :
      Finset.sum Finset.univ.offDiag (fun p : α × α => Fv p.1 p.2) <
        Finset.sum Finset.univ.offDiag (fun p : α × α => Fu p.1 p.2) := by
    nlinarith
  calc
    btObjective (fordSyntheticCount c u) v =
        Finset.sum Finset.univ.offDiag (fun p : α × α => Fv p.1 p.2) := by
          simpa [Fv] using
            btObjective_eq_sum_offDiag (fordSyntheticCount c u) v
    _ < Finset.sum Finset.univ.offDiag (fun p : α × α => Fu p.1 p.2) := hmain
    _ = btObjective (fordSyntheticCount c u) u := by
          simpa [Fu] using
            (btObjective_eq_sum_offDiag (fordSyntheticCount c u) u).symm

/-- Non-unique full-support log-likelihood maximizer form for Ford's synthetic
matrix. The uniqueness part of Ford/Zermelo is still the remaining analytic
input; this theorem internalizes the maximizer inequality for the synthetic
matrix. -/
theorem fordSyntheticCount_fullSupportBTObjectiveMaximizer
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : IsFullSupportLottery u) :
    IsFullSupportLottery u ∧
      ∀ v : α → ℝ, IsFullSupportLottery v →
        btObjective (fordSyntheticCount c u) v ≤
          btObjective (fordSyntheticCount c u) u :=
  ⟨hu, fun v hv =>
    btObjective_fordSyntheticCount_le_self (u := u) (v := v) hc hu.1 hv.1⟩

omit [Fintype α] [DecidableEq α] in
lemma fordSyntheticCount_nonneg
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x) :
    ∀ x y : α, 0 ≤ fordSyntheticCount c u x y := by
  intro x y
  unfold fordSyntheticCount fordPairTotal
  exact mul_nonneg (add_nonneg (hc x y) (hc y x))
    (btFraction_pos_of_pos hu x y).le

omit [Fintype α] [DecidableEq α] in
lemma fordSyntheticCount_self_eq_zero
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : IsFordCountMatrix c) (x : α) :
    fordSyntheticCount c u x x = 0 := by
  unfold fordSyntheticCount fordPairTotal
  rw [hc.1 x]
  simp

omit [Fintype α] [DecidableEq α] in
/-- Ford's synthetic matrix satisfies the same basic nonnegative count-matrix
side conditions as the original matrix. -/
lemma fordSyntheticCount_isFordCountMatrix
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hu : ∀ x : α, 0 < u x) :
    IsFordCountMatrix (fordSyntheticCount c u) :=
  ⟨fordSyntheticCount_self_eq_zero hc,
    fordSyntheticCount_nonneg hc.2 hu⟩

omit [Fintype α] [DecidableEq α] in
lemma fordSyntheticCount_pos_of_count_pos
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    {x y : α}
    (hxy : 0 < c x y) :
    0 < fordSyntheticCount c u x y := by
  unfold fordSyntheticCount fordPairTotal
  exact mul_pos (add_pos_of_pos_of_nonneg hxy (hc y x))
    (btFraction_pos_of_pos hu x y)

omit [Fintype α] [DecidableEq α] in
lemma fordSyntheticCount_reverse_pos_of_count_pos
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    {x y : α}
    (hxy : 0 < c x y) :
    0 < fordSyntheticCount c u y x := by
  unfold fordSyntheticCount fordPairTotal
  exact mul_pos (add_pos_of_nonneg_of_pos (hc y x) hxy)
    (btFraction_pos_of_pos hu y x)

omit [Fintype α] [DecidableEq α] in
/-- Ford strong connectivity is preserved by passing from a count matrix to
Ford's synthetic matrix at a positive strength vector. -/
lemma FordStronglyConnected_fordSyntheticCount
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    (hconn : FordStronglyConnected c) :
    FordStronglyConnected (fordSyntheticCount c u) := by
  refine FordStronglyConnected_mono ?_ hconn
  intro x y hxy
  exact fordSyntheticCount_pos_of_count_pos hc hu hxy

omit [Fintype α] [DecidableEq α] in
/-- Ford's original partition assumption is preserved by passing from a count
matrix to Ford's synthetic matrix at a positive strength vector. -/
lemma FordPartitionAssumption_fordSyntheticCount
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    (hpart : FordPartitionAssumption c) :
    FordPartitionAssumption (fordSyntheticCount c u) :=
  FordPartitionAssumption_mono
    (fun _ _ hxy => fordSyntheticCount_pos_of_count_pos hc hu hxy)
    hpart

/-- Ford's multiplicative likelihood objective, in directed-pair form.  This
is convenient for the boundary part of Ford's existence proof, where a single
zero factor forces the whole product to be zero. -/
noncomputable def fordBTProductObjective
    (c : α → α → ℝ) (u : α → ℝ) : ℝ :=
  Finset.prod Finset.univ (fun x =>
    Finset.prod (Finset.univ.erase x) (fun y =>
      (btFraction u x y) ^ (c x y)))

omit [Fintype α] [DecidableEq α] in
/-- The Bradley--Terry fraction is continuous on the positive orthant. -/
lemma continuousOn_btFraction_fullSupport
    (x y : α) :
    ContinuousOn (fun u : α → ℝ => btFraction u x y)
      {u : α → ℝ | ∀ z : α, 0 < u z} := by
  unfold btFraction
  exact ((continuous_apply x).continuousOn.div
    ((continuous_apply x).continuousOn.add
      (continuous_apply y).continuousOn)
    (fun u hu => (add_pos (hu x) (hu y)).ne'))

omit [Fintype α] [DecidableEq α] in
/-- Pair-local continuity of a Bradley--Terry fraction whenever the pair
denominator is nonzero. -/
lemma continuousAt_btFraction_of_pair_sum_ne
    {u : α → ℝ} {x y : α}
    (hden : u x + u y ≠ 0) :
    ContinuousAt (fun v : α → ℝ => btFraction v x y) u := by
  unfold btFraction
  exact (continuous_apply x).continuousAt.div
    ((continuous_apply x).continuousAt.add
      (continuous_apply y).continuousAt)
    hden

omit [Fintype α] [DecidableEq α] in
/-- At a boundary point where `x` has zero strength and `y` has positive
strength, the Bradley--Terry fraction for `x` against `y` tends to zero. -/
lemma tendsto_btFraction_nhds_zero_of_left_zero_right_pos
    {u : α → ℝ} {x y : α}
    (hx : u x = 0) (hy : 0 < u y) :
    Filter.Tendsto (fun v : α → ℝ => btFraction v x y) (𝓝 u) (𝓝 0) := by
  have hden : u x + u y ≠ 0 := by
    rw [hx]
    simpa using hy.ne'
  have hcont := continuousAt_btFraction_of_pair_sum_ne
    (u := u) (x := x) (y := y) hden
  have hval : btFraction u x y = 0 :=
    btFraction_eq_zero_of_left_eq_zero hx
  simpa [hval] using hcont.tendsto

omit [Fintype α] [DecidableEq α] in
/-- At a Ford boundary-crossing edge, the corresponding positive-count product
factor tends to zero. -/
lemma tendsto_fordEdgeFactor_nhds_zero_of_boundary_crossing
    {c : α → α → ℝ} {u : α → ℝ} {x y : α}
    (hxy : fordCountEdge c x y)
    (hx : u x = 0) (hy : 0 < u y) :
    Filter.Tendsto (fun v : α → ℝ => (btFraction v x y) ^ (c x y))
      (𝓝 u) (𝓝 0) := by
  have hfrac :=
    tendsto_btFraction_nhds_zero_of_left_zero_right_pos
      (u := u) (x := x) (y := y) hx hy
  have hpow :
      ContinuousAt (fun t : ℝ => t ^ (c x y)) 0 :=
    Real.continuousAt_rpow_const 0 (c x y) (Or.inr hxy.2.le)
  have hzero : (0 : ℝ) ^ (c x y) = 0 :=
    Real.zero_rpow hxy.2.ne'
  simpa [Function.comp_def, hzero] using hpow.tendsto.comp hfrac

/-- Ford's multiplicative likelihood is continuous on the positive orthant.
The closed-simplex boundary continuity needed for Ford's compactness proof is
separate: the fraction convention is not generally continuous at points where
both coordinates of a compared pair vanish. -/
lemma continuousOn_fordBTProductObjective_fullSupport
    (c : α → α → ℝ) :
    ContinuousOn (fun u : α → ℝ => fordBTProductObjective c u)
      {u : α → ℝ | ∀ x : α, 0 < u x} := by
  classical
  unfold fordBTProductObjective
  refine continuousOn_finset_prod Finset.univ ?_
  intro x _hx
  refine continuousOn_finset_prod (Finset.univ.erase x) ?_
  intro y _hy
  refine (continuousOn_btFraction_fullSupport x y).rpow_const ?_
  intro u hu
  exact Or.inl (btFraction_pos_of_pos hu x y).ne'

omit [Fintype α] [DecidableEq α] in
/-- Bradley--Terry fractions are nonnegative for nonnegative strength
coordinates, using Lean's harmless `0 / 0 = 0` convention on the boundary. -/
lemma btFraction_nonneg_of_nonneg
    {u : α → ℝ} {x y : α}
    (hx : 0 ≤ u x) (hy : 0 ≤ u y) :
    0 ≤ btFraction u x y := by
  unfold btFraction
  by_cases hden : u x + u y = 0
  · simp [hden]
  · have hdenpos : 0 < u x + u y :=
      lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hden)
    exact div_nonneg hx hdenpos.le

omit [Fintype α] [DecidableEq α] in
/-- Bradley--Terry fractions are at most one for nonnegative strength
coordinates. -/
lemma btFraction_le_one_of_nonneg
    {u : α → ℝ} {x y : α}
    (hx : 0 ≤ u x) (hy : 0 ≤ u y) :
    btFraction u x y ≤ 1 := by
  unfold btFraction
  by_cases hden : u x + u y = 0
  · simp [hden]
  · have hdenpos : 0 < u x + u y :=
      lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hden)
    calc
      u x / (u x + u y) ≤ (u x + u y) / (u x + u y) :=
        div_le_div_of_nonneg_right
          (le_add_of_nonneg_right hy) hdenpos.le
      _ = 1 := div_self hdenpos.ne'

/-- Ford's multiplicative likelihood is positive on the positive orthant. -/
lemma fordBTProductObjective_pos_of_pos
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    0 < fordBTProductObjective c u := by
  classical
  unfold fordBTProductObjective
  refine Finset.prod_pos ?_
  intro x _hx
  refine Finset.prod_pos ?_
  intro y _hy
  exact Real.rpow_pos_of_pos (btFraction_pos_of_pos hu x y) (c x y)

/-- Ford's multiplicative likelihood is bounded by `1` for nonnegative count
matrices on the positive orthant. -/
lemma fordBTProductObjective_le_one_of_pos
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x) :
    fordBTProductObjective c u ≤ 1 := by
  classical
  unfold fordBTProductObjective
  have hrow_nonneg :
      ∀ x : α, x ∈ Finset.univ →
        0 ≤ Finset.prod (Finset.univ.erase x) (fun y =>
          (btFraction u x y) ^ (c x y)) := by
    intro x _hx
    refine Finset.prod_nonneg ?_
    intro y _hy
    exact Real.rpow_nonneg (btFraction_pos_of_pos hu x y).le (c x y)
  calc
    Finset.prod Finset.univ (fun x =>
        Finset.prod (Finset.univ.erase x) (fun y =>
          (btFraction u x y) ^ (c x y)))
        ≤ Finset.prod Finset.univ (fun _x : α => (1 : ℝ)) := by
          refine Finset.prod_le_prod hrow_nonneg ?_
          intro x _hx
          calc
            Finset.prod (Finset.univ.erase x) (fun y =>
                (btFraction u x y) ^ (c x y))
                ≤ Finset.prod (Finset.univ.erase x) (fun _y : α => (1 : ℝ)) := by
                  refine Finset.prod_le_prod ?_ ?_
                  · intro y _hy
                    exact Real.rpow_nonneg
                      (btFraction_pos_of_pos hu x y).le (c x y)
                  · intro y _hy
                    exact Real.rpow_le_one
                      (btFraction_pos_of_pos hu x y).le
                      (btFraction_lt_one_of_pos hu x y).le
                      (hc x y)
            _ = 1 := by simp
    _ = 1 := by simp

/-- Ford's multiplicative likelihood is nonnegative on the closed nonnegative
orthant for nonnegative count matrices. -/
lemma fordBTProductObjective_nonneg_of_nonneg
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 ≤ u x) :
    0 ≤ fordBTProductObjective c u := by
  classical
  unfold fordBTProductObjective
  refine Finset.prod_nonneg ?_
  intro x _hx
  refine Finset.prod_nonneg ?_
  intro y _hy
  exact Real.rpow_nonneg
    (btFraction_nonneg_of_nonneg (hu x) (hu y)) (c x y)

/-- Ford's multiplicative likelihood is bounded by `1` on the closed
nonnegative orthant for nonnegative count matrices. -/
lemma fordBTProductObjective_le_one_of_nonneg
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 ≤ u x) :
    fordBTProductObjective c u ≤ 1 := by
  classical
  unfold fordBTProductObjective
  have hrow_nonneg :
      ∀ x : α, x ∈ Finset.univ →
        0 ≤ Finset.prod (Finset.univ.erase x) (fun y =>
          (btFraction u x y) ^ (c x y)) := by
    intro x _hx
    refine Finset.prod_nonneg ?_
    intro y _hy
    exact Real.rpow_nonneg
      (btFraction_nonneg_of_nonneg (hu x) (hu y)) (c x y)
  calc
    Finset.prod Finset.univ (fun x =>
        Finset.prod (Finset.univ.erase x) (fun y =>
          (btFraction u x y) ^ (c x y)))
        ≤ Finset.prod Finset.univ (fun _x : α => (1 : ℝ)) := by
          refine Finset.prod_le_prod hrow_nonneg ?_
          intro x _hx
          calc
            Finset.prod (Finset.univ.erase x) (fun y =>
                (btFraction u x y) ^ (c x y))
                ≤ Finset.prod (Finset.univ.erase x) (fun _y : α => (1 : ℝ)) := by
                  refine Finset.prod_le_prod ?_ ?_
                  · intro y _hy
                    exact Real.rpow_nonneg
                      (btFraction_nonneg_of_nonneg (hu x) (hu y)) (c x y)
                  · intro y _hy
                    exact Real.rpow_le_one
                      (btFraction_nonneg_of_nonneg (hu x) (hu y))
                      (btFraction_le_one_of_nonneg (hu x) (hu y))
                      (hc x y)
            _ = 1 := by simp
    _ = 1 := by simp

/-- Off-diagonal directed-pair form of Ford's product objective. -/
lemma fordBTProductObjective_eq_prod_offDiag
    (c : α → α → ℝ) (u : α → ℝ) :
    fordBTProductObjective c u =
      Finset.prod Finset.univ.offDiag (fun p : α × α =>
        (btFraction u p.1 p.2) ^ (c p.1 p.2)) := by
  classical
  unfold fordBTProductObjective
  exact prod_univ_erase_eq_prod_offDiag
    (fun x y : α => (btFraction u x y) ^ (c x y))

/-- On the closed nonnegative orthant, the whole Ford product objective is
bounded above by any one directed factor. -/
lemma fordBTProductObjective_le_edgeFactor_of_nonneg
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 ≤ u x)
    {a b : α} (hab : a ≠ b) :
    fordBTProductObjective c u ≤ (btFraction u a b) ^ (c a b) := by
  classical
  let f : α × α → ℝ := fun p =>
    (btFraction u p.1 p.2) ^ (c p.1 p.2)
  have hmem : (a, b) ∈ Finset.univ.offDiag := by
    simpa using hab
  have hfactor_nonneg : 0 ≤ f (a, b) :=
    Real.rpow_nonneg (btFraction_nonneg_of_nonneg (hu a) (hu b)) (c a b)
  have hrest_le_one :
      Finset.prod (Finset.univ.offDiag.erase (a, b)) f ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro p _hp
      exact Real.rpow_nonneg
        (btFraction_nonneg_of_nonneg (hu p.1) (hu p.2)) (c p.1 p.2)
    · intro p _hp
      exact Real.rpow_le_one
        (btFraction_nonneg_of_nonneg (hu p.1) (hu p.2))
        (btFraction_le_one_of_nonneg (hu p.1) (hu p.2))
        (hc p.1 p.2)
  have hprod :
      Finset.prod Finset.univ.offDiag f ≤ f (a, b) := by
    rw [← Finset.prod_erase_mul Finset.univ.offDiag f hmem]
    calc
      Finset.prod (Finset.univ.offDiag.erase (a, b)) f * f (a, b) ≤
          1 * f (a, b) :=
        mul_le_mul_of_nonneg_right hrest_le_one hfactor_nonneg
      _ = f (a, b) := by ring
  calc
    fordBTProductObjective c u =
        Finset.prod Finset.univ.offDiag f := by
          simpa [f] using fordBTProductObjective_eq_prod_offDiag c u
    _ ≤ f (a, b) := hprod
    _ = (btFraction u a b) ^ (c a b) := by
          simp [f]

/-- Ford's multiplicative likelihood is unchanged by multiplying all
strengths by the same positive scalar. -/
lemma fordBTProductObjective_scaled
    {c : α → α → ℝ} {u : α → ℝ} {a : ℝ}
    (ha : 0 < a)
    (hu : ∀ x : α, 0 < u x) :
    fordBTProductObjective c (fun x => a * u x) =
      fordBTProductObjective c u := by
  classical
  unfold fordBTProductObjective
  refine Finset.prod_congr rfl ?_
  intro x _hx
  refine Finset.prod_congr rfl ?_
  intro y _hy
  rw [btFraction_scaled ha hu x y]

/-- Ford simplex normalization does not change the multiplicative likelihood
of a positive Bradley--Terry vector. -/
lemma fordBTProductObjective_btNormalize
    [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    fordBTProductObjective c (btNormalize u) =
      fordBTProductObjective c u := by
  rw [btNormalize_eq_inv_sum_smul]
  exact fordBTProductObjective_scaled
    (one_div_pos.mpr (btNormalize_den_pos (α := α) hu)) hu

/-- On positive vectors, the logarithm of Ford's multiplicative likelihood is
the additive Bradley--Terry objective used by the DPO change of variables. -/
theorem Real_log_fordBTProductObjective_eq_btObjective
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    Real.log (fordBTProductObjective c u) = btObjective c u := by
  classical
  unfold fordBTProductObjective btObjective
  calc
    Real.log
        (Finset.prod Finset.univ (fun x =>
          Finset.prod (Finset.univ.erase x) (fun y =>
            (btFraction u x y) ^ (c x y))))
        =
      Finset.sum Finset.univ (fun x =>
        Real.log
          (Finset.prod (Finset.univ.erase x) (fun y =>
            (btFraction u x y) ^ (c x y)))) := by
          rw [Real.log_prod]
          intro x _hx
          exact (Finset.prod_pos (fun y _hy =>
            Real.rpow_pos_of_pos (btFraction_pos_of_pos hu x y) (c x y))).ne'
    _ =
      Finset.sum Finset.univ (fun x =>
        Finset.sum (Finset.univ.erase x) (fun y =>
          Real.log ((btFraction u x y) ^ (c x y)))) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [Real.log_prod]
          intro y _hy
          exact (Real.rpow_pos_of_pos
            (btFraction_pos_of_pos hu x y) (c x y)).ne'
    _ =
      Finset.sum Finset.univ (fun x =>
        Finset.sum (Finset.univ.erase x) (fun y =>
          c x y * Real.log (btFraction u x y))) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          refine Finset.sum_congr rfl ?_
          intro y _hy
          rw [Real.log_rpow (btFraction_pos_of_pos hu x y)]
    _ =
      Finset.sum Finset.univ (fun x =>
        Finset.sum (Finset.univ.erase x) (fun y =>
          c x y * Real.log (u x / (u x + u y)))) := by
          simp [btFraction]

/-- Product-likelihood form of the synthetic-matrix maximizer inequality. -/
theorem fordBTProductObjective_fordSyntheticCount_le_self
    {c : α → α → ℝ} {u v : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x) :
    fordBTProductObjective (fordSyntheticCount c u) v ≤
      fordBTProductObjective (fordSyntheticCount c u) u := by
  have hvpos :
      0 < fordBTProductObjective (fordSyntheticCount c u) v :=
    fordBTProductObjective_pos_of_pos hv
  have hupos :
      0 < fordBTProductObjective (fordSyntheticCount c u) u :=
    fordBTProductObjective_pos_of_pos hu
  have hlog :
      Real.log (fordBTProductObjective (fordSyntheticCount c u) v) ≤
        Real.log (fordBTProductObjective (fordSyntheticCount c u) u) := by
    calc
      Real.log (fordBTProductObjective (fordSyntheticCount c u) v) =
          btObjective (fordSyntheticCount c u) v :=
            Real_log_fordBTProductObjective_eq_btObjective hv
      _ ≤ btObjective (fordSyntheticCount c u) u :=
            btObjective_fordSyntheticCount_le_self hc hu hv
      _ = Real.log (fordBTProductObjective (fordSyntheticCount c u) u) :=
            (Real_log_fordBTProductObjective_eq_btObjective hu).symm
  exact (Real.log_le_log_iff hvpos hupos).mp hlog

/-- Product-likelihood strictness corresponding to
`btObjective_fordSyntheticCount_lt_self_of_exists_fraction_ne`. -/
theorem fordBTProductObjective_fordSyntheticCount_lt_self_of_exists_fraction_ne
    {c : α → α → ℝ} {u v : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    (hdiff : ∃ p : α × α, p ∈ Finset.univ.offDiag ∧
      0 < fordPairTotal c p.1 p.2 ∧
        btFraction u p.1 p.2 ≠ btFraction v p.1 p.2) :
    fordBTProductObjective (fordSyntheticCount c u) v <
      fordBTProductObjective (fordSyntheticCount c u) u := by
  have hvpos :
      0 < fordBTProductObjective (fordSyntheticCount c u) v :=
    fordBTProductObjective_pos_of_pos hv
  have hupos :
      0 < fordBTProductObjective (fordSyntheticCount c u) u :=
    fordBTProductObjective_pos_of_pos hu
  have hlog :
      Real.log (fordBTProductObjective (fordSyntheticCount c u) v) <
        Real.log (fordBTProductObjective (fordSyntheticCount c u) u) := by
    calc
      Real.log (fordBTProductObjective (fordSyntheticCount c u) v) =
          btObjective (fordSyntheticCount c u) v :=
            Real_log_fordBTProductObjective_eq_btObjective hv
      _ < btObjective (fordSyntheticCount c u) u :=
            btObjective_fordSyntheticCount_lt_self_of_exists_fraction_ne
              hc hu hv hdiff
      _ = Real.log (fordBTProductObjective (fordSyntheticCount c u) u) :=
            (Real_log_fordBTProductObjective_eq_btObjective hu).symm
  exact (Real.log_lt_log_iff hvpos hupos).mp hlog

/-- Non-unique full-support product-likelihood maximizer form for Ford's
synthetic matrix. -/
theorem fordSyntheticCount_fullSupportProductMaximizer
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hu : IsFullSupportLottery u) :
    IsFullSupportLottery u ∧
      ∀ v : α → ℝ, IsFullSupportLottery v →
        fordBTProductObjective (fordSyntheticCount c u) v ≤
          fordBTProductObjective (fordSyntheticCount c u) u :=
  ⟨hu, fun v hv =>
    fordBTProductObjective_fordSyntheticCount_le_self
      (u := u) (v := v) hc hu.1 hv.1⟩

/-- Ford's maximum-likelihood theorem is multiplicative in the original
paper. This predicate states the normalized product-likelihood form. -/
def HasFordNormalizedBTProductMaximizer
    (c : α → α → ℝ) (u : α → ℝ) : Prop :=
  IsFullSupportLottery u ∧
    (∀ v : α → ℝ, IsFullSupportLottery v →
      fordBTProductObjective c v ≤ fordBTProductObjective c u) ∧
      ∀ v : α → ℝ, IsFullSupportLottery v →
        (∀ w : α → ℝ, IsFullSupportLottery w →
          fordBTProductObjective c w ≤ fordBTProductObjective c v) →
            v = u

/-- A closed-simplex product-likelihood maximizer. Ford's proof first obtains
this kind of maximizer by compactness, then uses the boundary argument to show
it actually lies in the interior. -/
def HasFordClosedSimplexProductMaximizer
    (c : α → α → ℝ) (u : α → ℝ) : Prop :=
  IsLottery u ∧
    ∀ v : α → ℝ, IsLottery v →
      fordBTProductObjective c v ≤ fordBTProductObjective c u

/-- On the full-support simplex, Ford's product-likelihood maximizer statement
is equivalent to the log-likelihood maximizer statement used by the DPO layer. -/
theorem HasFordNormalizedBTProductMaximizer_iff_normalizedBTMaximizer
    {c : α → α → ℝ} {u : α → ℝ} :
    HasFordNormalizedBTProductMaximizer c u ↔
      HasFordNormalizedBTMaximizer c u := by
  constructor
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · intro v hv
      have hvpos := fordBTProductObjective_pos_of_pos (c := c) hv.1
      have hupos := fordBTProductObjective_pos_of_pos (c := c) h.1.1
      calc
        btObjective c v =
            Real.log (fordBTProductObjective c v) :=
              (Real_log_fordBTProductObjective_eq_btObjective hv.1).symm
        _ ≤ Real.log (fordBTProductObjective c u) :=
              (Real.log_le_log_iff hvpos hupos).mpr (h.2.1 v hv)
        _ = btObjective c u :=
              Real_log_fordBTProductObjective_eq_btObjective h.1.1
    · intro v hv hvmax
      apply h.2.2 v hv
      intro w hw
      have hwpos := fordBTProductObjective_pos_of_pos (c := c) hw.1
      have hvpos := fordBTProductObjective_pos_of_pos (c := c) hv.1
      have hlog :
          Real.log (fordBTProductObjective c w) ≤
            Real.log (fordBTProductObjective c v) := by
        calc
          Real.log (fordBTProductObjective c w) =
              btObjective c w :=
                Real_log_fordBTProductObjective_eq_btObjective hw.1
          _ ≤ btObjective c v := hvmax w hw
          _ = Real.log (fordBTProductObjective c v) :=
                (Real_log_fordBTProductObjective_eq_btObjective hv.1).symm
      exact (Real.log_le_log_iff hwpos hvpos).mp hlog
  · intro h
    refine ⟨h.1, ?_, ?_⟩
    · intro v hv
      have hvpos := fordBTProductObjective_pos_of_pos (c := c) hv.1
      have hupos := fordBTProductObjective_pos_of_pos (c := c) h.1.1
      have hlog :
          Real.log (fordBTProductObjective c v) ≤
            Real.log (fordBTProductObjective c u) := by
        calc
          Real.log (fordBTProductObjective c v) =
              btObjective c v :=
                Real_log_fordBTProductObjective_eq_btObjective hv.1
          _ ≤ btObjective c u := h.2.1 v hv
          _ = Real.log (fordBTProductObjective c u) :=
                (Real_log_fordBTProductObjective_eq_btObjective h.1.1).symm
      exact (Real.log_le_log_iff hvpos hupos).mp hlog
    · intro v hv hvmax
      apply h.2.2 v hv
      intro w hw
      have hwpos := fordBTProductObjective_pos_of_pos (c := c) hw.1
      have hvpos := fordBTProductObjective_pos_of_pos (c := c) hv.1
      calc
        btObjective c w =
            Real.log (fordBTProductObjective c w) :=
              (Real_log_fordBTProductObjective_eq_btObjective hw.1).symm
        _ ≤ Real.log (fordBTProductObjective c v) :=
              (Real.log_le_log_iff hwpos hvpos).mpr (hvmax w hw)
        _ = btObjective c v :=
              Real_log_fordBTProductObjective_eq_btObjective hv.1

/-- The displayed Bradley--Terry equations in Ford/Zermelo form. -/
def SatisfiesBTDisplayedEquation
    (w : α → α → ℝ) (B u : α → ℝ) : Prop :=
  ∀ x : α,
    Finset.sum (Finset.univ.erase x)
      (fun y => w x y * (u x / (u x + u y))) = B x

/-- Ford's displayed equations specialized to a strict-count matrix:
observed wins equal expected wins under pair totals. -/
def SatisfiesFordBTEquations
    (c : α → α → ℝ) (u : α → ℝ) : Prop :=
  SatisfiesBTDisplayedEquation (fordPairTotal c) (fordWinCount c) u

/-- Coordinate expression for the formal derivative of Ford's additive
Bradley--Terry objective at a positive strength vector.  Vanishing of these
coordinates is exactly Ford's displayed equation system. -/
noncomputable def fordBTObjectiveCoordinateDerivative
    (c : α → α → ℝ) (u : α → ℝ) (x : α) : ℝ :=
  fordWinCount c x / u x -
    Finset.sum (Finset.univ.erase x)
      (fun y => fordPairTotal c x y / (u x + u y))

/-- The affine line through a strength vector in a finite coordinate
direction. -/
def btLine (u d : α → ℝ) (t : ℝ) : α → ℝ :=
  fun z => u z + t * d z

/-- The two-coordinate direction preserving the simplex sum: add to `x` and
subtract from `y`.  Written as a difference of indicators so its total sum
simplifies uniformly, including the degenerate `x = y` case. -/
def btSimplexDirection (x y z : α) : ℝ :=
  (if z = x then 1 else 0) - (if z = y then 1 else 0)

lemma sum_btSimplexDirection (x y : α) :
    Finset.sum Finset.univ (fun z : α => btSimplexDirection x y z) = 0 := by
  classical
  simp [btSimplexDirection]

lemma sum_btSimplexDirection_mul (F : α → ℝ) (x y : α) :
    Finset.sum Finset.univ
        (fun z : α => btSimplexDirection x y z * F z) =
      F x - F y := by
  classical
  unfold btSimplexDirection
  calc
    Finset.sum Finset.univ
        (fun z : α =>
          ((if z = x then 1 else 0) - (if z = y then 1 else 0)) * F z) =
      Finset.sum Finset.univ
          (fun z : α => (if z = x then 1 else 0) * F z) -
        Finset.sum Finset.univ
          (fun z : α => (if z = y then 1 else 0) * F z) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro z _hz
        ring
    _ = F x - F y := by
        simp

lemma btLine_simplexDirection_sum
    {u : α → ℝ} (hu : IsFullSupportLottery u) (x y : α) (t : ℝ) :
    Finset.sum Finset.univ
        (fun z : α => btLine u (btSimplexDirection x y) t z) = 1 := by
  classical
  calc
    Finset.sum Finset.univ
        (fun z : α => btLine u (btSimplexDirection x y) t z) =
      Finset.sum Finset.univ (fun z : α => u z) +
        t * Finset.sum Finset.univ
          (fun z : α => btSimplexDirection x y z) := by
        unfold btLine
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 1 := by
        rw [hu.2, sum_btSimplexDirection]
        ring

lemma eventually_fullSupportLottery_btLine_simplexDirection
    {u : α → ℝ} (hu : IsFullSupportLottery u) {x y : α}
    (hxy : x ≠ y) :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      IsFullSupportLottery (btLine u (btSimplexDirection x y) t) := by
  classical
  have hposx : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < u x + t := by
    have h0 : 0 < (fun t : ℝ => u x + t) 0 := by
      simpa using hu.1 x
    simpa using
      ((continuousAt_const.add continuousAt_id).eventually
        (lt_mem_nhds h0))
  have hposy : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < u y - t := by
    have h0 : 0 < (fun t : ℝ => u y - t) 0 := by
      simpa using hu.1 y
    simpa using
      ((continuousAt_const.sub continuousAt_id).eventually
        (lt_mem_nhds h0))
  filter_upwards [hposx, hposy] with t htx hty
  refine ⟨?_, btLine_simplexDirection_sum hu x y t⟩
  intro z
  by_cases hzx : z = x
  · subst z
    simpa [btLine, btSimplexDirection, hxy] using htx
  · by_cases hzy : z = y
    · subst z
      simpa [btLine, btSimplexDirection, hxy, eq_comm] using hty
    · simpa [btLine, btSimplexDirection, hzx, hzy] using hu.1 z

omit [Fintype α] [DecidableEq α] in
/-- Directional derivative of one log Bradley--Terry fraction along an affine
coordinate line through a positive strength vector. -/
lemma hasDerivAt_log_btFraction_btLine
    {u d : α → ℝ} (hu : ∀ z : α, 0 < u z) (x y : α) :
    HasDerivAt
      (fun t : ℝ => Real.log (btFraction (btLine u d t) x y))
      (d x / u x - (d x + d y) / (u x + u y)) 0 := by
  have hx :
      HasDerivAt (fun t : ℝ => u x + t * d x) (d x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d x)).const_add (u x)
  have hy :
      HasDerivAt (fun t : ℝ => u y + t * d y) (d y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d y)).const_add (u y)
  have hden0 :
      (u x + 0 * d x + (u y + 0 * d y)) ≠ 0 := by
    simpa using (add_pos (hu x) (hu y)).ne'
  have hfrac0 :
      (u x + 0 * d x) / (u x + 0 * d x + (u y + 0 * d y)) ≠ 0 := by
    exact div_ne_zero (by simpa using (hu x).ne') hden0
  have hmain :
      HasDerivAt
        (fun t : ℝ =>
          Real.log ((u x + t * d x) /
            (u x + t * d x + (u y + t * d y))))
        (((d x * (u x + 0 * d x + (u y + 0 * d y)) -
              (u x + 0 * d x) * (d x + d y)) /
            (u x + 0 * d x + (u y + 0 * d y)) ^ 2) /
          ((u x + 0 * d x) /
            (u x + 0 * d x + (u y + 0 * d y)))) 0 :=
    ((hx.div (hx.add hy) hden0).log hfrac0)
  have hderiv :
      (((d x * (u x + 0 * d x + (u y + 0 * d y)) -
              (u x + 0 * d x) * (d x + d y)) /
            (u x + 0 * d x + (u y + 0 * d y)) ^ 2) /
          ((u x + 0 * d x) /
            (u x + 0 * d x + (u y + 0 * d y)))) =
        d x / u x - (d x + d y) / (u x + u y) := by
    field_simp [(hu x).ne', (add_pos (hu x) (hu y)).ne']
    ring
  simpa [btFraction, btLine] using hmain.congr_deriv hderiv

/-- Directional derivative of the additive Bradley--Terry objective, written
as the directed-pair sum obtained by differentiating every log fraction. -/
lemma hasDerivAt_btObjective_btLine_directed
    {c : α → α → ℝ} {u d : α → ℝ}
    (hu : ∀ z : α, 0 < u z) :
    HasDerivAt
      (fun t : ℝ => btObjective c (btLine u d t))
      (Finset.sum Finset.univ (fun x =>
        Finset.sum (Finset.univ.erase x) (fun y =>
          c x y * (d x / u x - (d x + d y) / (u x + u y))))) 0 := by
  classical
  unfold btObjective
  refine HasDerivAt.fun_sum ?_
  intro x _hx
  refine HasDerivAt.fun_sum ?_
  intro y _hy
  exact (hasDerivAt_log_btFraction_btLine hu x y).const_mul (c x y)

/-- The directed-pair derivative sum is the dot product of the perturbation
direction with Ford's coordinate derivative expression. -/
lemma btObjective_btLine_directedDerivative_eq_coordinateDerivative_sum
    {c : α → α → ℝ} {u d : α → ℝ} :
    Finset.sum Finset.univ (fun x =>
        Finset.sum (Finset.univ.erase x) (fun y =>
          c x y * (d x / u x - (d x + d y) / (u x + u y)))) =
      Finset.sum Finset.univ
        (fun x => d x * fordBTObjectiveCoordinateDerivative c u x) := by
  classical
  let A : ℝ := Finset.sum Finset.univ (fun x =>
    Finset.sum (Finset.univ.erase x) (fun y => c x y * (d x / u x)))
  let B : ℝ := Finset.sum Finset.univ (fun x =>
    Finset.sum (Finset.univ.erase x) (fun y =>
      c x y * (d x / (u x + u y))))
  let C : ℝ := Finset.sum Finset.univ (fun x =>
    Finset.sum (Finset.univ.erase x) (fun y =>
      c x y * (d y / (u x + u y))))
  let D : ℝ := Finset.sum Finset.univ (fun x =>
    Finset.sum (Finset.univ.erase x) (fun y =>
      c y x * (d x / (u x + u y))))
  let E : ℝ := Finset.sum Finset.univ (fun x =>
    d x * Finset.sum (Finset.univ.erase x) (fun y =>
      fordPairTotal c x y / (u x + u y)))
  have hraw :
      Finset.sum Finset.univ (fun x =>
          Finset.sum (Finset.univ.erase x) (fun y =>
            c x y * (d x / u x - (d x + d y) / (u x + u y)))) =
        A - B - C := by
    dsimp [A, B, C]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro y _hy
    ring
  have hA :
      A = Finset.sum Finset.univ
        (fun x => d x * (fordWinCount c x / u x)) := by
    dsimp [A, fordWinCount]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [← Finset.sum_mul]
    ring
  have hCoff :
      C =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 * (d p.2 / (u p.1 + u p.2))) := by
    dsimp [C]
    exact sum_univ_erase_eq_sum_offDiag
      (fun x y : α => c x y * (d y / (u x + u y)))
  have hDoff :
      D =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.2 p.1 * (d p.1 / (u p.1 + u p.2))) := by
    dsimp [D]
    exact sum_univ_erase_eq_sum_offDiag
      (fun x y : α => c y x * (d x / (u x + u y)))
  have hCD : C = D := by
    rw [hCoff, hDoff]
    simpa [add_comm] using
      (sum_offDiag_swap
        (fun x y : α => c x y * (d y / (u x + u y)))).symm
  have hE : E = B + D := by
    dsimp [E, B, D]
    calc
      Finset.sum Finset.univ (fun x =>
          d x * Finset.sum (Finset.univ.erase x) (fun y =>
            fordPairTotal c x y / (u x + u y))) =
        Finset.sum Finset.univ (fun x =>
          Finset.sum (Finset.univ.erase x) (fun y =>
            d x * (fordPairTotal c x y / (u x + u y)))) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [Finset.mul_sum]
      _ =
        Finset.sum Finset.univ (fun x =>
          Finset.sum (Finset.univ.erase x) (fun y =>
            c x y * (d x / (u x + u y)) +
              c y x * (d x / (u x + u y)))) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          refine Finset.sum_congr rfl ?_
          intro y _hy
          unfold fordPairTotal
          ring
      _ =
        Finset.sum Finset.univ (fun x =>
            Finset.sum (Finset.univ.erase x) (fun y =>
              c x y * (d x / (u x + u y)))) +
          Finset.sum Finset.univ (fun x =>
            Finset.sum (Finset.univ.erase x) (fun y =>
              c y x * (d x / (u x + u y)))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [Finset.sum_add_distrib]
  have htarget :
      Finset.sum Finset.univ
          (fun x => d x * fordBTObjectiveCoordinateDerivative c u x) =
        A - (B + D) := by
    calc
      Finset.sum Finset.univ
          (fun x => d x * fordBTObjectiveCoordinateDerivative c u x) =
        Finset.sum Finset.univ (fun x =>
            d x * (fordWinCount c x / u x)) - E := by
          dsimp [E, fordBTObjectiveCoordinateDerivative]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
      _ = A - (B + D) := by
          rw [← hA, hE]
  calc
    Finset.sum Finset.univ (fun x =>
        Finset.sum (Finset.univ.erase x) (fun y =>
          c x y * (d x / u x - (d x + d y) / (u x + u y)))) =
      A - B - C := hraw
    _ = A - (B + D) := by
      rw [hCD]
      ring
    _ =
      Finset.sum Finset.univ
        (fun x => d x * fordBTObjectiveCoordinateDerivative c u x) :=
      htarget.symm

/-- Directional derivative of the additive Bradley--Terry objective, written
as the dot product with Ford's coordinate derivative vector. -/
lemma hasDerivAt_btObjective_btLine
    {c : α → α → ℝ} {u d : α → ℝ}
    (hu : ∀ z : α, 0 < u z) :
    HasDerivAt
      (fun t : ℝ => btObjective c (btLine u d t))
      (Finset.sum Finset.univ
        (fun x => d x * fordBTObjectiveCoordinateDerivative c u x)) 0 :=
  (hasDerivAt_btObjective_btLine_directed (c := c) (u := u) (d := d) hu).congr_deriv
    (btObjective_btLine_directedDerivative_eq_coordinateDerivative_sum
      (c := c) (u := u) (d := d))

/-- Algebraic Euler-equation bridge: if the coordinate first-order expression
vanishes at a positive vector, then Ford's displayed Bradley--Terry equations
hold.  This isolates the remaining analytic step as proving stationarity of an
interior likelihood maximizer. -/
theorem SatisfiesFordBTEquations_of_coordinateDerivative_eq_zero
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hstat : ∀ x : α,
      fordBTObjectiveCoordinateDerivative c u x = 0) :
    SatisfiesFordBTEquations c u := by
  classical
  intro x
  let S : ℝ :=
    Finset.sum (Finset.univ.erase x)
      (fun y => fordPairTotal c x y / (u x + u y))
  have hder := hstat x
  have heq : fordWinCount c x / u x = S := by
    dsimp [fordBTObjectiveCoordinateDerivative, S] at hder
    linarith
  have hscaled : fordWinCount c x = u x * S := by
    calc
      fordWinCount c x = u x * (fordWinCount c x / u x) := by
        field_simp [(hu x).ne']
      _ = u x * S := by rw [heq]
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y =>
          fordPairTotal c x y * (u x / (u x + u y))) =
      u x * S := by
        dsimp [S]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y _hy
        have hden : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
        field_simp [hden]
    _ = fordWinCount c x := hscaled.symm

/-- Converse of the algebraic Euler-equation bridge: Ford's displayed
equations make every coordinate derivative expression vanish. -/
theorem coordinateDerivative_eq_zero_of_SatisfiesFordBTEquations
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hBT : SatisfiesFordBTEquations c u) :
    ∀ x : α, fordBTObjectiveCoordinateDerivative c u x = 0 := by
  classical
  intro x
  let S : ℝ :=
    Finset.sum (Finset.univ.erase x)
      (fun y => fordPairTotal c x y / (u x + u y))
  have hsum :
      Finset.sum (Finset.univ.erase x)
          (fun y =>
            fordPairTotal c x y * (u x / (u x + u y))) =
        u x * S := by
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _hy
    have hden : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
    field_simp [hden]
  have hBTx : u x * S = fordWinCount c x := by
    rw [← hsum]
    exact hBT x
  have heq : fordWinCount c x / u x = S := by
    calc
      fordWinCount c x / u x = (u x * S) / u x := by rw [hBTx]
      _ = S := by field_simp [(hu x).ne']
  dsimp [fordBTObjectiveCoordinateDerivative, S]
  linarith

/-- Positive-vector equivalence between Ford's displayed equations and
vanishing of the coordinate first-order expression. -/
theorem SatisfiesFordBTEquations_iff_coordinateDerivative_eq_zero
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    SatisfiesFordBTEquations c u ↔
      ∀ x : α, fordBTObjectiveCoordinateDerivative c u x = 0 :=
  ⟨coordinateDerivative_eq_zero_of_SatisfiesFordBTEquations hu,
    SatisfiesFordBTEquations_of_coordinateDerivative_eq_zero hu⟩

/-- Algebraic scale-invariance identity for Ford's coordinate derivative
expression: at every positive vector the derivative in the radial direction is
zero. -/
lemma sum_weighted_fordBTObjectiveCoordinateDerivative_eq_zero
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    Finset.sum Finset.univ
      (fun x => u x * fordBTObjectiveCoordinateDerivative c u x) = 0 := by
  classical
  let G : α → α → ℝ := fun x y =>
    u x * (fordPairTotal c x y / (u x + u y))
  have hrow :
      Finset.sum Finset.univ
          (fun x => u x * fordBTObjectiveCoordinateDerivative c u x) =
        Finset.sum Finset.univ (fun x => fordWinCount c x) -
          Finset.sum Finset.univ
            (fun x => Finset.sum (Finset.univ.erase x)
              (fun y => G x y)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    dsimp [fordBTObjectiveCoordinateDerivative, G]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · field_simp [(hu x).ne']
  have hwin :
      Finset.sum Finset.univ (fun x => fordWinCount c x) =
        Finset.sum Finset.univ.offDiag (fun p : α × α => c p.1 p.2) := by
    simpa [fordWinCount] using
      sum_univ_erase_eq_sum_offDiag (fun x y => c x y)
  have hGsum :
      Finset.sum Finset.univ
          (fun x => Finset.sum (Finset.univ.erase x)
            (fun y => G x y)) =
        Finset.sum Finset.univ.offDiag (fun p : α × α => G p.1 p.2) :=
    sum_univ_erase_eq_sum_offDiag G
  have hpair :
      ∀ p ∈ Finset.univ.offDiag,
        G p.1 p.2 + G p.2 p.1 =
          c p.1 p.2 + c p.2 p.1 := by
    intro p _hp
    have hden₁ : u p.1 + u p.2 ≠ 0 :=
      (add_pos (hu p.1) (hu p.2)).ne'
    have hden₂ : u p.2 + u p.1 ≠ 0 :=
      (add_pos (hu p.2) (hu p.1)).ne'
    dsimp [G, fordPairTotal]
    field_simp [hden₁, hden₂]
    ring
  let A : ℝ :=
    Finset.sum Finset.univ.offDiag (fun p : α × α => G p.1 p.2)
  let B : ℝ :=
    Finset.sum Finset.univ.offDiag (fun p : α × α => c p.1 p.2)
  have htwiceG :
      (2 : ℝ) * A =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          G p.1 p.2 + G p.2 p.1) := by
    dsimp [A]
    rw [Finset.sum_add_distrib, sum_offDiag_swap G]
    ring
  have htwiceC :
      (2 : ℝ) * B =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 + c p.2 p.1) := by
    dsimp [B]
    rw [Finset.sum_add_distrib, sum_offDiag_swap c]
    ring
  have hpair_sum :
      Finset.sum Finset.univ.offDiag (fun p : α × α =>
          G p.1 p.2 + G p.2 p.1) =
        Finset.sum Finset.univ.offDiag (fun p : α × α =>
          c p.1 p.2 + c p.2 p.1) :=
    Finset.sum_congr rfl hpair
  have hAB : A = B := by
    have htwice : (2 : ℝ) * A = (2 : ℝ) * B := by
      rw [htwiceG, htwiceC, hpair_sum]
    nlinarith
  calc
    Finset.sum Finset.univ
        (fun x => u x * fordBTObjectiveCoordinateDerivative c u x) =
      Finset.sum Finset.univ (fun x => fordWinCount c x) -
        Finset.sum Finset.univ
          (fun x => Finset.sum (Finset.univ.erase x)
            (fun y => G x y)) := hrow
    _ = B - A := by rw [hwin, hGsum]
    _ = 0 := by rw [hAB]; ring

/-- Constrained first-order bridge: if the coordinate derivative expression is
constant across alternatives at a full-support lottery, then the common
Lagrange multiplier is zero by scale invariance, hence Ford's displayed
equations hold. -/
theorem SatisfiesFordBTEquations_of_coordinateDerivative_constant
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : IsFullSupportLottery u)
    (hstat : ∀ x y : α,
      fordBTObjectiveCoordinateDerivative c u x =
        fordBTObjectiveCoordinateDerivative c u y) :
    SatisfiesFordBTEquations c u := by
  refine SatisfiesFordBTEquations_of_coordinateDerivative_eq_zero hu.1 ?_
  intro x
  have hweighted :=
    sum_weighted_fordBTObjectiveCoordinateDerivative_eq_zero
      (c := c) hu.1
  have hconst :
      Finset.sum Finset.univ
          (fun z => u z * fordBTObjectiveCoordinateDerivative c u z) =
        fordBTObjectiveCoordinateDerivative c u x *
          Finset.sum Finset.univ (fun z => u z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro z _hz
    rw [hstat z x]
    ring
  rw [hu.2] at hconst
  linarith

/-- Fermat/Lagrange multiplier step for Ford's likelihood: a full-support
simplex maximizer has constant coordinate derivative expression. -/
theorem coordinateDerivative_eq_of_fullSupportBTObjectiveMaximizer
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : IsFullSupportLottery u)
    (hmax : ∀ v : α → ℝ, IsFullSupportLottery v →
      btObjective c v ≤ btObjective c u) :
    ∀ x y : α,
      fordBTObjectiveCoordinateDerivative c u x =
        fordBTObjectiveCoordinateDerivative c u y := by
  classical
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  · have hlocal :
        IsLocalMax
          (fun t : ℝ =>
            btObjective c (btLine u (btSimplexDirection x y) t)) 0 := by
      exact (eventually_fullSupportLottery_btLine_simplexDirection
        hu hxy).mono (fun t ht => by
          have hzero :
              btLine u (btSimplexDirection x y) 0 = u := by
            funext z
            simp [btLine]
          change btObjective c (btLine u (btSimplexDirection x y) t) ≤
            btObjective c (btLine u (btSimplexDirection x y) 0)
          rw [hzero]
          exact hmax _ ht)
    have hderiv :
        HasDerivAt
          (fun t : ℝ =>
            btObjective c (btLine u (btSimplexDirection x y) t))
          (Finset.sum Finset.univ (fun z =>
            btSimplexDirection x y z *
              fordBTObjectiveCoordinateDerivative c u z)) 0 :=
      hasDerivAt_btObjective_btLine
        (c := c) (u := u) (d := btSimplexDirection x y) hu.1
    have hzero :
        Finset.sum Finset.univ (fun z =>
            btSimplexDirection x y z *
              fordBTObjectiveCoordinateDerivative c u z) = 0 :=
      hlocal.hasDerivAt_eq_zero hderiv
    have hsum :
        Finset.sum Finset.univ (fun z =>
            btSimplexDirection x y z *
              fordBTObjectiveCoordinateDerivative c u z) =
          fordBTObjectiveCoordinateDerivative c u x -
            fordBTObjectiveCoordinateDerivative c u y :=
      sum_btSimplexDirection_mul
        (fun z => fordBTObjectiveCoordinateDerivative c u z) x y
    rw [hsum] at hzero
    linarith

/-- An interior Bradley--Terry likelihood maximizer satisfies Ford's displayed
equations. -/
theorem SatisfiesFordBTEquations_of_fullSupportBTObjectiveMaximizer
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : IsFullSupportLottery u)
    (hmax : ∀ v : α → ℝ, IsFullSupportLottery v →
      btObjective c v ≤ btObjective c u) :
    SatisfiesFordBTEquations c u :=
  SatisfiesFordBTEquations_of_coordinateDerivative_constant hu
    (coordinateDerivative_eq_of_fullSupportBTObjectiveMaximizer hu hmax)

/-- If `u` satisfies Ford's displayed equations for `c`, then Ford's synthetic
matrix at `u` has the same win counts as `c`. This is Ford's identity
`T_i = W_i` for the matrix built from an interior solution. -/
lemma fordWinCount_fordSyntheticCount_eq_of_ford_equations
    {c : α → α → ℝ} {u : α → ℝ}
    (hBT : SatisfiesFordBTEquations c u) (x : α) :
    fordWinCount (fordSyntheticCount c u) x = fordWinCount c x := by
  calc
    fordWinCount (fordSyntheticCount c u) x =
        Finset.sum (Finset.univ.erase x)
          (fun y => fordPairTotal c x y * (u x / (u x + u y))) := by
          rfl
    _ = fordWinCount c x := hBT x

/-- If two positive vectors solve Ford's displayed equations for the same count
matrix, their synthetic matrices have the same row win counts. -/
lemma fordWinCount_fordSyntheticCount_eq_of_ford_equations_pair
    {c : α → α → ℝ} {u v : α → ℝ}
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c v)
    (x : α) :
    fordWinCount (fordSyntheticCount c u) x =
      fordWinCount (fordSyntheticCount c v) x := by
  rw [fordWinCount_fordSyntheticCount_eq_of_ford_equations hBTu x,
    fordWinCount_fordSyntheticCount_eq_of_ford_equations hBTv x]

/-- The vector used to generate Ford's synthetic matrix always satisfies Ford's
displayed equations for that synthetic matrix. -/
theorem SatisfiesFordBTEquations_fordSyntheticCount
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x) :
    SatisfiesFordBTEquations (fordSyntheticCount c u) u := by
  intro x
  unfold fordWinCount
  refine Finset.sum_congr rfl ?_
  intro y _hy
  simpa [btFraction] using
    (fordSyntheticCount_eq_pairTotal_mul_btFraction (c := c) hu x y).symm

/-- If two positive vectors solve Ford's displayed equations for the same
original matrix, then `u` also solves Ford's displayed equations for the
synthetic matrix generated by `v`. This transfers both the unordered pair
totals and the row win totals across the two synthetic matrices. -/
theorem SatisfiesFordBTEquations_fordSyntheticCount_of_same_base_solution
    {c : α → α → ℝ} {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c v) :
    SatisfiesFordBTEquations (fordSyntheticCount c v) u := by
  intro x
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y =>
          fordPairTotal (fordSyntheticCount c v) x y *
            (u x / (u x + u y)))
        =
      Finset.sum (Finset.univ.erase x)
        (fun y =>
          fordPairTotal (fordSyntheticCount c u) x y *
            (u x / (u x + u y))) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          rw [fordPairTotal_fordSyntheticCount_eq_of_same_base hv hu]
    _ = fordWinCount (fordSyntheticCount c u) x :=
          SatisfiesFordBTEquations_fordSyntheticCount hu x
    _ = fordWinCount (fordSyntheticCount c v) x :=
          fordWinCount_fordSyntheticCount_eq_of_ford_equations_pair
            hBTu hBTv x

/-- If `u` satisfies Ford's displayed equations for `c`, then `c` and Ford's
synthetic matrix generated by `u` give the same BT objective at every positive
strength vector. -/
theorem btObjective_eq_fordSyntheticCount_of_ford_equations
    {c : α → α → ℝ} {u v : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    (hBT : SatisfiesFordBTEquations c u) :
    btObjective c v = btObjective (fordSyntheticCount c u) v :=
  btObjective_eq_of_same_pairTotal_winCount hv
    (fun x y => (fordPairTotal_fordSyntheticCount hu x y).symm)
    (fun x => (fordWinCount_fordSyntheticCount_eq_of_ford_equations hBT x).symm)

/-- At a coordinate where the strength ratio `u/v` is maximal, two positive
solutions of Ford's displayed equations must have the same Bradley--Terry
fraction on every positive pair-total edge out of that coordinate. -/
lemma fordEquation_max_ratio_fraction_eq
    {c : α → α → ℝ} {u v : α → ℝ} {x y : α}
    (hc : IsFordCountMatrix c)
    (hu : ∀ z : α, 0 < u z)
    (hv : ∀ z : α, 0 < v z)
    (hmax : ∀ z : α, u z / v z ≤ u x / v x)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c v)
    (hTxy : 0 < fordPairTotal c x y) :
    btFraction u x y = btFraction v x y := by
  have hBTu_x :
      Finset.sum (Finset.univ.erase x)
        (fun z => fordPairTotal c x z * btFraction u x z) =
          fordWinCount c x := by
    simpa [btFraction] using hBTu x
  have hBTv_x :
      Finset.sum (Finset.univ.erase x)
        (fun z => fordPairTotal c x z * btFraction v x z) =
          fordWinCount c x := by
    simpa [btFraction] using hBTv x
  have hterm_nonneg :
      ∀ z : α, z ∈ Finset.univ.erase x →
        0 ≤ fordPairTotal c x z *
          (btFraction u x z - btFraction v x z) := by
    intro z _hz
    have hTnonneg : 0 ≤ fordPairTotal c x z := by
      unfold fordPairTotal
      exact add_nonneg (hc.2 x z) (hc.2 z x)
    have hfrac_le : btFraction v x z ≤ btFraction u x z :=
      btFraction_le_of_ratio_ge hu hv (hmax z)
    exact mul_nonneg hTnonneg (sub_nonneg.mpr hfrac_le)
  have hsumzero :
      Finset.sum (Finset.univ.erase x)
        (fun z => fordPairTotal c x z *
          (btFraction u x z - btFraction v x z)) = 0 := by
    calc
      Finset.sum (Finset.univ.erase x)
          (fun z => fordPairTotal c x z *
            (btFraction u x z - btFraction v x z))
          =
        Finset.sum (Finset.univ.erase x)
          (fun z => fordPairTotal c x z * btFraction u x z) -
          Finset.sum (Finset.univ.erase x)
            (fun z => fordPairTotal c x z * btFraction v x z) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro z _hz
          ring
      _ = 0 := by
          rw [hBTu_x, hBTv_x]
          ring
  have hyne : y ≠ x := by
    intro hyx
    subst y
    have hTzero : fordPairTotal c x x = 0 := by
      unfold fordPairTotal
      rw [hc.1 x]
      ring
    rw [hTzero] at hTxy
    linarith
  have hy_mem : y ∈ Finset.univ.erase x :=
    Finset.mem_erase.mpr ⟨hyne, Finset.mem_univ y⟩
  have hterm_zero :
      fordPairTotal c x y *
          (btFraction u x y - btFraction v x y) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp
      hsumzero y hy_mem
  have hdiff_zero : btFraction u x y - btFraction v x y = 0 := by
    nlinarith
  linarith

/-- Ratio form of `fordEquation_max_ratio_fraction_eq`. -/
lemma fordEquation_max_ratio_ratio_eq
    {c : α → α → ℝ} {u v : α → ℝ} {x y : α}
    (hc : IsFordCountMatrix c)
    (hu : ∀ z : α, 0 < u z)
    (hv : ∀ z : α, 0 < v z)
    (hmax : ∀ z : α, u z / v z ≤ u x / v x)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c v)
    (hTxy : 0 < fordPairTotal c x y) :
    u x / v x = u y / v y :=
  ratio_eq_of_btFraction_eq hu hv
    (fordEquation_max_ratio_fraction_eq hc hu hv hmax hBTu hBTv hTxy)

/-- The max-ratio equality propagates along every positive-count path. -/
lemma ford_ratio_eq_of_reflTransGen_from_max
    {c : α → α → ℝ} {u v : α → ℝ} {x z : α}
    (hc : IsFordCountMatrix c)
    (hu : ∀ t : α, 0 < u t)
    (hv : ∀ t : α, 0 < v t)
    (hmax : ∀ t : α, u t / v t ≤ u x / v x)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c v)
    (hpath : Relation.ReflTransGen (fordCountEdge c) x z) :
    u x / v x = u z / v z := by
  induction hpath with
  | refl =>
      rfl
  | tail hpath htail ih =>
      rename_i b z
      have hmax_b : ∀ t : α, u t / v t ≤ u b / v b := by
        intro t
        calc
          u t / v t ≤ u x / v x := hmax t
          _ = u b / v b := ih
      have hT : 0 < fordPairTotal c b z :=
        fordPairTotal_pos_of_count_pos hc.2 htail.2
      have hbz : u b / v b = u z / v z :=
        fordEquation_max_ratio_ratio_eq hc hu hv hmax_b hBTu hBTv hT
      exact ih.trans hbz

omit [Fintype α] [DecidableEq α] in
/-- Equality of Bradley--Terry fractions on every edge of a positive-count path
propagates equality of strength ratios along that path. -/
lemma ratio_eq_of_reflTransGen_of_btFraction_eq
    {c : α → α → ℝ} {u v : α → ℝ} {x y : α}
    (hu : ∀ t : α, 0 < u t)
    (hv : ∀ t : α, 0 < v t)
    (hfrac : ∀ {a b : α}, fordCountEdge c a b →
      btFraction u a b = btFraction v a b)
    (hpath : Relation.ReflTransGen (fordCountEdge c) x y) :
    u x / v x = u y / v y := by
  induction hpath with
  | refl =>
      rfl
  | tail hpath htail ih =>
      rename_i b z
      have hbz : u b / v b = u z / v z :=
        ratio_eq_of_btFraction_eq hu hv (hfrac htail)
      exact ih.trans hbz

omit [DecidableEq α] in
/-- If two full-support lotteries have the same BT fractions on every
positive-count edge of a Ford-connected graph, then they are the same
normalized strength vector. -/
theorem IsFullSupportLottery.eq_of_btFraction_eq_on_ford_edges
    [Nonempty α]
    {c : α → α → ℝ} {u v : α → ℝ}
    (hconn : FordStronglyConnected c)
    (hu : IsFullSupportLottery u)
    (hv : IsFullSupportLottery v)
    (hfrac : ∀ {a b : α}, fordCountEdge c a b →
      btFraction u a b = btFraction v a b) :
    u = v := by
  let x : α := Classical.choice (inferInstance : Nonempty α)
  let a : ℝ := u x / v x
  have hratio : ∀ z : α, a = u z / v z := by
    intro z
    exact ratio_eq_of_reflTransGen_of_btFraction_eq hu.1 hv.1
      hfrac (hconn x z)
  have hscale : ∀ z : α, u z = a * v z := by
    intro z
    calc
      u z = (u z / v z) * v z := by
        field_simp [(hv.1 z).ne']
      _ = a * v z := by
        rw [← hratio z]
  have hsum_scale :
      Finset.sum Finset.univ (fun z : α => u z) =
        a * Finset.sum Finset.univ (fun z : α => v z) := by
    calc
      Finset.sum Finset.univ (fun z : α => u z) =
          Finset.sum Finset.univ (fun z : α => a * v z) := by
          refine Finset.sum_congr rfl ?_
          intro z _hz
          rw [hscale z]
      _ = a * Finset.sum Finset.univ (fun z : α => v z) := by
          rw [← Finset.mul_sum]
  have ha : a = 1 := by
    rw [hu.2, hv.2] at hsum_scale
    linarith
  funext z
  calc
    u z = a * v z := hscale z
    _ = v z := by
      rw [ha]
      ring

/-- A full-support solution of Ford's displayed equations is the unique
normalized full-support maximizer of the Bradley--Terry log-likelihood.  This
internalizes the maximum-likelihood part of Ford/Zermelo once existence of a
positive solution is available. -/
theorem HasFordNormalizedBTMaximizer_of_satisfiesFordEquations
    [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hu : IsFullSupportLottery u)
    (hBT : SatisfiesFordBTEquations c u) :
    HasFordNormalizedBTMaximizer c u := by
  have hobj_eq :
      ∀ v : α → ℝ, (∀ x : α, 0 < v x) →
        btObjective c v = btObjective (fordSyntheticCount c u) v := by
    intro v hv
    exact btObjective_eq_fordSyntheticCount_of_ford_equations hu.1 hv hBT
  refine ⟨hu, ?_, ?_⟩
  · intro v hv
    calc
      btObjective c v =
          btObjective (fordSyntheticCount c u) v := hobj_eq v hv.1
      _ ≤ btObjective (fordSyntheticCount c u) u :=
          btObjective_fordSyntheticCount_le_self hc.2 hu.1 hv.1
      _ = btObjective c u := (hobj_eq u hu.1).symm
  · intro v hv hvmax
    have hle_vu :
        btObjective c v ≤ btObjective c u := by
      calc
        btObjective c v =
            btObjective (fordSyntheticCount c u) v := hobj_eq v hv.1
        _ ≤ btObjective (fordSyntheticCount c u) u :=
            btObjective_fordSyntheticCount_le_self hc.2 hu.1 hv.1
        _ = btObjective c u := (hobj_eq u hu.1).symm
    have hle_uv : btObjective c u ≤ btObjective c v := hvmax u hu
    have heq_c : btObjective c v = btObjective c u :=
      le_antisymm hle_vu hle_uv
    have heq_syn :
        btObjective (fordSyntheticCount c u) v =
          btObjective (fordSyntheticCount c u) u := by
      calc
        btObjective (fordSyntheticCount c u) v =
            btObjective c v := (hobj_eq v hv.1).symm
        _ = btObjective c u := heq_c
        _ = btObjective (fordSyntheticCount c u) u := hobj_eq u hu.1
    have hfrac_edges :
        ∀ {a b : α}, fordCountEdge c a b →
          btFraction u a b = btFraction v a b := by
      intro a b hab
      by_contra hfrac_ne
      have hT : 0 < fordPairTotal c a b :=
        fordPairTotal_pos_of_count_pos hc.2 hab.2
      have hp : (a, b) ∈ Finset.univ.offDiag := by
        simpa using hab.1
      have hstrict :
          btObjective (fordSyntheticCount c u) v <
            btObjective (fordSyntheticCount c u) u :=
        btObjective_fordSyntheticCount_lt_self_of_exists_fraction_ne
          hc.2 hu.1 hv.1 ⟨(a, b), hp, hT, hfrac_ne⟩
      rw [heq_syn] at hstrict
      exact (lt_self_iff_false _).mp hstrict
    have hfrac_edges_symm :
        ∀ {a b : α}, fordCountEdge c a b →
          btFraction v a b = btFraction u a b := by
      intro a b hab
      exact (hfrac_edges hab).symm
    exact hv.eq_of_btFraction_eq_on_ford_edges
      hconn hu hfrac_edges_symm

/-- Ford/Zermelo uniqueness for normalized positive solutions of the displayed
equations, proved by the standard finite max-ratio propagation argument. -/
theorem SatisfiesFordBTEquations_unique_of_stronglyConnected
    [Nonempty α]
    {c : α → α → ℝ} {u v : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hu : IsFullSupportLottery u)
    (hv : IsFullSupportLottery v)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c v) :
    u = v := by
  rcases Finset.exists_max_image (Finset.univ : Finset α)
      (fun z => u z / v z) Finset.univ_nonempty with
    ⟨x, _hx, hmax_univ⟩
  let a : ℝ := u x / v x
  have hmax : ∀ z : α, u z / v z ≤ u x / v x := by
    intro z
    exact hmax_univ z (Finset.mem_univ z)
  have hratio : ∀ z : α, a = u z / v z := by
    intro z
    exact ford_ratio_eq_of_reflTransGen_from_max
      hc hu.1 hv.1 hmax hBTu hBTv (hconn x z)
  have hscale : ∀ z : α, u z = a * v z := by
    intro z
    calc
      u z = (u z / v z) * v z := by
        field_simp [(hv.1 z).ne']
      _ = a * v z := by
        rw [← hratio z]
  have hsum_scale :
      Finset.sum Finset.univ (fun z : α => u z) =
        a * Finset.sum Finset.univ (fun z : α => v z) := by
    calc
      Finset.sum Finset.univ (fun z : α => u z) =
          Finset.sum Finset.univ (fun z : α => a * v z) := by
          refine Finset.sum_congr rfl ?_
          intro z _hz
          rw [hscale z]
      _ = a * Finset.sum Finset.univ (fun z : α => v z) := by
          rw [← Finset.mul_sum]
  have ha : a = 1 := by
    rw [hu.2, hv.2] at hsum_scale
    linarith
  funext z
  calc
    u z = a * v z := hscale z
    _ = v z := by
      rw [ha]
      ring

/-- If a Ford edge crosses from zero weight to positive weight, the directed
product likelihood has a zero factor. -/
lemma fordBTProductObjective_eq_zero_of_zero_to_pos_edge
    {c : α → α → ℝ} {u : α → ℝ} {a b : α}
    (hab : fordCountEdge c a b)
    (ha : u a = 0)
    (hb : 0 < u b) :
    fordBTProductObjective c u = 0 := by
  classical
  have _hb_ne : u b ≠ 0 := hb.ne'
  unfold fordBTProductObjective
  refine Finset.prod_eq_zero (i := a) (Finset.mem_univ a) ?_
  refine Finset.prod_eq_zero (i := b) ?_ ?_
  · exact Finset.mem_erase.mpr ⟨Ne.symm hab.1, Finset.mem_univ b⟩
  · rw [btFraction_eq_zero_of_left_eq_zero ha]
    exact Real.zero_rpow hab.2.ne'

/-- Ford's boundary conclusion in product-objective form: under strong
connectivity, every nonnegative sum-one boundary point has zero multiplicative
likelihood. -/
theorem fordBTProductObjective_eq_zero_of_simplex_boundary
    {c : α → α → ℝ} {u : α → ℝ}
    (hconn : FordStronglyConnected c)
    (hnonneg : ∀ z : α, 0 ≤ u z)
    (hsum : Finset.sum Finset.univ (fun z : α => u z) = 1)
    {x : α}
    (hx : u x = 0) :
    fordBTProductObjective c u = 0 := by
  rcases exists_fordCountEdge_zero_to_pos_of_simplex_boundary
      hconn hnonneg hsum hx with
    ⟨a, b, hab, ha, hb⟩
  exact fordBTProductObjective_eq_zero_of_zero_to_pos_edge hab ha hb

omit [DecidableEq α] in
/-- Every finite lottery has some positive coordinate. -/
lemma exists_pos_of_isLottery
    {u : α → ℝ}
    (hu : IsLottery u) :
    ∃ y : α, 0 < u y := by
  by_contra hno
  have hzero : ∀ z : α, u z = 0 := by
    intro z
    have hzle : u z ≤ 0 := le_of_not_gt (fun hz => hno ⟨z, hz⟩)
    exact le_antisymm hzle (hu.1 z)
  have hsum_zero : Finset.sum Finset.univ (fun z : α => u z) = 0 := by
    simp [hzero]
  rw [hu.2] at hsum_zero
  norm_num at hsum_zero

omit [DecidableEq α] in
/-- A finite lottery is either full-support or has a zero coordinate. -/
lemma IsLottery.fullSupport_or_boundary
    {u : α → ℝ}
    (hu : IsLottery u) :
    IsFullSupportLottery u ∨ ∃ x : α, u x = 0 := by
  by_cases hpos : ∀ x : α, 0 < u x
  · exact Or.inl ⟨hpos, hu.2⟩
  · push_neg at hpos
    rcases hpos with ⟨x, hx⟩
    exact Or.inr ⟨x, le_antisymm hx (hu.1 x)⟩

omit [DecidableEq α] in
/-- Lottery-boundary form of Ford's boundary step. -/
lemma exists_fordCountEdge_zero_to_pos_of_lottery_boundary
    {c : α → α → ℝ} {u : α → ℝ}
    (hconn : FordStronglyConnected c)
    (hu : IsLottery u)
    {x : α}
    (hx : u x = 0) :
    ∃ a b : α, fordCountEdge c a b ∧ u a = 0 ∧ 0 < u b :=
  exists_fordCountEdge_zero_to_pos_of_simplex_boundary
    hconn hu.1 hu.2 hx

/-- Ford's product likelihood vanishes at every simplex-boundary lottery under
Ford strong connectivity. -/
theorem fordBTProductObjective_eq_zero_of_lottery_boundary
    {c : α → α → ℝ} {u : α → ℝ}
    (hconn : FordStronglyConnected c)
    (hu : IsLottery u)
    (hboundary : ∃ x : α, u x = 0) :
    fordBTProductObjective c u = 0 := by
  rcases hboundary with ⟨x, hx⟩
  exact fordBTProductObjective_eq_zero_of_simplex_boundary
    hconn hu.1 hu.2 hx

/-- At a Ford-connected simplex-boundary lottery, the product objective tends
to zero along the closed simplex. -/
theorem tendsto_fordBTProductObjective_nhdsWithin_zero_of_lottery_boundary
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hconn : FordStronglyConnected c)
    (hu : IsLottery u)
    (hboundary : ∃ x : α, u x = 0) :
    Filter.Tendsto (fun v : α → ℝ => fordBTProductObjective c v)
      (𝓝[{v : α → ℝ | IsLottery v}] u) (𝓝 0) := by
  rcases hboundary with ⟨x, hx⟩
  rcases exists_fordCountEdge_zero_to_pos_of_lottery_boundary
      hconn hu hx with ⟨a, b, hab, ha, hb⟩
  have hfactor :
      Filter.Tendsto
        (fun v : α → ℝ => (btFraction v a b) ^ (c a b))
        (𝓝[{v : α → ℝ | IsLottery v}] u) (𝓝 0) :=
    (tendsto_fordEdgeFactor_nhds_zero_of_boundary_crossing
      (c := c) (u := u) hab ha hb).mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hfactor
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact fordBTProductObjective_nonneg_of_nonneg hv.1
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact fordBTProductObjective_le_edgeFactor_of_nonneg
      hc hv.1 hab.1

/-- Boundary continuity of Ford's product objective on the closed simplex. -/
theorem continuousWithinAt_fordBTProductObjective_lottery_boundary
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hconn : FordStronglyConnected c)
    (hu : IsLottery u)
    (hboundary : ∃ x : α, u x = 0) :
    ContinuousWithinAt (fun v : α → ℝ => fordBTProductObjective c v)
      {v : α → ℝ | IsLottery v} u := by
  have htend :=
    tendsto_fordBTProductObjective_nhdsWithin_zero_of_lottery_boundary
      (c := c) (u := u) hc hconn hu hboundary
  have hzero :
      fordBTProductObjective c u = 0 :=
    fordBTProductObjective_eq_zero_of_lottery_boundary hconn hu hboundary
  change Filter.Tendsto (fun v : α → ℝ => fordBTProductObjective c v)
    (𝓝[{v : α → ℝ | IsLottery v}] u) (𝓝 (fordBTProductObjective c u))
  rw [hzero]
  exact htend

omit [DecidableEq α] in
/-- The positive orthant is a neighborhood of each positive finite vector. -/
lemma fullSupport_set_mem_nhds
    {u : α → ℝ}
    (hu : ∀ z : α, 0 < u z) :
    {v : α → ℝ | ∀ z : α, 0 < v z} ∈ 𝓝 u := by
  change ∀ᶠ v in 𝓝 u, ∀ z : α, 0 < v z
  rw [Filter.eventually_all]
  intro z
  have hz : 0 < (fun v : α → ℝ => v z) u := hu z
  simpa using
    ((continuous_apply z).continuousAt.eventually (lt_mem_nhds hz))

/-- Pointwise full-support continuity of Ford's product objective. -/
lemma continuousAt_fordBTProductObjective_fullSupport
    (c : α → α → ℝ) {u : α → ℝ}
    (hu : ∀ z : α, 0 < u z) :
    ContinuousAt (fun v : α → ℝ => fordBTProductObjective c v) u :=
  (continuousOn_fordBTProductObjective_fullSupport c).continuousAt
    (fullSupport_set_mem_nhds hu)

/-- Ford's product objective is continuous at every point of the closed simplex
under nonnegative counts and Ford strong connectivity. -/
theorem continuousWithinAt_fordBTProductObjective_simplex
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hconn : FordStronglyConnected c)
    (hu : IsLottery u) :
    ContinuousWithinAt (fun v : α → ℝ => fordBTProductObjective c v)
      {v : α → ℝ | IsLottery v} u := by
  rcases hu.fullSupport_or_boundary with hfull | hboundary
  · exact (continuousAt_fordBTProductObjective_fullSupport
      (c := c) hfull.1).continuousWithinAt
  · exact continuousWithinAt_fordBTProductObjective_lottery_boundary
      hc hconn hu hboundary

/-- Closed-simplex continuity of Ford's product objective under the hypotheses
of Ford/Zermelo. -/
theorem continuousOn_fordBTProductObjective_simplex_of_stronglyConnected
    {c : α → α → ℝ}
    (hc : ∀ x y : α, 0 ≤ c x y)
    (hconn : FordStronglyConnected c) :
    ContinuousOn (fun u : α → ℝ => fordBTProductObjective c u)
      {u : α → ℝ | IsLottery u} := by
  intro u hu
  exact continuousWithinAt_fordBTProductObjective_simplex hc hconn hu

/-- Any positive point has strictly larger Ford product likelihood than a
Ford-connected simplex-boundary point. This is the order-theoretic core of
Ford's boundary exclusion argument. -/
theorem fordBTProductObjective_boundary_lt_of_pos
    {c : α → α → ℝ} {u v : α → ℝ}
    (hconn : FordStronglyConnected c)
    (hnonneg : ∀ z : α, 0 ≤ u z)
    (hsum : Finset.sum Finset.univ (fun z : α => u z) = 1)
    {x : α}
    (hx : u x = 0)
    (hv : ∀ z : α, 0 < v z) :
    fordBTProductObjective c u < fordBTProductObjective c v := by
  rw [fordBTProductObjective_eq_zero_of_simplex_boundary hconn hnonneg hsum hx]
  exact fordBTProductObjective_pos_of_pos hv

/-- Full-support lotteries strictly beat simplex-boundary lotteries for
Ford's product likelihood under Ford strong connectivity. -/
theorem fordBTProductObjective_lottery_boundary_lt_fullSupport
    {c : α → α → ℝ} {u v : α → ℝ}
    (hconn : FordStronglyConnected c)
    (hu : IsLottery u)
    (hboundary : ∃ x : α, u x = 0)
    (hv : IsFullSupportLottery v) :
    fordBTProductObjective c u < fordBTProductObjective c v := by
  rw [fordBTProductObjective_eq_zero_of_lottery_boundary hconn hu hboundary]
  exact fordBTProductObjective_pos_of_pos hv.1

/-- Under Ford connectivity, the positive vector that generates Ford's
synthetic matrix is a closed-simplex product-likelihood maximizer for that
synthetic matrix. -/
theorem HasFordClosedSimplexProductMaximizer_fordSyntheticCount
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hu : IsFullSupportLottery u) :
    HasFordClosedSimplexProductMaximizer (fordSyntheticCount c u) u := by
  refine ⟨IsFullSupportLottery.toLottery hu, ?_⟩
  intro v hv
  rcases hv.fullSupport_or_boundary with hvfull | hboundary
  · exact fordBTProductObjective_fordSyntheticCount_le_self hc.2 hu.1 hvfull.1
  · have hzero :
        fordBTProductObjective (fordSyntheticCount c u) v = 0 :=
      fordBTProductObjective_eq_zero_of_lottery_boundary
        (FordStronglyConnected_fordSyntheticCount hc.2 hu.1 hconn)
        hv hboundary
    rw [hzero]
    exact (fordBTProductObjective_pos_of_pos
      (c := fordSyntheticCount c u) hu.1).le

omit [DecidableEq α] in
/-- Every nonempty finite type admits a full-support lottery. -/
lemma exists_fullSupportLottery [Nonempty α] :
    ∃ v : α → ℝ, IsFullSupportLottery v := by
  classical
  refine ⟨fun _ => ((Fintype.card α : ℝ)⁻¹), ?_⟩
  have hcardpos_nat : 0 < Fintype.card α :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcardpos : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast hcardpos_nat
  constructor
  · intro x
    exact inv_pos.mpr hcardpos
  · simp [Finset.sum_const, hcardpos.ne']

/-- Weierstrass step for Ford's compactness proof: a Ford product objective
that is continuous on the closed finite simplex attains a closed-simplex
maximum.  The remaining hard Ford existence work is then continuity/first-order
analysis for the chosen objective, not compactness itself. -/
theorem exists_fordClosedSimplexProductMaximizer_of_continuousOn
    [Nonempty α]
    {c : α → α → ℝ}
    (hcont :
      ContinuousOn (fun u : α → ℝ => fordBTProductObjective c u)
        {u : α → ℝ | IsLottery u}) :
    ∃ u : α → ℝ, HasFordClosedSimplexProductMaximizer c u := by
  classical
  have hcompact : IsCompact {u : α → ℝ | IsLottery u} :=
    isCompact_setOf_isLottery
  have hnonempty : ({u : α → ℝ | IsLottery u} : Set (α → ℝ)).Nonempty := by
    rcases exists_fullSupportLottery (α := α) with ⟨u, hu⟩
    exact ⟨u, hu.toLottery⟩
  rcases hcompact.exists_isMaxOn hnonempty hcont with
    ⟨u, hu, humax⟩
  exact ⟨u, hu, fun v hv => (isMaxOn_iff.mp humax) v hv⟩

/-- Ford's boundary exclusion for a closed-simplex product maximizer: if the
simplex has any full-support point, a Ford-connected closed-simplex maximizer
must itself have full support. -/
theorem HasFordClosedSimplexProductMaximizer.fullSupport_of_stronglyConnected
    {c : α → α → ℝ} {u : α → ℝ}
    (hmax : HasFordClosedSimplexProductMaximizer c u)
    (hconn : FordStronglyConnected c)
    (hinterior : ∃ v : α → ℝ, IsFullSupportLottery v) :
    IsFullSupportLottery u := by
  refine ⟨?_, hmax.1.2⟩
  intro x
  by_contra hxpos
  have hx0 : u x = 0 :=
    le_antisymm (le_of_not_gt hxpos) (hmax.1.1 x)
  rcases hinterior with ⟨v, hv⟩
  have hlt :
      fordBTProductObjective c u < fordBTProductObjective c v :=
    fordBTProductObjective_lottery_boundary_lt_fullSupport
      hconn hmax.1 ⟨x, hx0⟩ hv
  have hle :
      fordBTProductObjective c v ≤ fordBTProductObjective c u :=
    hmax.2 v (IsFullSupportLottery.toLottery hv)
  exact not_lt_of_ge hle hlt

/-- A closed-simplex product maximizer is a full-support product maximizer once
Ford connectivity rules out boundary maximizers. This is the non-unique part
of Ford's compactness-to-interior step. -/
theorem HasFordClosedSimplexProductMaximizer.to_fullSupportProductMaximizer
    {c : α → α → ℝ} {u : α → ℝ}
    (hmax : HasFordClosedSimplexProductMaximizer c u)
    (hconn : FordStronglyConnected c)
    (hinterior : ∃ v : α → ℝ, IsFullSupportLottery v) :
    IsFullSupportLottery u ∧
      ∀ v : α → ℝ, IsFullSupportLottery v →
        fordBTProductObjective c v ≤ fordBTProductObjective c u :=
  ⟨hmax.fullSupport_of_stronglyConnected hconn hinterior,
    fun v hv => hmax.2 v (IsFullSupportLottery.toLottery hv)⟩

/-- On a nonempty finite type, Ford connectivity alone rules out boundary
closed-simplex product maximizers. -/
theorem HasFordClosedSimplexProductMaximizer.fullSupport_of_stronglyConnected'
    [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hmax : HasFordClosedSimplexProductMaximizer c u)
    (hconn : FordStronglyConnected c) :
    IsFullSupportLottery u :=
  hmax.fullSupport_of_stronglyConnected hconn exists_fullSupportLottery

/-- Non-unique closed-simplex maximizers restrict to full-support product
maximizers on nonempty finite types under Ford connectivity. -/
theorem HasFordClosedSimplexProductMaximizer.to_fullSupportProductMaximizer'
    [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hmax : HasFordClosedSimplexProductMaximizer c u)
    (hconn : FordStronglyConnected c) :
    IsFullSupportLottery u ∧
      ∀ v : α → ℝ, IsFullSupportLottery v →
        fordBTProductObjective c v ≤ fordBTProductObjective c u :=
  hmax.to_fullSupportProductMaximizer hconn exists_fullSupportLottery

/-- Compactness plus Ford's boundary exclusion gives a full-support
product-likelihood maximizer whenever the Ford objective is continuous on the
closed finite simplex. -/
theorem exists_fordFullSupportProductMaximizer_of_continuousOn
    [Nonempty α]
    {c : α → α → ℝ}
    (hconn : FordStronglyConnected c)
    (hcont :
      ContinuousOn (fun u : α → ℝ => fordBTProductObjective c u)
        {u : α → ℝ | IsLottery u}) :
    ∃ u : α → ℝ,
      IsFullSupportLottery u ∧
        ∀ v : α → ℝ, IsFullSupportLottery v →
          fordBTProductObjective c v ≤ fordBTProductObjective c u := by
  rcases exists_fordClosedSimplexProductMaximizer_of_continuousOn
      hcont with ⟨u, hmax⟩
  exact ⟨u, hmax.to_fullSupportProductMaximizer' hconn⟩

/-- Compactness plus boundary exclusion also gives a full-support
log-likelihood maximizer, by taking logarithms of the product-likelihood
maximizer inequality on the positive simplex. -/
theorem exists_fordFullSupportBTObjectiveMaximizer_of_continuousOn
    [Nonempty α]
    {c : α → α → ℝ}
    (hconn : FordStronglyConnected c)
    (hcont :
      ContinuousOn (fun u : α → ℝ => fordBTProductObjective c u)
        {u : α → ℝ | IsLottery u}) :
    ∃ u : α → ℝ,
      IsFullSupportLottery u ∧
        ∀ v : α → ℝ, IsFullSupportLottery v →
          btObjective c v ≤ btObjective c u := by
  rcases exists_fordFullSupportProductMaximizer_of_continuousOn
      hconn hcont with ⟨u, hu, hmax⟩
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hvpos := fordBTProductObjective_pos_of_pos (c := c) hv.1
  have hupos := fordBTProductObjective_pos_of_pos (c := c) hu.1
  calc
    btObjective c v =
        Real.log (fordBTProductObjective c v) :=
          (Real_log_fordBTProductObjective_eq_btObjective hv.1).symm
    _ ≤ Real.log (fordBTProductObjective c u) :=
        (Real.log_le_log_iff hvpos hupos).mpr (hmax v hv)
    _ = btObjective c u :=
        Real_log_fordBTProductObjective_eq_btObjective hu.1

/-- Compactness, Ford boundary exclusion, and the first-order stationarity
argument together produce a positive solution of Ford's displayed equations
whenever the product objective is continuous on the closed finite simplex. -/
theorem exists_positive_ford_equation_solution_of_continuousOn
    [Nonempty α]
    {c : α → α → ℝ}
    (hconn : FordStronglyConnected c)
    (hcont :
      ContinuousOn (fun u : α → ℝ => fordBTProductObjective c u)
        {u : α → ℝ | IsLottery u}) :
    ∃ u : α → ℝ,
      (∀ x : α, 0 < u x) ∧ SatisfiesFordBTEquations c u := by
  rcases exists_fordFullSupportBTObjectiveMaximizer_of_continuousOn
      hconn hcont with ⟨u, hu, hmax⟩
  exact ⟨u, hu.1,
    SatisfiesFordBTEquations_of_fullSupportBTObjectiveMaximizer hu hmax⟩

/-- Ford/Zermelo positive-equation existence for finite strongly connected
nonnegative count matrices, proved from compactness, closed-simplex
continuity, boundary exclusion, and the first-order equations. -/
theorem exists_positive_ford_equation_solution
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ,
      (∀ x : α, 0 < u x) ∧ SatisfiesFordBTEquations c u :=
  exists_positive_ford_equation_solution_of_continuousOn hconn
    (continuousOn_fordBTProductObjective_simplex_of_stronglyConnected
      hc.2 hconn)

/-- The synthetic closed-simplex maximizer theorem, projected to the
full-support product-maximizer statement by the general boundary-exclusion
bridge. -/
theorem HasFordClosedSimplexProductMaximizer_fordSyntheticCount_to_fullSupportProductMaximizer
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hu : IsFullSupportLottery u) :
    IsFullSupportLottery u ∧
      ∀ v : α → ℝ, IsFullSupportLottery v →
        fordBTProductObjective (fordSyntheticCount c u) v ≤
          fordBTProductObjective (fordSyntheticCount c u) u :=
  HasFordClosedSimplexProductMaximizer.to_fullSupportProductMaximizer
    (HasFordClosedSimplexProductMaximizer_fordSyntheticCount hc hconn hu)
    (FordStronglyConnected_fordSyntheticCount hc.2 hu.1 hconn) ⟨u, hu⟩

/-- The displayed Bradley--Terry equations are invariant under Ford simplex
normalization. -/
lemma SatisfiesBTDisplayedEquation_btNormalize
    [Nonempty α]
    {w : α → α → ℝ} {B u : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hBT : SatisfiesBTDisplayedEquation w B u) :
    SatisfiesBTDisplayedEquation w B (btNormalize u) := by
  intro x
  have hden_pos := btNormalize_den_pos (α := α) hu
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y =>
          w x y *
            (btNormalize u x / (btNormalize u x + btNormalize u y)))
        =
      Finset.sum (Finset.univ.erase x)
        (fun y => w x y * (u x / (u x + u y))) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          have hxy : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
          unfold btNormalize
          field_simp [hden_pos.ne', hxy]
    _ = B x := hBT x

/-- The displayed Bradley--Terry equations are invariant under multiplying
all strengths by the same positive scalar. -/
lemma SatisfiesBTDisplayedEquation_scaled
    {w : α → α → ℝ} {B u : α → ℝ} {a : ℝ}
    (ha : 0 < a)
    (hu : ∀ x : α, 0 < u x)
    (hBT : SatisfiesBTDisplayedEquation w B u) :
    SatisfiesBTDisplayedEquation w B (fun x => a * u x) := by
  intro x
  calc
    Finset.sum (Finset.univ.erase x)
        (fun y => w x y * ((a * u x) / ((a * u x) + (a * u y))))
        =
      Finset.sum (Finset.univ.erase x)
        (fun y => w x y * (u x / (u x + u y))) := by
          refine Finset.sum_congr rfl ?_
          intro y _hy
          have hxy : u x + u y ≠ 0 := (add_pos (hu x) (hu y)).ne'
          field_simp [ha.ne', hxy]
    _ = B x := hBT x

/-- Ford's strict-count Bradley--Terry equations are invariant under positive
scalar multiplication of the strength vector. -/
lemma SatisfiesFordBTEquations_scaled
    {c : α → α → ℝ} {u : α → ℝ} {a : ℝ}
    (ha : 0 < a)
    (hu : ∀ x : α, 0 < u x)
    (hBT : SatisfiesFordBTEquations c u) :
    SatisfiesFordBTEquations c (fun x => a * u x) :=
  SatisfiesBTDisplayedEquation_scaled ha hu hBT

/-- Ford's strict-count Bradley--Terry equations are invariant under Ford
simplex normalization. -/
lemma SatisfiesFordBTEquations_btNormalize
    [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hBT : SatisfiesFordBTEquations c u) :
    SatisfiesFordBTEquations c (btNormalize u) :=
  SatisfiesBTDisplayedEquation_btNormalize hu hBT

/-- Unnormalized positive solutions of Ford's displayed equations are unique
up to a positive scalar. -/
theorem SatisfiesFordBTEquations_positive_unique_ray
    [Nonempty α]
    {c : α → α → ℝ} {u v : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hu : ∀ x : α, 0 < u x)
    (hv : ∀ x : α, 0 < v x)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c v) :
    ∃ a : ℝ, 0 < a ∧ v = fun x => a * u x := by
  have hnorm :
      btNormalize u = btNormalize v :=
    SatisfiesFordBTEquations_unique_of_stronglyConnected
      hc hconn
      (btNormalize_fullSupport hu)
      (btNormalize_fullSupport hv)
      (SatisfiesFordBTEquations_btNormalize hu hBTu)
      (SatisfiesFordBTEquations_btNormalize hv hBTv)
  let Su : ℝ := Finset.sum Finset.univ (fun z : α => u z)
  let Sv : ℝ := Finset.sum Finset.univ (fun z : α => v z)
  have hSu : 0 < Su := by
    dsimp [Su]
    exact btNormalize_den_pos (α := α) hu
  have hSv : 0 < Sv := by
    dsimp [Sv]
    exact btNormalize_den_pos (α := α) hv
  refine ⟨Sv / Su, div_pos hSv hSu, ?_⟩
  funext x
  have hx := congrArg (fun f : α → ℝ => f x) hnorm
  dsimp [btNormalize, Su, Sv] at hx ⊢
  calc
    v x = (v x / Sv) * Sv := by
      field_simp [hSv.ne']
    _ = (u x / Su) * Sv := by
      rw [← hx]
    _ = (Sv / Su) * u x := by
      field_simp [hSu.ne']

/-- A normalized full-support solution of Ford's displayed equations is a
Bradley--Terry strength vector for Ford pair totals and strict wins. -/
theorem IsBTStrength_of_fullSupport_ford_equations
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : IsFullSupportLottery u)
    (hBT : SatisfiesFordBTEquations c u) :
    IsBTStrength (fordPairTotal c) c u := by
  refine ⟨hu, ?_⟩
  intro x
  have hx := hBT x
  simpa [SatisfiesFordBTEquations, fordWinCount] using hx

/-- Ford/Zermelo uniqueness for normalized Bradley--Terry strengths, derived
from the displayed-equation max-ratio proof rather than treated as an external
input. -/
theorem IsBTStrength_unique_of_ford_stronglyConnected
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∀ u v : α → ℝ,
      IsBTStrength (fordPairTotal c) c u →
        IsBTStrength (fordPairTotal c) c v →
          u = v := by
  intro u v hu hv
  exact SatisfiesFordBTEquations_unique_of_stronglyConnected
    hc hconn hu.1 hv.1
    (by
      intro x
      simpa [SatisfiesFordBTEquations, fordWinCount] using hu.2 x)
    (by
      intro x
      simpa [SatisfiesFordBTEquations, fordWinCount] using hv.2 x)

/-- The positive vector used to generate Ford's synthetic matrix is a normalized
Bradley--Terry strength vector for that synthetic matrix. -/
theorem IsBTStrength_fordSyntheticCount
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : IsFullSupportLottery u) :
    IsBTStrength
      (fordPairTotal (fordSyntheticCount c u))
      (fordSyntheticCount c u) u :=
  IsBTStrength_of_fullSupport_ford_equations hu
    (SatisfiesFordBTEquations_fordSyntheticCount hu.1)

/-- If two full-support vectors solve Ford's displayed equations for the same
original matrix, then `u` is a normalized Bradley--Terry strength vector for the
synthetic matrix generated by `v`. -/
theorem IsBTStrength_fordSyntheticCount_of_same_base_solution
    {c : α → α → ℝ} {u v : α → ℝ}
    (hu : IsFullSupportLottery u)
    (hv : IsFullSupportLottery v)
    (hBTu : SatisfiesFordBTEquations c u)
    (hBTv : SatisfiesFordBTEquations c v) :
    IsBTStrength
      (fordPairTotal (fordSyntheticCount c v))
      (fordSyntheticCount c v) u :=
  IsBTStrength_of_fullSupport_ford_equations hu
    (SatisfiesFordBTEquations_fordSyntheticCount_of_same_base_solution
      hu.1 hv.1 hBTu hBTv)

/-- Any Bradley--Terry strength vector for Ford pair totals and strict wins
satisfies Ford's displayed equations. -/
theorem SatisfiesFordBTEquations_of_isBTStrength
    {c : α → α → ℝ} {u : α → ℝ}
    (hBT : IsBTStrength (fordPairTotal c) c u) :
    SatisfiesFordBTEquations c u := by
  intro x
  simpa [SatisfiesFordBTEquations, fordWinCount] using hBT.2 x

/-- A normalized Bradley--Terry strength for a Ford-connected count matrix
already supplies the full Ford-style certificate: maximum likelihood and
uniqueness are proved internally above. -/
theorem HasFordBTPropCertificate_of_isBTStrength
    [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hBT : IsBTStrength (fordPairTotal c) c u) :
    HasFordBTPropCertificate (fordPairTotal c) c u :=
  ⟨hBT,
    HasFordNormalizedBTMaximizer_of_satisfiesFordEquations
      hc hconn hBT.1 (SatisfiesFordBTEquations_of_isBTStrength hBT),
    fun v hv =>
      IsBTStrength_unique_of_ford_stronglyConnected
        hc hconn v u hv hBT⟩

/-- A positive vector satisfying Ford's displayed equations gives the
simplex-normalized `IsBTStrength` representative for the strict-count matrix. -/
theorem IsBTStrength_of_ford_equations_btNormalize
    [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hu : ∀ x : α, 0 < u x)
    (hBT : SatisfiesFordBTEquations c u) :
    IsBTStrength (fordPairTotal c) c (btNormalize u) := by
  refine ⟨btNormalize_fullSupport hu, ?_⟩
  intro x
  have hx := SatisfiesBTDisplayedEquation_btNormalize hu hBT x
  simpa [SatisfiesFordBTEquations, fordWinCount] using hx

/-- An unnormalized positive solution of Ford's displayed equations gives the
full normalized Ford-style certificate after simplex normalization. -/
theorem HasFordBTPropCertificate_of_positive_ford_equations
    [Nonempty α]
    {c : α → α → ℝ} {u : α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c)
    (hu : ∀ x : α, 0 < u x)
    (hBT : SatisfiesFordBTEquations c u) :
    HasFordBTPropCertificate (fordPairTotal c) c (btNormalize u) :=
  HasFordBTPropCertificate_of_isBTStrength hc hconn
    (IsBTStrength_of_ford_equations_btNormalize hu hBT)

/-- Interface schema for Ford/Zermelo existence over a fixed finite alternative
type: every strongly connected Ford count matrix admits a positive, not
necessarily normalized, solution of Ford's displayed equations.  It is not an
external input: `FordZermeloBTTheorem_finite` below proves it from the
closed-simplex product objective, and the maximum-likelihood and uniqueness
parts are then derived from this positive solution. -/
def FordZermeloBTTheorem
    (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α] : Prop :=
  ∀ c : α → α → ℝ,
    IsFordCountMatrix c →
      FordStronglyConnected c →
        ∃ u : α → ℝ,
          (∀ x : α, 0 < u x) ∧ SatisfiesFordBTEquations c u

/-- A closed-simplex continuity theorem for every Ford-connected count matrix
implies the reduced Ford/Zermelo positive-equation theorem.  The global
continuity of the multiplicative objective on the closed simplex is proved
below and supplies this hypothesis. -/
theorem FordZermeloBTTheorem_of_continuousOn
    [Nonempty α]
    (hcont : ∀ c : α → α → ℝ,
      IsFordCountMatrix c →
        FordStronglyConnected c →
          ContinuousOn (fun u : α → ℝ => fordBTProductObjective c u)
            {u : α → ℝ | IsLottery u}) :
    FordZermeloBTTheorem α := by
  intro c hc hconn
  exact exists_positive_ford_equation_solution_of_continuousOn
    hconn (hcont c hc hconn)

/-- The finite Ford/Zermelo positive-equation theorem, with no remaining
external mathematical input. -/
theorem FordZermeloBTTheorem_finite
    [Nonempty α] :
    FordZermeloBTTheorem α := by
  intro c hc hconn
  exact exists_positive_ford_equation_solution hc hconn

/-- The reduced Ford/Zermelo input, unpacked at a concrete count matrix. -/
theorem exists_positive_ford_equation_solution_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ,
      (∀ x : α, 0 < u x) ∧ SatisfiesFordBTEquations c u :=
  hFord c hc hconn

/-- Ford/Zermelo unpacked using Ford's original partition formulation. -/
theorem exists_positive_ford_equation_solution_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃ u : α → ℝ,
      (∀ x : α, 0 < u x) ∧ SatisfiesFordBTEquations c u :=
  exists_positive_ford_equation_solution_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- A Ford/Zermelo theorem instance supplies the exact Ford-style certificate
used by the DPO/RTBT bridge. -/
theorem exists_ford_BTProp_certificate_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ, HasFordBTPropCertificate (fordPairTotal c) c u := by
  rcases hFord c hc hconn with ⟨u, hu, hBT⟩
  exact ⟨btNormalize u,
    HasFordBTPropCertificate_of_positive_ford_equations hc hconn hu hBT⟩

/-- Ford/Zermelo certificate extraction using Ford's original partition
formulation. -/
theorem exists_ford_BTProp_certificate_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃ u : α → ℝ, HasFordBTPropCertificate (fordPairTotal c) c u :=
  exists_ford_BTProp_certificate_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- Paper-facing Ford/Zermelo existence and uniqueness for normalized
Bradley--Terry strength vectors.  The external input only provides a positive
equation solution; Lean derives the normalized representative and its
uniqueness. -/
theorem exists_unique_ford_BTStrength_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, IsBTStrength (fordPairTotal c) c u := by
  rcases exists_ford_BTProp_certificate_of_ford_zermelo hFord hc hconn with
    ⟨u, hcert⟩
  exact ⟨u, hcert.1, hcert.2.2⟩

/-- Partition-assumption version of the paper-facing normalized
Bradley--Terry strength existence and uniqueness theorem. -/
theorem exists_unique_ford_BTStrength_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃! u : α → ℝ, IsBTStrength (fordPairTotal c) c u :=
  exists_unique_ford_BTStrength_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- Paper-facing Ford/Zermelo existence and uniqueness for normalized
log-likelihood maximizers. -/
theorem exists_unique_ford_normalizedBTMaximizer_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasFordNormalizedBTMaximizer c u := by
  rcases exists_ford_BTProp_certificate_of_ford_zermelo hFord hc hconn with
    ⟨u, hcert⟩
  refine ⟨u, hcert.2.1, ?_⟩
  intro v hv
  exact hcert.2.1.2.2 v hv.1 hv.2.1

/-- Partition-assumption version of normalized log-likelihood maximizer
existence and uniqueness. -/
theorem exists_unique_ford_normalizedBTMaximizer_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃! u : α → ℝ, HasFordNormalizedBTMaximizer c u :=
  exists_unique_ford_normalizedBTMaximizer_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- Ford's original multiplicative likelihood form: a Ford/Zermelo instance
gives a unique normalized product-likelihood maximizer. -/
theorem exists_unique_ford_normalizedBTProductMaximizer_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasFordNormalizedBTProductMaximizer c u := by
  rcases exists_ford_BTProp_certificate_of_ford_zermelo hFord hc hconn with
    ⟨u, hcert⟩
  refine ⟨u,
    HasFordNormalizedBTProductMaximizer_iff_normalizedBTMaximizer.mpr hcert.2.1,
    ?_⟩
  intro v hv
  have hvlog :
      HasFordNormalizedBTMaximizer c v :=
    HasFordNormalizedBTProductMaximizer_iff_normalizedBTMaximizer.mp hv
  exact hcert.2.1.2.2 v hvlog.1 hvlog.2.1

/-- Partition-assumption version of Ford's original multiplicative
likelihood existence and uniqueness theorem. -/
theorem exists_unique_ford_normalizedBTProductMaximizer_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃! u : α → ℝ, HasFordNormalizedBTProductMaximizer c u :=
  exists_unique_ford_normalizedBTProductMaximizer_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- The Ford-style certificate is unique in its selected normalized strength
vector. -/
theorem exists_unique_ford_BTProp_certificate_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasFordBTPropCertificate (fordPairTotal c) c u := by
  rcases exists_ford_BTProp_certificate_of_ford_zermelo hFord hc hconn with
    ⟨u, hcert⟩
  exact ⟨u, hcert, fun v hv => hcert.2.2 v hv.1⟩

/-- Partition-assumption version of Ford-style certificate existence and
uniqueness. -/
theorem exists_unique_ford_BTProp_certificate_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃! u : α → ℝ, HasFordBTPropCertificate (fordPairTotal c) c u :=
  exists_unique_ford_BTProp_certificate_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- The canonical normalized Bradley--Terry strength vector selected directly
from Ford/Zermelo's stronger normalized maximum-likelihood certificate. -/
noncomputable def selectedFordBTOfFordZermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    (c : α → α → ℝ)
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) : α → ℝ :=
  Classical.choose
    (exists_ford_BTProp_certificate_of_ford_zermelo hFord hc hconn)

theorem selectedFordBTOfFordZermelo_certificate
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    HasFordBTPropCertificate (fordPairTotal c) c
      (selectedFordBTOfFordZermelo hFord c hc hconn) :=
  Classical.choose_spec
    (exists_ford_BTProp_certificate_of_ford_zermelo hFord hc hconn)

theorem selectedFordBTOfFordZermelo_isBTStrength
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    IsBTStrength (fordPairTotal c) c
      (selectedFordBTOfFordZermelo hFord c hc hconn) :=
  (selectedFordBTOfFordZermelo_certificate hFord hc hconn).1

theorem selectedFordBTOfFordZermelo_fullSupport
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    IsFullSupportLottery
      (selectedFordBTOfFordZermelo hFord c hc hconn) :=
  (selectedFordBTOfFordZermelo_isBTStrength hFord hc hconn).1

theorem selectedFordBTOfFordZermelo_pos
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∀ x : α, 0 < selectedFordBTOfFordZermelo hFord c hc hconn x :=
  (selectedFordBTOfFordZermelo_fullSupport hFord hc hconn).1

theorem selectedFordBTOfFordZermelo_satisfiesFordEquations
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    SatisfiesFordBTEquations c
      (selectedFordBTOfFordZermelo hFord c hc hconn) :=
  SatisfiesFordBTEquations_of_isBTStrength
    (selectedFordBTOfFordZermelo_isBTStrength hFord hc hconn)

theorem selectedFordBTOfFordZermelo_normalizedMaximizer
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    HasFordNormalizedBTMaximizer c
      (selectedFordBTOfFordZermelo hFord c hc hconn) :=
  (selectedFordBTOfFordZermelo_certificate hFord hc hconn).2.1

theorem selectedFordBTOfFordZermelo_productMaximizer
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    HasFordNormalizedBTProductMaximizer c
      (selectedFordBTOfFordZermelo hFord c hc hconn) :=
  HasFordNormalizedBTProductMaximizer_iff_normalizedBTMaximizer.mpr
    (selectedFordBTOfFordZermelo_normalizedMaximizer hFord hc hconn)

theorem selectedFordBTOfFordZermelo_unique_isBTStrength
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∀ v : α → ℝ,
      IsBTStrength (fordPairTotal c) c v →
        v = selectedFordBTOfFordZermelo hFord c hc hconn :=
  (selectedFordBTOfFordZermelo_certificate hFord hc hconn).2.2

/-- Ford/Zermelo uniqueness, stated directly for normalized solutions of
Ford's displayed equations. -/
theorem selectedFordBTOfFordZermelo_unique_satisfiesFordEquations
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∀ v : α → ℝ,
      IsFullSupportLottery v →
        SatisfiesFordBTEquations c v →
          v = selectedFordBTOfFordZermelo hFord c hc hconn := by
  intro v hv hEq
  refine selectedFordBTOfFordZermelo_unique_isBTStrength hFord hc hconn v ?_
  exact IsBTStrength_of_fullSupport_ford_equations hv hEq

theorem selectedFordBTOfFordZermelo_positiveMaximizerRay
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    HasBTPositiveMaximizerRay c
      (selectedFordBTOfFordZermelo hFord c hc hconn) :=
  HasBTPositiveMaximizerRay_of_ford_normalized_maximizer
    (selectedFordBTOfFordZermelo_normalizedMaximizer hFord hc hconn)

/-- The Ford/Zermelo theorem also supplies the existing combined `BTProp`
certificate after the normalized-maximizer-to-ray bridge proved in `DPO`. -/
theorem exists_BTProp_certificate_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ, HasBTPropCertificate (fordPairTotal c) c u := by
  rcases exists_ford_BTProp_certificate_of_ford_zermelo hFord hc hconn with
    ⟨u, hu⟩
  exact ⟨u, HasBTPropCertificate_of_ford_certificate hu⟩

/-- Combined `BTProp` certificate extraction using Ford's original partition
formulation. -/
theorem exists_BTProp_certificate_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃ u : α → ℝ, HasBTPropCertificate (fordPairTotal c) c u :=
  exists_BTProp_certificate_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- The combined `BTProp` certificate is unique in its selected normalized
strength vector. -/
theorem exists_unique_BTProp_certificate_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasBTPropCertificate (fordPairTotal c) c u := by
  rcases exists_BTProp_certificate_of_ford_zermelo hFord hc hconn with
    ⟨u, hcert⟩
  exact ⟨u, hcert, fun v hv => hcert.2.2 v hv.1⟩

/-- Partition-assumption version of combined `BTProp` certificate existence
and uniqueness. -/
theorem exists_unique_BTProp_certificate_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃! u : α → ℝ, HasBTPropCertificate (fordPairTotal c) c u :=
  exists_unique_BTProp_certificate_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- Ford/Zermelo also supplies the positive-ray maximizer interface used
directly by the DPO change-of-variables proof. -/
theorem exists_BTPositiveMaximizerRay_of_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ, HasBTPositiveMaximizerRay c u := by
  rcases exists_BTProp_certificate_of_ford_zermelo hFord hc hconn with
    ⟨u, hcert⟩
  exact ⟨u, hcert.2.1⟩

/-- Partition-assumption version of the positive-ray maximizer extraction. -/
theorem exists_BTPositiveMaximizerRay_of_ford_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃ u : α → ℝ, HasBTPositiveMaximizerRay c u :=
  exists_BTPositiveMaximizerRay_of_ford_zermelo
    hFord hc (FordStronglyConnected_of_partitionAssumption hpart)

/-- The proved finite Ford/Zermelo theorem supplies the Ford-style certificate
without an external Ford/Zermelo hypothesis. -/
theorem exists_ford_BTProp_certificate
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ, HasFordBTPropCertificate (fordPairTotal c) c u :=
  exists_ford_BTProp_certificate_of_ford_zermelo
    FordZermeloBTTheorem_finite hc hconn

/-- The proved finite Ford/Zermelo theorem gives existence and uniqueness of
the normalized Ford Bradley--Terry strength vector. -/
theorem exists_unique_ford_BTStrength
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, IsBTStrength (fordPairTotal c) c u :=
  exists_unique_ford_BTStrength_of_ford_zermelo
    FordZermeloBTTheorem_finite hc hconn

/-- The proved finite Ford/Zermelo theorem gives the unique normalized
additive log-likelihood maximizer. -/
theorem exists_unique_ford_normalizedBTMaximizer
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasFordNormalizedBTMaximizer c u :=
  exists_unique_ford_normalizedBTMaximizer_of_ford_zermelo
    FordZermeloBTTheorem_finite hc hconn

/-- The proved finite Ford/Zermelo theorem gives the unique normalized product
likelihood maximizer. -/
theorem exists_unique_ford_normalizedBTProductMaximizer
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasFordNormalizedBTProductMaximizer c u :=
  exists_unique_ford_normalizedBTProductMaximizer_of_ford_zermelo
    FordZermeloBTTheorem_finite hc hconn

/-- The proved finite Ford/Zermelo theorem gives the unique Ford-style
`BTProp` certificate representative. -/
theorem exists_unique_ford_BTProp_certificate
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasFordBTPropCertificate (fordPairTotal c) c u :=
  exists_unique_ford_BTProp_certificate_of_ford_zermelo
    FordZermeloBTTheorem_finite hc hconn

/-- The proved finite Ford/Zermelo theorem supplies the combined `BTProp`
certificate without an external Ford/Zermelo hypothesis. -/
theorem exists_BTProp_certificate
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ, HasBTPropCertificate (fordPairTotal c) c u :=
  exists_BTProp_certificate_of_ford_zermelo
    FordZermeloBTTheorem_finite hc hconn

/-- The proved finite Ford/Zermelo theorem gives the unique combined `BTProp`
certificate representative. -/
theorem exists_unique_BTProp_certificate
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃! u : α → ℝ, HasBTPropCertificate (fordPairTotal c) c u :=
  exists_unique_BTProp_certificate_of_ford_zermelo
    FordZermeloBTTheorem_finite hc hconn

/-- The proved finite Ford/Zermelo theorem supplies the positive-ray maximizer
interface used by the DPO/RTBT bridge. -/
theorem exists_BTPositiveMaximizerRay
    [Nonempty α]
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ, HasBTPositiveMaximizerRay c u :=
  exists_BTPositiveMaximizerRay_of_ford_zermelo
    FordZermeloBTTheorem_finite hc hconn

/-- The canonical normalized Bradley--Terry strength vector selected from the
Ford/Zermelo theorem for a concrete count matrix. -/
noncomputable def selectedBTOfFordZermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    (c : α → α → ℝ)
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) : α → ℝ :=
  Classical.choose
    (exists_BTProp_certificate_of_ford_zermelo hFord hc hconn)

theorem selectedBTOfFordZermelo_certificate
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    HasBTPropCertificate (fordPairTotal c) c
      (selectedBTOfFordZermelo hFord c hc hconn) :=
  Classical.choose_spec
    (exists_BTProp_certificate_of_ford_zermelo hFord hc hconn)

theorem selectedBTOfFordZermelo_isBTStrength
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    IsBTStrength (fordPairTotal c) c
      (selectedBTOfFordZermelo hFord c hc hconn) :=
  (selectedBTOfFordZermelo_certificate hFord hc hconn).1

theorem selectedBTOfFordZermelo_fullSupport
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    IsFullSupportLottery
      (selectedBTOfFordZermelo hFord c hc hconn) :=
  (selectedBTOfFordZermelo_isBTStrength hFord hc hconn).1

theorem selectedBTOfFordZermelo_pos
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∀ x : α, 0 < selectedBTOfFordZermelo hFord c hc hconn x :=
  (selectedBTOfFordZermelo_fullSupport hFord hc hconn).1

theorem selectedBTOfFordZermelo_satisfiesFordEquations
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    SatisfiesFordBTEquations c
      (selectedBTOfFordZermelo hFord c hc hconn) :=
  SatisfiesFordBTEquations_of_isBTStrength
    (selectedBTOfFordZermelo_isBTStrength hFord hc hconn)

theorem selectedBTOfFordZermelo_unique_isBTStrength
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∀ v : α → ℝ,
      IsBTStrength (fordPairTotal c) c v →
        v = selectedBTOfFordZermelo hFord c hc hconn :=
  (selectedBTOfFordZermelo_certificate hFord hc hconn).2.2

/-- The two canonical selectors exposed by this file are definitionally chosen
from different certificates but coincide by Ford/Zermelo uniqueness. -/
theorem selectedBTOfFordZermelo_eq_selectedFordBTOfFordZermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    selectedBTOfFordZermelo hFord c hc hconn =
      selectedFordBTOfFordZermelo hFord c hc hconn :=
  selectedFordBTOfFordZermelo_unique_isBTStrength hFord hc hconn
    (selectedBTOfFordZermelo hFord c hc hconn)
    (selectedBTOfFordZermelo_isBTStrength hFord hc hconn)

theorem selectedBTOfFordZermelo_productMaximizer
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    HasFordNormalizedBTProductMaximizer c
      (selectedBTOfFordZermelo hFord c hc hconn) := by
  rw [selectedBTOfFordZermelo_eq_selectedFordBTOfFordZermelo hFord hc hconn]
  exact selectedFordBTOfFordZermelo_productMaximizer hFord hc hconn

/-- The RTBT lotteries obtained from the two exposed Ford/Zermelo selectors
are equal, because the underlying normalized Bradley--Terry vectors coincide. -/
theorem RTBTFrom_selectedBTOfFordZermelo_eq_selectedFordBTOfFordZermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} {ρ : α → ℝ}
    {c : α → α → ℝ}
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    RTBTFromStrength β ρ
        (selectedBTOfFordZermelo hFord c hc hconn) =
      RTBTFromStrength β ρ
        (selectedFordBTOfFordZermelo hFord c hc hconn) := by
  rw [selectedBTOfFordZermelo_eq_selectedFordBTOfFordZermelo hFord hc hconn]

/-- Proposition `DPOasRTBT` using the canonical Ford/Zermelo-selected
Bradley--Terry vector. -/
theorem DPOasRTBT_selectedBTOfFordZermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {c : α → α → ℝ} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    dpoArgmaxSet β c ρ =
      ({RTBTFromStrength β ρ
          (selectedBTOfFordZermelo hFord c hc hconn)} : Set (α → ℝ)) :=
  DPOasRTBT_from_BTProp_certificate hβ hρ
    (selectedBTOfFordZermelo_certificate hFord hc hconn)

/-- Proposition `DPOasRTBT` using the canonical selector taken directly from
Ford/Zermelo's normalized maximum-likelihood certificate. -/
theorem DPOasRTBT_selectedFordBTOfFordZermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {c : α → α → ℝ} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    dpoArgmaxSet β c ρ =
      ({RTBTFromStrength β ρ
          (selectedFordBTOfFordZermelo hFord c hc hconn)} : Set (α → ℝ)) :=
  DPOasRTBT_from_ford_BTProp_certificate hβ hρ
    (selectedFordBTOfFordZermelo_certificate hFord hc hconn)

/-- Combining Ford/Zermelo with the DPO/BT change of variables gives the
paper's singleton RTBT argmax statement.  The finite count-matrix and
connectivity hypotheses are the only local side conditions. -/
theorem DPOasRTBT_from_ford_zermelo
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {c : α → α → ℝ} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal c) c u ∧
        dpoArgmaxSet β c ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) := by
  rcases exists_BTProp_certificate_of_ford_zermelo hFord hc hconn with
    ⟨u, hBT⟩
  exact ⟨u, hBT, DPOasRTBT_from_BTProp_certificate hβ hρ hBT⟩

/-- Partition-assumption version of the paper's singleton RTBT argmax
statement. -/
theorem DPOasRTBT_from_ford_zermelo_partitionAssumption
    [Nonempty α]
    (hFord : FordZermeloBTTheorem α)
    {β : ℝ} (hβ : 0 < β)
    {c : α → α → ℝ} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal c) c u ∧
        dpoArgmaxSet β c ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_ford_zermelo hFord hβ hρ hc
    (FordStronglyConnected_of_partitionAssumption hpart)

/-- Proposition `DPOasRTBT` with Ford/Zermelo discharged by the proved finite
theorem. -/
theorem DPOasRTBT_from_finite_ford_zermelo
    [Nonempty α]
    {β : ℝ} (hβ : 0 < β)
    {c : α → α → ℝ} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hc : IsFordCountMatrix c)
    (hconn : FordStronglyConnected c) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal c) c u ∧
        dpoArgmaxSet β c ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_ford_zermelo
    FordZermeloBTTheorem_finite hβ hρ hc hconn

/-- Partition-assumption version of `DPOasRTBT` with Ford/Zermelo discharged
by the proved finite theorem. -/
theorem DPOasRTBT_from_finite_ford_zermelo_partitionAssumption
    [Nonempty α]
    {β : ℝ} (hβ : 0 < β)
    {c : α → α → ℝ} {ρ : α → ℝ}
    (hρ : ∀ x : α, 0 < ρ x)
    (hc : IsFordCountMatrix c)
    (hpart : FordPartitionAssumption c) :
    ∃ u : α → ℝ,
      HasBTPropCertificate (fordPairTotal c) c u ∧
        dpoArgmaxSet β c ρ =
          ({RTBTFromStrength β ρ u} : Set (α → ℝ)) :=
  DPOasRTBT_from_ford_zermelo_partitionAssumption
    FordZermeloBTTheorem_finite hβ hρ hc hpart

end PaperFormalization
