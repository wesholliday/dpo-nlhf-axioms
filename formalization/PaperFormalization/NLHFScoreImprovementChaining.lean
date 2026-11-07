import PaperFormalization.WeakProfileMargin
import PaperFormalization.NLHFMonotonicityFinite

open scoped BigOperators

namespace PaperFormalization

/-! # Chaining the paper's improvement conditions into uniform block moves

The `1/8` clauses of Theorem `NLHFmono` are proved in `paper/main.tex` by
moving `x` up one position at a time in each voter's weak order: each single
move raises `x` against exactly one tied block `B` of candidates and leaves
every other comparison alone, so it is a *uniform block improvement* of the
normalized margin matrix, which is what the analytic `1/8` theorem handles.

This module formalizes that decomposition for score-represented weak orders:
from the paper's conditions (i)–(iii) it builds an explicit finite chain of
single-voter, single-block moves. -/

/-- The Boolean weak-order profile induced by a score profile:
`(a,b) ∈ R_v` iff `v` ranks `a` at least as high as `b`. -/
noncomputable def scoreWeakProfile {V α : Type*} (score : V → α → ℝ) : V → α → α → Bool :=
  fun v a b => decide (score v b ≤ score v a)

/-- Level of `a` against `b`: `2` for strictly above, `1` for tied, `0` for
strictly below.  This is `scoreMarginSignReal + 1`. -/
noncomputable def scoreLevel (a b : ℝ) : ℕ :=
  if b < a then 2 else if a = b then 1 else 0

lemma scoreLevel_eq_two {a b : ℝ} (h : b < a) : scoreLevel a b = 2 := by
  simp [scoreLevel, h]

lemma scoreLevel_eq_one {a b : ℝ} (h : a = b) : scoreLevel a b = 1 := by
  subst h; simp [scoreLevel]

lemma scoreLevel_eq_zero {a b : ℝ} (h : a < b) : scoreLevel a b = 0 := by
  have h1 : ¬ b < a := by linarith
  have h2 : a ≠ b := by linarith
  simp [scoreLevel, h1, h2]

lemma scoreMarginSignReal_eq_scoreLevel (a b : ℝ) :
    scoreMarginSignReal a b = (scoreLevel a b : ℝ) - 1 := by
  rcases lt_trichotomy a b with h | h | h
  · rw [scoreMarginSignReal_of_lt h, scoreLevel_eq_zero h]; norm_num
  · rw [scoreMarginSignReal_of_eq h, scoreLevel_eq_one h]; norm_num
  · rw [scoreMarginSignReal_of_gt h, scoreLevel_eq_two h]; norm_num

lemma scoreLevel_mono {a a' b : ℝ} (h : a ≤ a') :
    scoreLevel a b ≤ scoreLevel a' b := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rw [scoreLevel_eq_zero h1]; exact Nat.zero_le _
  · rw [scoreLevel_eq_one h1]
    rcases eq_or_lt_of_le h with rfl | h2
    · rw [scoreLevel_eq_one h1]
    · rw [scoreLevel_eq_two (by linarith)]; norm_num
  · rw [scoreLevel_eq_two h1, scoreLevel_eq_two (by linarith)]

lemma lt_of_scoreLevel_lt {a a' b : ℝ} (h : scoreLevel a b < scoreLevel a' b) :
    a < a' := by
  by_contra hcon
  have hle : a' ≤ a := le_of_not_gt hcon
  have hmono : scoreLevel a' b ≤ scoreLevel a b := scoreLevel_mono hle
  omega

lemma scoreLevel_le_of_le_of_le {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
    scoreLevel a c ≤ scoreLevel b c ∧ scoreLevel b c ≤ scoreLevel c c := by
  exact ⟨scoreLevel_mono h1, scoreLevel_mono h2⟩

/-! ## Reading the paper's conditions (i)–(iii) off a score improvement -/

section Bridge

variable {V α : Type*} {score score' : V → α → ℝ} {x : α}

lemma scoreLevel_le_of_scoreWeakProfileImprovement
    (h : IsWeakProfileImprovement (scoreWeakProfile score)
      (scoreWeakProfile score') x)
    (v : V) {y : α} (hy : y ≠ x) :
    scoreLevel (score v x) (score v y) ≤
      scoreLevel (score' v x) (score' v y) := by
  have h1 := h.1 v y hy
  have h2 := h.2.1 v y hy
  simp only [scoreWeakProfile, decide_eq_true_eq, decide_eq_false_iff_not,
    not_le] at h1 h2
  rcases lt_trichotomy (score v x) (score v y) with hlt | heq | hgt
  · rw [scoreLevel_eq_zero hlt]; exact Nat.zero_le _
  · rw [scoreLevel_eq_one heq]
    have hle : score' v y ≤ score' v x := h1 (le_of_eq heq.symm)
    rcases eq_or_lt_of_le hle with heq' | hlt'
    · rw [scoreLevel_eq_one heq'.symm]
    · rw [scoreLevel_eq_two hlt']; norm_num
  · rw [scoreLevel_eq_two hgt, scoreLevel_eq_two (h2 hgt)]

lemma scoreLevel_off_eq_of_scoreWeakProfileImprovement
    (h : IsWeakProfileImprovement (scoreWeakProfile score)
      (scoreWeakProfile score') x)
    (v : V) {y z : α} (hy : y ≠ x) (hz : z ≠ x) :
    scoreLevel (score' v y) (score' v z) = scoreLevel (score v y) (score v z) := by
  have h1 := h.2.2 v y z hy hz
  have h2 := h.2.2 v z y hz hy
  simp only [scoreWeakProfile, decide_eq_decide] at h1 h2
  rcases lt_trichotomy (score v y) (score v z) with hlt | heq | hgt
  · have hnot : ¬ (score' v z ≤ score' v y) := by
      intro hc
      exact absurd (h1.mp hc) (by linarith)
    rw [scoreLevel_eq_zero (lt_of_not_ge hnot), scoreLevel_eq_zero hlt]
  · have hle1 : score' v z ≤ score' v y := h1.mpr (le_of_eq heq.symm)
    have hle2 : score' v y ≤ score' v z := h2.mpr (le_of_eq heq)
    rw [scoreLevel_eq_one (le_antisymm hle2 hle1), scoreLevel_eq_one heq]
  · have hnot : ¬ (score' v y ≤ score' v z) := by
      intro hc
      exact absurd (h2.mp hc) (by linarith)
    rw [scoreLevel_eq_two (lt_of_not_ge hnot), scoreLevel_eq_two hgt]

end Bridge

/-! ## Choosing a value in a gap -/

lemma exists_between_finsets (S T : Finset ℝ)
    (h : ∀ a ∈ S, ∀ b ∈ T, a < b) :
    ∃ c : ℝ, (∀ a ∈ S, a < c) ∧ (∀ b ∈ T, c < b) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rcases T.eq_empty_or_nonempty with rfl | hT
    · exact ⟨0, by simp, by simp⟩
    · refine ⟨T.min' hT - 1, by simp, ?_⟩
      intro b hb
      have := T.min'_le b hb
      linarith
  · rcases T.eq_empty_or_nonempty with rfl | hT
    · refine ⟨S.max' hS + 1, ?_, by simp⟩
      intro a ha
      have := S.le_max' a ha
      linarith
    · have hmid := h (S.max' hS) (S.max'_mem hS) (T.min' hT) (T.min'_mem hT)
      refine ⟨(S.max' hS + T.min' hT) / 2, ?_, ?_⟩
      · intro a ha
        have := S.le_max' a ha
        linarith
      · intro b hb
        have := T.min'_le b hb
        linarith

/-! ## One single-voter, single-block move -/

lemma scoreProfileMargin_congr_signs
    {V α : Type*} [Fintype V] (s₁ s₂ : V → α → ℝ)
    (h : ∀ (v : V) (a b : α),
      scoreMarginSignReal (s₁ v a) (s₁ v b) =
        scoreMarginSignReal (s₂ v a) (s₂ v b)) :
    scoreProfileMargin s₁ = scoreProfileMargin s₂ := by
  funext a b
  unfold scoreProfileMargin scoreMarginSign
  exact congrArg (fun r : ℝ => r / (Fintype.card V : ℝ))
    (Finset.sum_congr rfl fun v _ => h v a b)

/-- Raising one voter's score for `x` so that exactly the candidates of the
block `B` gain one level is a uniform block improvement of the margin matrix
with `δ = 1 / |V|`. -/
lemma scoreProfileMargin_update_x_step
    {V α : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype α] [DecidableEq α]
    (score : V → α → ℝ) (v : V) (x : α) (c₁ : ℝ) (B : Finset α)
    (hxB : x ∉ B)
    (hstep : ∀ y : α, y ≠ x →
      scoreMarginSignReal c₁ (score v y) -
          scoreMarginSignReal (score v x) (score v y) =
        if y ∈ B then 1 else 0)
    (a b : α) :
    scoreProfileMargin
        (Function.update score v (Function.update (score v) x c₁)) a b -
        scoreProfileMargin score a b =
      blockImprovementChange x B (1 / (Fintype.card V : ℝ)) a b := by
  classical
  have hcardpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  set g : α → ℝ := Function.update (score v) x c₁ with hg
  have hgx : g x = c₁ := by simp [hg]
  have hgy : ∀ y : α, y ≠ x → g y = score v y := by
    intro y hy
    simp [hg, hy]
  have hupd : ∀ u : V, u ≠ v →
      Function.update score v g u = score u := by
    intro u hu
    simp [hu]
  have hupdv : Function.update score v g v = g := by simp
  have hnum :
      Finset.univ.sum (fun u : V =>
          scoreMarginSign (Function.update score v g u) a b) -
        Finset.univ.sum (fun u : V => scoreMarginSign (score u) a b) =
      scoreMarginSignReal (g a) (g b) -
        scoreMarginSignReal (score v a) (score v b) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_single_of_mem v (Finset.mem_univ v) ?_ |>.trans ?_
    · intro u _hu hune
      rw [hupd u hune]
      simp
    · rw [hupdv]
      rfl
  have hstepval :
      scoreMarginSignReal (g a) (g b) -
          scoreMarginSignReal (score v a) (score v b) =
        (if a = x ∧ b ∈ B then (1 : ℝ) else 0) -
          (if a ∈ B ∧ b = x then (1 : ℝ) else 0) := by
    by_cases hax : a = x
    · by_cases hbx : b = x
      · rw [hax, hbx, hgx]
        have hz1 : scoreMarginSignReal c₁ c₁ = 0 := scoreMarginSignReal_of_eq rfl
        have hz2 : scoreMarginSignReal (score v x) (score v x) = 0 :=
          scoreMarginSignReal_of_eq rfl
        rw [hz1, hz2, if_neg (fun hc : x = x ∧ x ∈ B => hxB hc.2),
          if_neg (fun hc : x ∈ B ∧ x = x => hxB hc.1)]
      · rw [hax, hgx, hgy b hbx, hstep b hbx,
          if_neg (fun hc : x ∈ B ∧ b = x => hxB hc.1)]
        by_cases hbB : b ∈ B
        · rw [if_pos hbB, if_pos (⟨rfl, hbB⟩ : x = x ∧ b ∈ B)]
          ring
        · rw [if_neg hbB, if_neg (fun hc : x = x ∧ b ∈ B => hbB hc.2)]
          ring
    · by_cases hbx : b = x
      · rw [hbx, hgx, hgy a hax]
        have hkey := hstep a hax
        have e1 : scoreMarginSignReal (score v a) c₁ =
            -scoreMarginSignReal c₁ (score v a) :=
          scoreMarginSignReal_antisymm _ _
        have e2 : scoreMarginSignReal (score v a) (score v x) =
            -scoreMarginSignReal (score v x) (score v a) :=
          scoreMarginSignReal_antisymm _ _
        rw [e1, e2, if_neg (fun hc : a = x ∧ x ∈ B => hax hc.1)]
        by_cases haB : a ∈ B
        · rw [if_pos haB] at hkey
          rw [if_pos (⟨haB, rfl⟩ : a ∈ B ∧ x = x)]
          linarith
        · rw [if_neg haB] at hkey
          rw [if_neg (fun hc : a ∈ B ∧ x = x => haB hc.1)]
          linarith
      · rw [hgy a hax, hgy b hbx,
          if_neg (fun hc : a = x ∧ b ∈ B => hax hc.1),
          if_neg (fun hc : a ∈ B ∧ b = x => hbx hc.2)]
        ring
  unfold scoreProfileMargin
  rw [div_sub_div_same, hnum, hstepval]
  unfold blockImprovementChange
  rw [sub_div]
  by_cases h1 : a = x ∧ b ∈ B
  · have h2 : ¬ (a ∈ B ∧ b = x) := by
      rintro ⟨haB, _hbx⟩
      exact hxB (h1.1 ▸ haB)
    simp only [if_pos h1, if_neg h2]
    ring
  · by_cases h2 : a ∈ B ∧ b = x
    · simp only [if_neg h1, if_pos h2]
      ring
    · simp only [if_neg h1, if_neg h2]
      ring

/-! ## The paper's "move `x` up one position at a time" step -/

lemma scoreLevel_le_two (a b : ℝ) : scoreLevel a b ≤ 2 := by
  unfold scoreLevel
  split_ifs <;> omega

lemma le_of_one_le_scoreLevel {a b : ℝ} (h : 1 ≤ scoreLevel a b) : b ≤ a := by
  by_contra hc
  rw [scoreLevel_eq_zero (lt_of_not_ge hc)] at h
  omega

/-- One step of the paper's chain: from the current position of `x` there is a
next position `c₁` at which exactly one tied block `B` of candidates gains one
level, every other comparison is unchanged, and `x` has not overshot its
target. -/
lemma exists_scoreLevel_block_step
    {α : Type*} [Fintype α] [DecidableEq α] {x : α} (s : α → ℝ) (c c' : ℝ)
    (hlev : ∀ y : α, y ≠ x → scoreLevel c (s y) ≤ scoreLevel c' (s y))
    {y₀ : α} (hy₀ : y₀ ≠ x)
    (hy₀lt : scoreLevel c (s y₀) < scoreLevel c' (s y₀)) :
    ∃ (c₁ : ℝ) (B : Finset α),
      (∀ y ∈ B, y ≠ x) ∧ B.Nonempty ∧
      (∀ y ∈ B, scoreLevel c₁ (s y) = scoreLevel c (s y) + 1) ∧
      (∀ y : α, y ≠ x → y ∉ B → scoreLevel c₁ (s y) = scoreLevel c (s y)) ∧
      (∀ y : α, y ≠ x → scoreLevel c₁ (s y) ≤ scoreLevel c' (s y)) := by
  classical
  have hcc' : c < c' := lt_of_scoreLevel_lt hy₀lt
  by_cases hA : ∃ y : α, y ≠ x ∧ s y = c
  · obtain ⟨yt, hytx, hyt⟩ := hA
    have hcross : ∀ a ∈ ({c} : Finset ℝ), ∀ b ∈ insert c'
        (((Finset.univ.erase x).filter (fun y => c < s y)).image s), a < b := by
      intro a ha b hb
      rw [Finset.mem_singleton] at ha
      subst ha
      rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact hcc'
      · obtain ⟨y, hy, hyb⟩ := Finset.mem_image.mp hb'
        rw [← hyb]
        exact (Finset.mem_filter.mp hy).2
    obtain ⟨c₁, hlo, hhi⟩ := exists_between_finsets _ _ hcross
    have hc1lo : c < c₁ := hlo c (Finset.mem_singleton_self c)
    have hc1c' : c₁ < c' := hhi c' (Finset.mem_insert_self _ _)
    have hc1hi : ∀ y : α, y ≠ x → c < s y → c₁ < s y := by
      intro y hy hlt
      refine hhi (s y) (Finset.mem_insert_of_mem ?_)
      exact Finset.mem_image_of_mem s (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩, hlt⟩)
    refine ⟨c₁, (Finset.univ.erase x).filter (fun y => s y = c), ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
    · exact ⟨yt, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hytx, Finset.mem_univ _⟩, hyt⟩⟩
    · intro y hy
      have hsy : s y = c := (Finset.mem_filter.mp hy).2
      have h1 : scoreLevel c (s y) = 1 := scoreLevel_eq_one hsy.symm
      have h2 : scoreLevel c₁ (s y) = 2 := by
        refine scoreLevel_eq_two ?_
        rw [hsy]
        exact hc1lo
      omega
    · intro y hyx hyB
      have hne : s y ≠ c := by
        intro hc
        exact hyB (Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ _⟩, hc⟩)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [scoreLevel_eq_two hlt, scoreLevel_eq_two (by linarith)]
      · rw [scoreLevel_eq_zero hgt, scoreLevel_eq_zero (hc1hi y hyx hgt)]
    · intro y _hyx
      exact scoreLevel_mono (le_of_lt hc1c')
  · push_neg at hA
    have hDne : ((Finset.univ.erase x).filter
        (fun y => scoreLevel c (s y) < scoreLevel c' (s y))).Nonempty :=
      ⟨y₀, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hy₀, Finset.mem_univ _⟩, hy₀lt⟩⟩
    have hDlt : ∀ y ∈ (Finset.univ.erase x).filter
        (fun y => scoreLevel c (s y) < scoreLevel c' (s y)), c < s y := by
      intro y hy
      have hyx : y ≠ x := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
      have hylt : scoreLevel c (s y) < scoreLevel c' (s y) :=
        (Finset.mem_filter.mp hy).2
      have hne : s y ≠ c := hA y hyx
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exfalso
        have h2 : scoreLevel c (s y) = 2 := scoreLevel_eq_two hlt
        have h3 := scoreLevel_le_two c' (s y)
        omega
      · exact hgt
    obtain ⟨y₁, hy₁D, hy₁eq⟩ :=
      Finset.exists_mem_eq_inf' hDne s
    have hy₁x : y₁ ≠ x := (Finset.mem_erase.mp (Finset.mem_filter.mp hy₁D).1).1
    have hy₁lt : scoreLevel c (s y₁) < scoreLevel c' (s y₁) :=
      (Finset.mem_filter.mp hy₁D).2
    have hclt : c < s y₁ := hDlt y₁ hy₁D
    have hc'le : s y₁ ≤ c' := by
      refine le_of_one_le_scoreLevel ?_
      omega
    have hmin : ∀ y ∈ (Finset.univ.erase x).filter
        (fun y => scoreLevel c (s y) < scoreLevel c' (s y)), s y₁ ≤ s y := by
      intro y hy
      rw [← hy₁eq]
      exact Finset.inf'_le s hy
    have hnogap : ∀ y : α, y ≠ x → c < s y → s y₁ ≤ s y := by
      intro y hyx hlt
      by_cases hyD : y ∈ (Finset.univ.erase x).filter
          (fun y => scoreLevel c (s y) < scoreLevel c' (s y))
      · exact hmin y hyD
      · have hyeq : scoreLevel c (s y) = scoreLevel c' (s y) := by
          have hle := hlev y hyx
          have hnlt : ¬ scoreLevel c (s y) < scoreLevel c' (s y) := by
            intro hc
            exact hyD (Finset.mem_filter.mpr
              ⟨Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ _⟩, hc⟩)
          omega
        have h0 : scoreLevel c (s y) = 0 := scoreLevel_eq_zero hlt
        have h0' : scoreLevel c' (s y) = 0 := by omega
        have : c' < s y := by
          by_contra hcon
          have h1 : 1 ≤ scoreLevel c' (s y) := by
            rcases eq_or_lt_of_le (le_of_not_gt hcon) with heq | hgt
            · rw [scoreLevel_eq_one heq.symm]
            · rw [scoreLevel_eq_two hgt]; omega
          omega
        linarith
    refine ⟨s y₁, (Finset.univ.erase x).filter (fun y => s y = s y₁),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
    · exact ⟨y₁, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hy₁x, Finset.mem_univ _⟩, rfl⟩⟩
    · intro y hy
      have hsy : s y = s y₁ := (Finset.mem_filter.mp hy).2
      have h1 : scoreLevel c (s y) = 0 := by
        refine scoreLevel_eq_zero ?_
        rw [hsy]
        exact hclt
      have h2 : scoreLevel (s y₁) (s y) = 1 := scoreLevel_eq_one hsy.symm
      omega
    · intro y hyx hyB
      have hne : s y ≠ s y₁ := by
        intro hc
        exact hyB (Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ _⟩, hc⟩)
      have hnec : s y ≠ c := hA y hyx
      rcases lt_or_gt_of_ne hnec with hlt | hgt
      · rw [scoreLevel_eq_two hlt, scoreLevel_eq_two (by linarith)]
      · have hle := hnogap y hyx hgt
        have hlt' : s y₁ < s y := lt_of_le_of_ne hle (Ne.symm hne)
        rw [scoreLevel_eq_zero hgt, scoreLevel_eq_zero hlt']
    · intro y _hyx
      exact scoreLevel_mono hc'le

/-! ## Sign-equivalent updates leave the margin matrix alone -/

lemma scoreProfileMargin_update_eq_of_levels_eq
    {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α]
    (score : V → α → ℝ) (v : V) (x : α) (c' : ℝ)
    (heq : ∀ y : α, y ≠ x →
      scoreLevel (score v x) (score v y) = scoreLevel c' (score v y)) :
    scoreProfileMargin
        (Function.update score v (Function.update (score v) x c')) =
      scoreProfileMargin score := by
  classical
  refine scoreProfileMargin_congr_signs _ _ ?_
  intro u a b
  by_cases hu : u = v
  · subst hu
    have hupd : Function.update score u (Function.update (score u) x c') u =
        Function.update (score u) x c' := by
      simp
    rw [hupd]
    have hgx : Function.update (score u) x c' x = c' := by simp
    have hgy : ∀ y : α, y ≠ x → Function.update (score u) x c' y = score u y := by
      intro y hy
      simp only [Function.update_apply, if_neg hy]
    have hkey : ∀ y : α, y ≠ x →
        scoreMarginSignReal c' (score u y) =
          scoreMarginSignReal (score u x) (score u y) := by
      intro y hy
      rw [scoreMarginSignReal_eq_scoreLevel, scoreMarginSignReal_eq_scoreLevel,
        heq y hy]
    by_cases hax : a = x
    · by_cases hbx : b = x
      · rw [hax, hbx, hgx, scoreMarginSignReal_of_eq (rfl : c' = c'),
          scoreMarginSignReal_of_eq (rfl : score u x = score u x)]
      · rw [hax, hgx, hgy b hbx]
        exact hkey b hbx
    · by_cases hbx : b = x
      · rw [hbx, hgx, hgy a hax]
        rw [scoreMarginSignReal_antisymm (score u a) c',
          scoreMarginSignReal_antisymm (score u a) (score u x)]
        rw [hkey a hax]
      · rw [hgy a hax, hgy b hbx]
  · have hupd : Function.update score v (Function.update (score v) x c') u =
        score u := by
      simp only [Function.update_apply, if_neg hu]
    rw [hupd]

/-! ## Raising `x` for a single voter, by the paper's chain of block moves -/

section SingleVoter

variable {V α : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype α] [DecidableEq α]
  {F : ℝ → MatrixRule α} {τ : ℝ} {ρ : α → ℝ} {x : α}

/-- The measure driving the chain: the total number of level increases still
required of the improved voter. -/
noncomputable def raiseMeasure (s : α → ℝ) (c c' : ℝ) (x : α) : ℕ :=
  (Finset.univ.erase x).sum (fun y => scoreLevel c' (s y) - scoreLevel c (s y))

theorem nlhf_single_voter_raise_selected
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hρ : IsFullSupportLottery ρ)
    (v : V) :
    ∀ (n : ℕ) (score : V → α → ℝ) (c' : ℝ),
      (∀ y : α, y ≠ x → scoreLevel (score v x) (score v y) ≤
        scoreLevel c' (score v y)) →
      raiseMeasure (score v) (score v x) c' x ≤ n →
      F τ (scoreProfileMargin score) ρ x ≤
        F τ (scoreProfileMargin
          (Function.update score v (Function.update (score v) x c'))) ρ x := by
  classical
  have hcardpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  intro n
  induction n with
  | zero =>
    intro score c' hlev hsum
    have hall : ∀ y : α, y ≠ x →
        scoreLevel (score v x) (score v y) = scoreLevel c' (score v y) := by
      intro y hy
      have hmem : y ∈ Finset.univ.erase x :=
        Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩
      have hle : scoreLevel c' (score v y) - scoreLevel (score v x) (score v y)
          ≤ raiseMeasure (score v) (score v x) c' x := by
        unfold raiseMeasure
        exact Finset.single_le_sum
          (f := fun y =>
            scoreLevel c' (score v y) - scoreLevel (score v x) (score v y))
          (fun i _ => Nat.zero_le _) hmem
      have hlevy := hlev y hy
      omega
    rw [scoreProfileMargin_update_eq_of_levels_eq score v x c' hall]
  | succ n ih =>
    intro score c' hlev hsum
    by_cases hallcase : ∀ y : α, y ≠ x →
        scoreLevel (score v x) (score v y) = scoreLevel c' (score v y)
    · rw [scoreProfileMargin_update_eq_of_levels_eq score v x c' hallcase]
    · push_neg at hallcase
      obtain ⟨y₀, hy₀x, hy₀ne⟩ := hallcase
      have hy₀lt : scoreLevel (score v x) (score v y₀) <
          scoreLevel c' (score v y₀) :=
        lt_of_le_of_ne (hlev y₀ hy₀x) hy₀ne
      obtain ⟨c₁, B, hBx, hBne, hBin, hBout, hBlev⟩ :=
        exists_scoreLevel_block_step (x := x) (score v) (score v x) c'
          hlev hy₀x hy₀lt
      have hxB : x ∉ B := fun hc => (hBx x hc) rfl
      have hstep : ∀ y : α, y ≠ x →
          scoreMarginSignReal c₁ (score v y) -
            scoreMarginSignReal (score v x) (score v y) =
              if y ∈ B then 1 else 0 := by
        intro y hy
        rw [scoreMarginSignReal_eq_scoreLevel, scoreMarginSignReal_eq_scoreLevel]
        by_cases hyB : y ∈ B
        · rw [if_pos hyB, hBin y hyB]
          push_cast
          ring
        · rw [if_neg hyB, hBout y hy hyB]
          ring
      set score₁ : V → α → ℝ :=
        Function.update score v (Function.update (score v) x c₁) with hs1
      have hs1v : score₁ v = Function.update (score v) x c₁ := by
        rw [hs1]; simp
      have hs1vx : score₁ v x = c₁ := by rw [hs1v]; simp
      have hs1vy : ∀ y : α, y ≠ x → score₁ v y = score v y := by
        intro y hy
        rw [hs1v]
        simp only [Function.update_apply, if_neg hy]
      let Bsub : Finset {z : α // z ≠ x} :=
        Finset.univ.filter (fun z : {z : α // z ≠ x} => z.1 ∈ B)
      have hBmap :
          Bsub.map (Function.Embedding.subtype (fun z : α => z ≠ x)) = B := by
        ext y
        simp only [Finset.mem_map, Function.Embedding.coe_subtype,
          Finset.mem_filter, Finset.mem_univ, true_and, Bsub]
        constructor
        · rintro ⟨z, hz, hzy⟩
          rw [← hzy]
          exact hz
        · intro hy
          exact ⟨⟨y, hBx y hy⟩, hy, rfl⟩
      have hBsubne : Bsub.Nonempty := by
        obtain ⟨y, hy⟩ := hBne
        refine ⟨⟨y, hBx y hy⟩, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bsub]
        exact hy
      have hchange : ∀ a b : α,
          scoreProfileMargin score₁ a b - scoreProfileMargin score a b =
            blockImprovementChange x
              (Bsub.map (Function.Embedding.subtype (fun z : α => z ≠ x)))
              (1 / (Fintype.card V : ℝ)) a b := by
        intro a b
        rw [hBmap, hs1]
        exact scoreProfileMargin_update_x_step score v x c₁ B hxB hstep a b
      have hstep1 :
          F τ (scoreProfileMargin score) ρ x ≤
            F τ (scoreProfileMargin score₁) ρ x :=
        nlhf_block_improvement_monotone_of_tau_ge_one_eighth_unit_bound_selected
          hselect hselected hτge
          (scoreProfileMargin_normalized score)
          (scoreProfileMargin_normalized score₁)
          hρ hchange hBsubne
          (fun i j => scoreProfileMargin_coordinate_abs_le_one score₁ x i.1 j.1)
          (div_pos one_pos hcardpos)
      have hlev₁ : ∀ y : α, y ≠ x →
          scoreLevel (score₁ v x) (score₁ v y) ≤ scoreLevel c' (score₁ v y) := by
        intro y hy
        rw [hs1vx, hs1vy y hy]
        exact hBlev y hy
      have hdrop :
          (Finset.univ.erase x).sum (fun y =>
              scoreLevel c' (score v y) - scoreLevel c₁ (score v y)) <
            (Finset.univ.erase x).sum (fun y =>
              scoreLevel c' (score v y) - scoreLevel (score v x) (score v y)) := by
        obtain ⟨y₁, hy₁⟩ := hBne
        refine Finset.sum_lt_sum (fun y hy => ?_) ⟨y₁, ?_, ?_⟩
        · have hyx := (Finset.mem_erase.mp hy).1
          by_cases hyB : y ∈ B
          · have h1 := hBin y hyB
            omega
          · have h1 := hBout y hyx hyB
            omega
        · exact Finset.mem_erase.mpr ⟨hBx y₁ hy₁, Finset.mem_univ _⟩
        · have h1 := hBin y₁ hy₁
          have h2 := hBlev y₁ (hBx y₁ hy₁)
          omega
      have hsum₁ : raiseMeasure (score₁ v) (score₁ v x) c' x ≤ n := by
        have hcongr :
            (Finset.univ.erase x).sum (fun y =>
                scoreLevel c' (score₁ v y) - scoreLevel (score₁ v x) (score₁ v y)) =
              (Finset.univ.erase x).sum (fun y =>
                scoreLevel c' (score v y) - scoreLevel c₁ (score v y)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [hs1vx, hs1vy y (Finset.mem_erase.mp hy).1]
        unfold raiseMeasure at hsum ⊢
        rw [hcongr]
        omega
      have hupd :
          Function.update score₁ v (Function.update (score₁ v) x c') =
            Function.update score v (Function.update (score v) x c') := by
        simp [hs1, Function.update_idem]
      have hfinal := ih score₁ c' hlev₁ hsum₁
      rw [hupd] at hfinal
      exact le_trans hstep1 hfinal

end SingleVoter

/-! ## Re-representing the improved position in the old value system -/

lemma lt_of_scoreLevel_eq_zero {a b : ℝ} (h : scoreLevel a b = 0) : a < b := by
  by_contra hc
  have h1 : 1 ≤ scoreLevel a b := by
    rcases eq_or_lt_of_le (le_of_not_gt hc) with heq | hgt
    · rw [scoreLevel_eq_one heq.symm]
    · rw [scoreLevel_eq_two hgt]; omega
  omega

/-- If two score functions induce the same weak order off `x`, then the
position of `x` in the second one is realized by some value in the first
one's value system. -/
lemma exists_position_representation
    {α : Type*} [Fintype α] [DecidableEq α] {x : α} (p p' : α → ℝ)
    (hoff : ∀ y z : α, y ≠ x → z ≠ x →
      scoreLevel (p' y) (p' z) = scoreLevel (p y) (p z)) :
    ∃ c₁ : ℝ, ∀ y : α, y ≠ x →
      scoreLevel c₁ (p y) = scoreLevel (p' x) (p' y) := by
  classical
  by_cases htie : ∃ y₀ : α, y₀ ≠ x ∧ p' x = p' y₀
  · obtain ⟨y₀, hy₀x, hy₀⟩ := htie
    refine ⟨p y₀, fun y hy => ?_⟩
    rw [hy₀]
    exact (hoff y₀ y hy₀x hy).symm
  · push_neg at htie
    have hcross : ∀ a ∈ ((Finset.univ.erase x).filter
        (fun y => p' y < p' x)).image p,
        ∀ b ∈ ((Finset.univ.erase x).filter (fun y => p' x < p' y)).image p,
        a < b := by
      intro a ha b hb
      obtain ⟨y, hy, hya⟩ := Finset.mem_image.mp ha
      obtain ⟨z, hz, hzb⟩ := Finset.mem_image.mp hb
      have hyx : y ≠ x := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1
      have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_filter.mp hz).1).1
      have hy2 : p' y < p' x := (Finset.mem_filter.mp hy).2
      have hz2 : p' x < p' z := (Finset.mem_filter.mp hz).2
      have h0 : scoreLevel (p' y) (p' z) = 0 :=
        scoreLevel_eq_zero (lt_trans hy2 hz2)
      rw [hoff y z hyx hzx] at h0
      rw [← hya, ← hzb]
      exact lt_of_scoreLevel_eq_zero h0
    obtain ⟨c₁, hlo, hhi⟩ := exists_between_finsets _ _ hcross
    refine ⟨c₁, fun y hy => ?_⟩
    rcases lt_trichotomy (p' x) (p' y) with hlt | heq | hgt
    · rw [scoreLevel_eq_zero hlt]
      refine scoreLevel_eq_zero (hhi (p y) ?_)
      exact Finset.mem_image_of_mem p (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hy, Finset.mem_univ _⟩, hlt⟩)
    · exact absurd heq (htie y hy)
    · rw [scoreLevel_eq_two hgt]
      refine scoreLevel_eq_two (hlo (p y) ?_)
      exact Finset.mem_image_of_mem p (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hy, Finset.mem_univ _⟩, hgt⟩)

/-! ## Hybridizing over voters -/

/-- The profile in which the voters of `S` have already switched to `score'`. -/
noncomputable def hybridScore {V α : Type*} [DecidableEq V]
    (score score' : V → α → ℝ) (S : Finset V) : V → α → ℝ :=
  fun u => if u ∈ S then score' u else score u

section Hybrid

variable {V α : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
  [Fintype α] [DecidableEq α]
  {F : ℝ → MatrixRule α} {τ : ℝ} {ρ : α → ℝ} {x : α}
  {score score' : V → α → ℝ}

lemma nlhf_hybrid_insert_step
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hρ : IsFullSupportLottery ρ)
    (himp : IsWeakProfileImprovement (scoreWeakProfile score)
      (scoreWeakProfile score') x)
    (v : V) (S : Finset V) (hv : v ∉ S) :
    F τ (scoreProfileMargin (hybridScore score score' S)) ρ x ≤
      F τ (scoreProfileMargin (hybridScore score score' (insert v S))) ρ x := by
  classical
  have hoff : ∀ y z : α, y ≠ x → z ≠ x →
      scoreLevel (score' v y) (score' v z) = scoreLevel (score v y) (score v z) :=
    fun y z hy hz => scoreLevel_off_eq_of_scoreWeakProfileImprovement himp v hy hz
  obtain ⟨c₁, hc₁⟩ := exists_position_representation (x := x) (score v) (score' v) hoff
  have hhybv : hybridScore score score' S v = score v := by
    simp [hybridScore, hv]
  have hhybu : ∀ u : V, u ≠ v →
      hybridScore score score' (insert v S) u = hybridScore score score' S u := by
    intro u hu
    simp [hybridScore, Finset.mem_insert, hu]
  have hhybvins : hybridScore score score' (insert v S) v = score' v := by
    simp [hybridScore]
  -- Step 1: raise `x` for voter `v` inside the old value system.
  have hlev : ∀ y : α, y ≠ x →
      scoreLevel (hybridScore score score' S v x)
          (hybridScore score score' S v y) ≤
        scoreLevel c₁ (hybridScore score score' S v y) := by
    intro y hy
    rw [hhybv, hc₁ y hy]
    exact scoreLevel_le_of_scoreWeakProfileImprovement himp v hy
  have hraise :
      F τ (scoreProfileMargin (hybridScore score score' S)) ρ x ≤
        F τ (scoreProfileMargin (Function.update (hybridScore score score' S) v
          (Function.update (hybridScore score score' S v) x c₁))) ρ x :=
    nlhf_single_voter_raise_selected hselect hselected hτge hρ v
      (raiseMeasure (hybridScore score score' S v)
        (hybridScore score score' S v x) c₁ x)
      (hybridScore score score' S) c₁ hlev le_rfl
  -- Step 2: the resulting profile has the same signs as the new hybrid.
  have hsame :
      scoreProfileMargin (Function.update (hybridScore score score' S) v
          (Function.update (hybridScore score score' S v) x c₁)) =
        scoreProfileMargin (hybridScore score score' (insert v S)) := by
    refine scoreProfileMargin_congr_signs _ _ ?_
    intro u a b
    by_cases hu : u = v
    · subst hu
      have hupd : Function.update (hybridScore score score' S) u
          (Function.update (hybridScore score score' S u) x c₁) u =
          Function.update (score u) x c₁ := by
        rw [Function.update_self, hhybv]
      rw [hupd, hhybvins]
      have hgx : Function.update (score u) x c₁ x = c₁ := by simp
      have hgy : ∀ y : α, y ≠ x →
          Function.update (score u) x c₁ y = score u y := by
        intro y hy
        simp only [Function.update_apply, if_neg hy]
      have hkey : ∀ y : α, y ≠ x →
          scoreMarginSignReal c₁ (score u y) =
            scoreMarginSignReal (score' u x) (score' u y) := by
        intro y hy
        rw [scoreMarginSignReal_eq_scoreLevel, scoreMarginSignReal_eq_scoreLevel,
          hc₁ y hy]
      by_cases hax : a = x
      · by_cases hbx : b = x
        · rw [hax, hbx, hgx, scoreMarginSignReal_of_eq (rfl : c₁ = c₁),
            scoreMarginSignReal_of_eq (rfl : score' u x = score' u x)]
        · rw [hax, hgx, hgy b hbx]
          exact hkey b hbx
      · by_cases hbx : b = x
        · rw [hbx, hgx, hgy a hax,
            scoreMarginSignReal_antisymm (score u a) c₁,
            scoreMarginSignReal_antisymm (score' u a) (score' u x), hkey a hax]
        · rw [hgy a hax, hgy b hbx,
            scoreMarginSignReal_eq_scoreLevel,
            scoreMarginSignReal_eq_scoreLevel, hoff a b hax hbx]
    · rw [Function.update_apply, if_neg hu, hhybu u hu]
  rw [hsame] at hraise
  exact hraise

/-- Master `1/8` chaining theorem: the paper's improvement conditions
(i)–(iii) on a score-represented weak-order profile give monotonicity, by
hybridizing over voters and moving `x` up one tied block at a time. -/
theorem nlhf_scoreProfile_improvement_monotone_of_tau_ge_one_eighth_selected
    (hselect : IsNLHFFixedPointSelection F)
    (hselected : SatisfiesNLHFSelectedVariationalInequality F)
    (hτge : (1 : ℝ) / 8 ≤ τ)
    (hρ : IsFullSupportLottery ρ)
    (himp : IsWeakProfileImprovement (scoreWeakProfile score)
      (scoreWeakProfile score') x) :
    F τ (scoreProfileMargin score) ρ x ≤
      F τ (scoreProfileMargin score') ρ x := by
  classical
  have hbase : hybridScore score score' (∅ : Finset V) = score := by
    funext u
    simp [hybridScore]
  have htop : hybridScore score score' (Finset.univ : Finset V) = score' := by
    funext u
    simp [hybridScore]
  have hchain : ∀ S : Finset V,
      F τ (scoreProfileMargin score) ρ x ≤
        F τ (scoreProfileMargin (hybridScore score score' S)) ρ x := by
    intro S
    induction S using Finset.induction_on with
    | empty => rw [hbase]
    | insert v S hv ih =>
      exact le_trans ih
        (nlhf_hybrid_insert_step hselect hselected hτge hρ himp v S hv)
  have := hchain (Finset.univ : Finset V)
  rwa [htop] at this

end Hybrid

end PaperFormalization
