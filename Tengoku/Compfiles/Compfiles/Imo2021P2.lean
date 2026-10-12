/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw, Benpigchu
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2021, Problem 2

Let n be a natural number, and let x₁, ..., xₙ be real numbers.
Show that

     ∑ᵢ∑ⱼ √|xᵢ - xⱼ| ≤ ∑ᵢ∑ⱼ √|xᵢ + xⱼ|.

-/

namespace Imo2021P2

universe u

def PiecewiseConcaveOn (s : Finset ℝ) (f : ℝ → ℝ) :=
  (∀ l r : ℝ, l ≤ r → (∀ t ∈ s, t ≤ l ∨ r ≤ t) → ConcaveOn ℝ (Set.Icc l r) f)

/--
@isnad1 id=piecewis.2h4v.s5.5f9cd0baadf0 from=translated src=- shape=74a4f49e vocab=6a3069b1
-/
lemma piecewise_concave_add {s₁ s₂ : Finset ℝ} {f₁ f₂ : ℝ → ℝ}
    (h₁ : PiecewiseConcaveOn s₁ f₁) (h₂ : PiecewiseConcaveOn s₂ f₂)
    : PiecewiseConcaveOn (s₁ ∪ s₂) (f₁ + f₂) := by
  intro l r hlr hslr
  apply ConcaveOn.add
  · apply h₁ l r hlr
    intro t ht
    apply hslr
    apply Finset.mem_union_left
    exact ht
  · apply h₂ l r hlr
    intro t ht
    apply hslr
    apply Finset.mem_union_right
    exact ht

/--
@isnad1 id=piecewis.1h4v.s6.a7f034e9f20c from=translated src=- shape=6238bcb8 vocab=d218ddd1
-/
lemma piecewise_concave_sum {α : Type u} [DecidableEq α] (s : Finset α)
    (s' : α → Finset ℝ) (f' : α → ℝ → ℝ)
    (h : ∀ i ∈ s, PiecewiseConcaveOn (s' i) (f' i))
    : PiecewiseConcaveOn (s.biUnion s') (∑ i ∈ s, f' i) := by
  induction' s using Finset.cons_induction with i s'' his'' hs''
  · rw [Finset.sum_empty, Finset.biUnion_empty]
    intro l r hlr hlr'
    apply concaveOn_const
    apply convex_Icc
  · rw [Finset.sum_cons, Finset.cons_eq_insert, Finset.biUnion_insert]
    apply piecewise_concave_add
    · apply h
      apply Finset.mem_cons_self
    · apply hs''
      intro i' hi's'
      apply h
      apply Finset.mem_cons_of_mem hi's'

def UnboundedAtPosInfinity (f : ℝ → ℝ) :=
  (∀ y : ℝ, ∃ x : ℝ, ∀ t : ℝ, x ≤ t → y ≤ f t)

/--
@isnad1 id=unbounde.2h2v.s5.75818871d7ef from=translated src=- shape=688438e4 vocab=ce825d2b
-/
lemma unbounded_at_pos_infinity_add {f₁ f₂ : ℝ → ℝ}
    (h₁ : UnboundedAtPosInfinity f₁) (h₂ : UnboundedAtPosInfinity f₂)
    : UnboundedAtPosInfinity (f₁ + f₂) := by
  intro y
  rcases h₁ (y / 2) with ⟨x₁, hx₁⟩
  rcases h₂ (y / 2) with ⟨x₂, hx₂⟩
  use max x₁ x₂
  intro t ht
  rw [Pi.add_apply]
  rw [(by ring : y = y / 2 + y / 2)]
  grind

/--
@isnad1 id=unbounde.2h3v.s5.5dac83929676 from=translated src=- shape=5e8828b4 vocab=28c6bb93
-/
lemma unbounded_at_pos_infinity_sum {α : Type u} (s : Finset α) (hs : s.Nonempty)
    (f' : α → ℝ → ℝ)
    (h : ∀ i ∈ s, UnboundedAtPosInfinity (f' i))
    : UnboundedAtPosInfinity (∑ i ∈ s, f' i) := by
  induction' hs using Finset.Nonempty.cons_induction with i i s' his' hs' h'
  · rw [Finset.sum_singleton]
    apply h
    apply Finset.mem_singleton_self
  · rw [Finset.sum_cons]
    apply unbounded_at_pos_infinity_add
    · apply h
      apply Finset.mem_cons_self
    · apply h'
      intro i' hi's'
      apply h
      apply Finset.mem_cons_of_mem hi's'

def UnboundedAtNegInfinity (f : ℝ → ℝ) :=
  (∀ y : ℝ, ∃ x : ℝ, ∀ t : ℝ, t ≤ x → y ≤ f t)

/--
@isnad1 id=unbounde.2h2v.s5.e2a88dc8f84c from=translated src=- shape=688438e4 vocab=ceeca3a6
-/
lemma unbounded_at_neg_infinity_add {f₁ f₂ : ℝ → ℝ}
    (h₁ : UnboundedAtNegInfinity f₁) (h₂ : UnboundedAtNegInfinity f₂)
    : UnboundedAtNegInfinity (f₁ + f₂) := by
  intro y
  rcases h₁ (y / 2) with ⟨x₁, hx₁⟩
  rcases h₂ (y / 2) with ⟨x₂, hx₂⟩
  use min x₁ x₂
  intro t ht
  rw [Pi.add_apply]
  rw [(by ring : y = y / 2 + y / 2)]
  grind

/--
@isnad1 id=unbounde.2h3v.s5.db846f4df66b from=translated src=- shape=5e8828b4 vocab=6a1b180a
-/
lemma unbounded_at_neg_infinity_sum {α : Type u} (s : Finset α) (hs : s.Nonempty)
    (f' : α → ℝ → ℝ)
    (h : ∀ i ∈ s, UnboundedAtNegInfinity (f' i))
    : UnboundedAtNegInfinity (∑ i ∈ s, f' i) := by
  induction' hs using Finset.Nonempty.cons_induction with i i s' his' hs' h'
  · rw [Finset.sum_singleton]
    apply h
    apply Finset.mem_singleton_self
  · rw [Finset.sum_cons]
    apply unbounded_at_neg_infinity_add
    · apply h
      apply Finset.mem_cons_self
    · apply h'
      intro i' hi's'
      apply h
      apply Finset.mem_cons_of_mem hi's'

def PiecewiseConcavePlusOn (s : Finset ℝ) (f : ℝ → ℝ) :=
  PiecewiseConcaveOn s f
  ∧ UnboundedAtPosInfinity f
  ∧ UnboundedAtNegInfinity f

/--
@isnad1 id=piecewis.2h4v.s6.4c9cacb72d92 from=translated src=- shape=cba1fd5f vocab=191ca503
-/
lemma piecewise_concave_plus_sum {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty)
    (s' : α → Finset ℝ) (f' : α → ℝ → ℝ)
    (h : ∀ i ∈ s, PiecewiseConcavePlusOn (s' i) (f' i))
    : PiecewiseConcavePlusOn (s.biUnion s') (∑ i ∈ s, f' i) := by
  rw [PiecewiseConcavePlusOn]
  constructorm* _ ∧ _
  · have h' : ∀ i ∈ s, PiecewiseConcaveOn (s' i) (f' i) := by
      intro i hi
      exact (h i hi).left
    exact piecewise_concave_sum s s' f' h'
  · have h' : ∀ i ∈ s, UnboundedAtPosInfinity (f' i) := by
      intro i hi
      exact (h i hi).right.left
    exact unbounded_at_pos_infinity_sum s hs f' h'
  · have h' : ∀ i ∈ s, UnboundedAtNegInfinity (f' i) := by
      intro i hi
      exact (h i hi).right.right
    exact unbounded_at_neg_infinity_sum s hs f' h'

def ExistsDecreaseOn (s : Finset ℝ) (f : ℝ → ℝ) :=
  ∀ t : ℝ, ∃ x ∈ s , f x ≤ f t

/--
@isnad1 id=existsde.1h2v.s3.8429d8f1d7cf from=translated src=- shape=4dae6d34 vocab=ba536195
-/
lemma exists_decrease_of_piecewise_concave_plus {s : Finset ℝ} {f : ℝ → ℝ}
    (h : PiecewiseConcavePlusOn s f) : ExistsDecreaseOn s f := by
  rcases h with ⟨h₁, h₂, h₃⟩
  intro t
  set l := {x ∈ s | x ≤ t }.max
  set r := {x ∈ s | t ≤ x }.min
  by_cases hlr : l = ⊥ ∧ r = ⊤
  · exfalso
    rcases hlr with ⟨hl, hr⟩
    simp only [l] at hl
    simp only [r] at hr
    rw [Finset.max_eq_bot] at hl
    rw [Finset.min_eq_top] at hr
    rw [Finset.eq_empty_iff_forall_notMem] at hl hr
    have hs : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x
      by_cases! hx : x ≤ t
      · contrapose! hl
        use x
        rw [Finset.mem_filter]
        exact ⟨hl, hx⟩
      · contrapose! hr
        use x
        rw [Finset.mem_filter]
        exact ⟨hr, le_of_lt hx⟩
    rcases h₂ (f t + 1) with ⟨r', hr'⟩
    rcases h₃ (f t + 1) with ⟨l', hl'⟩
    have hl'r' : min t l' ≤ max t r' := le_trans (min_le_left _ _) (le_max_left _ _)
    have hl'r's : ∀ x ∈ s, x ≤ min t l' ∨ max t r' ≤ x := by
      rw [hs]
      intro x hx
      contrapose! hx
      apply Finset.notMem_empty
    have h' := h₁ (min t l') (max t r') hl'r' hl'r's
    have ht : t ∈ Set.Icc (min t l') (max t r') := by
      rw [Set.mem_Icc]
      exact ⟨min_le_left _ _, le_max_left _ _⟩
    have h'' := ConcaveOn.min_le_of_mem_Icc h' (Set.left_mem_Icc.mpr hl'r') (Set.right_mem_Icc.mpr hl'r') ht
    contrapose! h''
    apply lt_of_lt_of_le (lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 1))
    apply le_min
    · apply hl'
      apply min_le_right
    · apply hr'
      apply le_max_right
  · by_cases hlr' : l ≠ ⊥ ∧ r ≠ ⊤
    · rcases hlr' with ⟨hl, hr⟩
      set l' := WithBot.unbot l hl with hl'
      set r' := WithTop.untop r hr with hr'
      rw [WithBot.eq_unbot_iff] at hl'
      rw [WithTop.eq_untop_iff] at hr'
      simp only [l] at hl'
      simp only [r] at hr'
      symm at hl' hr'
      have hl'' := Finset.mem_of_max hl'
      have hr'' := Finset.mem_of_min hr'
      rw [Finset.mem_filter] at hl'' hr''
      have hl'r' : l' ≤ r' := le_trans hl''.right hr''.right
      have hl'r's : ∀ x ∈ s, x ≤ l' ∨ r' ≤ x := by
        intro x hx
        by_cases! hx' : x ≤ t
        · left
          apply Finset.le_max_of_eq _ hl'
          rw [Finset.mem_filter]
          exact ⟨hx, hx'⟩
        · right
          apply Finset.min_le_of_eq _ hr'
          rw [Finset.mem_filter]
          exact ⟨hx, le_of_lt hx'⟩
      have h' := h₁ l' r' hl'r' hl'r's
      have ht : t ∈ Set.Icc l' r' := by
        rw [Set.mem_Icc]
        exact ⟨hl''.right, hr''.right⟩
      have h'' := ConcaveOn.min_le_of_mem_Icc h' (Set.left_mem_Icc.mpr hl'r') (Set.right_mem_Icc.mpr hl'r') ht
      rcases min_choice (f l') (f r') with hmin|hmin <;> rw [hmin] at h''
      · use l'
        rw [and_iff_left h'']
        exact hl''.left
      · use r'
        rw [and_iff_left h'']
        exact hr''.left
    · have hlr'' : (l = ⊥ ∧ r ≠ ⊤) ∨ (l ≠ ⊥ ∧ r = ⊤) := by tauto
      rcases hlr'' with ⟨hl, hr⟩|⟨hl, hr⟩
      · set r' := WithTop.untop r hr with hr'
        rw [WithTop.eq_untop_iff] at hr'
        simp only [l] at hl
        simp only [r] at hr'
        rw [Finset.max_eq_bot] at hl
        rw [Finset.eq_empty_iff_forall_notMem] at hl
        symm at hr'
        have hr'' := Finset.mem_of_min hr'
        rw [Finset.mem_filter] at hr''
        rcases h₃ (f t + 1) with ⟨l', hl'⟩
        have hl'r' : min t l' ≤ r' := le_trans (min_le_left _ _) (hr''.right)
        have hl'r's : ∀ x ∈ s, x ≤ min t l' ∨ r' ≤ x := by
          intro x hx
          by_cases! hx' : x ≤ t
          · contrapose! hl
            use x
            rw [Finset.mem_filter]
            exact ⟨hx, hx'⟩
          · right
            apply Finset.min_le_of_eq _ hr'
            rw [Finset.mem_filter]
            exact ⟨hx, le_of_lt hx'⟩
        have h' := h₁ (min t l') r' hl'r' hl'r's
        have ht : t ∈ Set.Icc (min t l') r' := by
          rw [Set.mem_Icc]
          exact ⟨min_le_left _ _, hr''.right⟩
        have h'' := ConcaveOn.min_le_of_mem_Icc h' (Set.left_mem_Icc.mpr hl'r') (Set.right_mem_Icc.mpr hl'r') ht
        rcases min_choice (f (min t l')) (f r') with hmin|hmin <;> rw [hmin] at h''
        · contrapose! hl'
          use min t l'
          rw [and_iff_right (min_le_right _ _)]
          exact lt_of_le_of_lt h'' (lt_add_one _)
        · use r'
          rw [and_iff_left h'']
          exact hr''.left
      · set l' := WithBot.unbot l hl with hl'
        rw [WithBot.eq_unbot_iff] at hl'
        simp only [l] at hl'
        simp only [r] at hr
        rw [Finset.min_eq_top] at hr
        rw [Finset.eq_empty_iff_forall_notMem] at hr
        symm at hl'
        have hl'' := Finset.mem_of_max hl'
        rw [Finset.mem_filter] at hl''
        rcases h₂ (f t + 1) with ⟨r', hr'⟩
        have hl'r' : l' ≤ (max t r') := le_trans (hl''.right) (le_max_left _ _)
        have hl'r's : ∀ x ∈ s, x ≤ l' ∨ (max t r') ≤ x := by
          intro x hx
          by_cases! hx' : x ≤ t
          · left
            apply Finset.le_max_of_eq _ hl'
            rw [Finset.mem_filter]
            exact ⟨hx, hx'⟩
          · contrapose! hr
            use x
            rw [Finset.mem_filter]
            exact ⟨hx, le_of_lt hx'⟩
        have h' := h₁ l' (max t r') hl'r' hl'r's
        have ht : t ∈ Set.Icc l' (max t r') := by
          rw [Set.mem_Icc]
          exact ⟨hl''.right, le_max_left _ _⟩
        have h'' := ConcaveOn.min_le_of_mem_Icc h' (Set.left_mem_Icc.mpr hl'r') (Set.right_mem_Icc.mpr hl'r') ht
        rcases min_choice (f l') (f (max t r')) with hmin|hmin <;> rw [hmin] at h''
        · use l'
          rw [and_iff_left h'']
          exact hl''.left
        · contrapose! hr'
          use (max t r')
          rw [and_iff_right (le_max_right _ _)]
          apply lt_of_le_of_lt h''
          exact lt_add_one (f t)

noncomputable def Finset.SumSqrtDist {α : Type u} (s : Finset α)
    (x : α → ℝ) (t : ℝ) := ∑ i ∈ s, √|x i - t|

/--
@isnad1 id=piecewis.0h1v.s4.9cff4d4a5279 from=translated src=- shape=a8d1c009 vocab=3efca018
-/
lemma piecewise_concave_sqrt_dist (x : ℝ) :
    PiecewiseConcaveOn {x} (fun t ↦ √|x - t|) := by
  intro l r hlr hlr'
  have hx := hlr' x (Finset.mem_singleton_self x)
  set f := fun (t : ℝ) ↦ |x - t|
  set g := fun (t : ℝ) ↦ t ^ ((1 : ℝ) / 2)
  have h' : (fun t ↦ √|x - t|) = g ∘ f := by
    ext t
    simp only [Function.comp_apply, g, f]
    rw [Real.sqrt_eq_rpow]
  rw [h']
  have hf : f '' Set.Icc l r ⊆ Set.Ici 0 := by
    simp only [f]
    intro y hy
    rw [Set.mem_image] at hy
    rw [Set.mem_Ici]
    rcases hy with ⟨t, ht', ht⟩
    rw [← ht]
    positivity
  apply ConcaveOn.comp
  · simp only [g]
    have h'' := Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : 1 / 2 ≤ (1 : ℝ))
    apply ConcaveOn.subset h'' hf
    rcases hx with (hx|hx)
    · have hf : f '' Set.Icc l r = (fun t ↦ -x + (1 : ℝ) • t) '' Set.Icc l r := by
        apply Set.image_congr
        intro t ht
        simp only [Set.mem_Icc] at ht
        simp only [f]
        rw [smul_eq_mul, (by ring : -x + (1 : ℝ) * t = -(x - t))]
        apply abs_of_nonpos
        rw [sub_nonpos]
        apply le_trans hx ht.left
      rw [hf]
      exact Convex.affinity (convex_Icc l r) (-x) (1 : ℝ)
    · have hf : f '' Set.Icc l r = (fun t ↦ x + (-1 : ℝ) • t) '' Set.Icc l r := by
        apply Set.image_congr
        intro t ht
        simp only [Set.mem_Icc] at ht
        simp only [f]
        rw [smul_eq_mul, (by ring : x + (-1 : ℝ) * t = x - t)]
        apply abs_of_nonneg
        rw [sub_nonneg]
        apply le_trans ht.right hx
      rw [hf]
      exact Convex.affinity (convex_Icc l r) x (-1 : ℝ)
  · rw [ConcaveOn, and_iff_right (convex_Icc _ _)]
    intro p hp q hq a b ha hb hab
    repeat rw [smul_eq_mul]
    simp only [f]
    apply le_of_eq
    have h' : x - (a * p + b * q) = a * (x - p) + b * (x - q) := by
      nth_rw 1 [← one_mul x]
      rw [← hab]
      ring
    rw [h']
    simp only [Set.mem_Icc] at hp hq
    rcases hx with (hx|hx)
    · have hpx : x - p ≤ 0 := by
        rw [sub_nonpos]
        apply le_trans hx hp.left
      have hqx : x - q ≤ 0 := by
        rw [sub_nonpos]
        apply le_trans hx hq.left
      have h'x : a * (x - p) + b * (x - q) ≤ 0 := by
        apply add_nonpos
        · apply mul_nonpos_of_nonneg_of_nonpos ha hpx
        · apply mul_nonpos_of_nonneg_of_nonpos hb hqx
      rw [abs_of_nonpos hpx, abs_of_nonpos hqx, abs_of_nonpos h'x]
      ring
    · have hpx : 0 ≤ x - p  := by
        rw [sub_nonneg]
        apply le_trans hp.right hx
      have hqx : 0 ≤ x - q := by
        rw [sub_nonneg]
        apply le_trans hq.right hx
      have h'x : 0 ≤ a * (x - p) + b * (x - q) := by positivity
      rw [abs_of_nonneg hpx, abs_of_nonneg hqx, abs_of_nonneg h'x]
  · simp only [g]
    have h'' := Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply MonotoneOn.mono h'' hf

/--
@isnad1 id=unbounde.0h1v.s4.8ce1543765cc from=translated src=- shape=930a5fa4 vocab=e9f894c9
-/
lemma unbounded_at_pos_infinity_sqrt_dist (x : ℝ) :
    UnboundedAtPosInfinity (fun t ↦ √|x - t|) := by
  intro y
  use (x + y ^ 2)
  intro t ht
  dsimp only
  rw [← le_sub_iff_add_le'] at ht
  apply Real.le_sqrt_of_sq_le
  rw [abs_sub_comm, abs_of_nonneg (le_trans (sq_nonneg _) ht)]
  exact ht

/--
@isnad1 id=unbounde.0h1v.s4.30e3212f02d0 from=translated src=- shape=930a5fa4 vocab=689fa583
-/
lemma unbounded_at_neg_infinity_sqrt_dist (x : ℝ) :
    UnboundedAtNegInfinity (fun t ↦ √|x - t|) := by
  intro y
  use (x - y ^ 2)
  intro t ht
  dsimp only
  rw [← le_sub_comm] at ht
  apply Real.le_sqrt_of_sq_le
  rw [abs_of_nonneg (le_trans (sq_nonneg _) ht)]
  exact ht

/--
@isnad1 id=piecewis.0h1v.s4.fe49bda8c9e2 from=translated src=- shape=a8d1c009 vocab=a5ee5eab
-/
lemma piecewise_concave_plus_sqrt_dist (x : ℝ) :
    PiecewiseConcavePlusOn {x} (fun t ↦ √|x - t|) := by
  rw [PiecewiseConcavePlusOn]
  constructorm* _ ∧ _
  · exact piecewise_concave_sqrt_dist x
  · exact unbounded_at_pos_infinity_sqrt_dist x
  · exact unbounded_at_neg_infinity_sqrt_dist x

/--
@isnad1 id=piecewis.1h3v.s4.351e080e6091 from=translated src=- shape=df389095 vocab=a2f711d6
-/
lemma piecewise_concave_plus_sum_sqrt_dist {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (x : α → ℝ) :
      PiecewiseConcavePlusOn (s.image x) (Finset.SumSqrtDist s x) := by
    have h' : ∀ i ∈ s, PiecewiseConcavePlusOn {x i} (fun t ↦ √|x i - t|) := by
      intro i hi
      exact piecewise_concave_plus_sqrt_dist (x i)
    have h := piecewise_concave_plus_sum s hs (fun i ↦ {x i}) (fun i ↦ fun t ↦ √|x i - t|) h'
    have hsum : ∑ i ∈ s, (fun t ↦ √|x i - t|) = Finset.SumSqrtDist s x := by
      ext t
      rw [Finset.SumSqrtDist]
      apply Finset.sum_apply
    rw [Finset.biUnion_singleton, hsum] at h
    exact h

/--
@isnad1 id=existsde.1h3v.s4.668c2fdb1e0f from=translated src=- shape=df389095 vocab=e00f49f6
-/
lemma exists_decrease_sum_sqrt_dist {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (x : α → ℝ) :
    ExistsDecreaseOn (s.image x) (Finset.SumSqrtDist s x) := by
  apply exists_decrease_of_piecewise_concave_plus
  exact piecewise_concave_plus_sum_sqrt_dist s hs x

/--
@isnad1 id=ex.1h3v.s6.35784287a43a from=translated src=- shape=dcf1ef3d vocab=09001622
-/
lemma exists_sum_sqrt_dist_le_sum_sqrt_dist {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (x : α → ℝ) :
  ∃ k ∈ s, ∑ i ∈ s, √|x i - x k| ≤ ∑ i ∈ s, √|x i| := by
  have h := exists_decrease_sum_sqrt_dist s hs x 0
  rcases h with ⟨xk, hxks, hxk⟩
  rw [Finset.mem_image] at hxks
  rcases hxks with ⟨k, hks, hk⟩
  use k
  rw [and_iff_right hks]
  rw [Finset.SumSqrtDist, Finset.SumSqrtDist, ← hk] at hxk
  ring_nf at hxk
  exact hxk

/--
@isnad1 id=ex.1h3v.s7.c2225bbfce2b from=translated src=- shape=59a9c54b vocab=baf59cb2
-/
lemma decrease_sum {α : Type u} [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (x : α → ℝ) :
  ∃ k ∈ s, ∃ l ∈ s, ∑ i ∈ s, ∑ j ∈ s, √|x i + x j - (x k + x l)| ≤ ∑ i ∈ s, ∑ j ∈ s, √|x i + x j| := by
  have h := exists_sum_sqrt_dist_le_sum_sqrt_dist (s ×ˢ s) (Finset.Nonempty.product hs hs) (fun (i,j) ↦ x i + x j)
  rcases h with ⟨⟨k, l⟩, hkls, hkl⟩
  simp [Finset.mem_product] at hkls
  simp [Finset.sum_product] at hkl
  use k
  rw [and_iff_right hkls.left]
  use l
  rw [and_iff_right hkls.right]
  exact hkl

/--
@isnad1 id=le.0h3v.s6.8b4fc8f59846 from=translated src=- shape=c83cf3df vocab=c8689385
-/
theorem imo2021_p2_finset_version {α : Type u} [DecidableEq α] (s : Finset α) (x : α → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, √|x i - x j| ≤ ∑ i ∈ s, ∑ j ∈ s, √|x i + x j| := by
  induction' s using Finset.strongInductionOn with s h generalizing x
  by_cases! hs : ¬s.Nonempty
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    rw [hs, Finset.sum_empty, Finset.sum_empty]
  · rcases decrease_sum s hs x with ⟨k, hk, l, hl, hkl⟩
    apply le_trans' hkl
    by_cases! hkl' : k = l
    · rw [← hkl']
      set s' := s.erase k with hs'
      set x' := fun i ↦ x i - x k
      have h' := h s' (Finset.erase_ssubset hk) x'
      simp only [x'] at h'
      rw [← Finset.insert_erase hk]
      repeat rw [Finset.sum_insert (Finset.notMem_erase k s)]
      nth_rw 1 [Finset.sum_comm]
      nth_rw 2 [Finset.sum_comm]
      repeat rw [Finset.sum_insert (Finset.notMem_erase k s)]
      nth_rw 1 [Finset.sum_comm]
      nth_rw 2 [Finset.sum_comm]
      repeat rw [← hs']
      have hsum₁ : ∀ i ∈ s', √|x k - x i| = √|x i - x k| := by
        intro i hi
        rw [← abs_neg]
        ring_nf
      rw [Finset.sum_congr rfl hsum₁]
      ring_nf at ⊢ h'
      exact (add_le_add_iff_left _).mpr h'
    · set s' := s \ {k, l} with hs'
      set x' := fun i ↦ x i - (x k + x l) / 2
      have hkl'' : {k, l} ⊆ s := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hk, hl⟩
      have h' := h s' (Finset.sdiff_ssubset hkl'' (Finset.insert_nonempty _ _)) x'
      simp only [x'] at h'
      rw [← Finset.sdiff_union_of_subset hkl'']
      repeat rw [Finset.sum_union Finset.sdiff_disjoint, Finset.sum_pair hkl']
      nth_rw 1 [Finset.sum_comm]
      nth_rw 2 [Finset.sum_comm]
      repeat rw [Finset.sum_union Finset.sdiff_disjoint, Finset.sum_pair hkl']
      nth_rw 1 [Finset.sum_comm]
      nth_rw 2 [Finset.sum_comm]
      repeat rw [← hs']
      have hsum₁ : ∀ i ∈ s', √|x k - x i| = √|x i - x k| := by
        intro i hi
        rw [← abs_neg]
        ring_nf
      have hsum₂ : ∀ i ∈ s', √|x l - x i| = √|x i - x l| := by
        intro i hi
        rw [← abs_neg]
        ring_nf
      rw [Finset.sum_congr rfl hsum₁, Finset.sum_congr rfl hsum₂]
      ring_nf at ⊢ h'
      repeat rw [add_assoc]
      rw [add_comm]
      repeat rw [add_assoc]
      repeat rw [add_le_add_iff_left]
      exact h'

end Imo2021P2
