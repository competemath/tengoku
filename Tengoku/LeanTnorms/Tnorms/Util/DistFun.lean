/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku
import Tengoku.LeanTnorms.Tnorms.Util.Interpolate

/-!
TODOs:
  * General proof cleanup
  * File docstring
  * Does this generalize?  Is it useful to do so?
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
variable {X : Type*} [MetricSpace X]

open unitInterval

open Classical in
noncomputable
def _root_.Tengoku.LeanTnorms.dist_fun (x : ℕ → X) (y : X) (p : ℕ → I) (q : I) : ℝ → I := fun a ↦
  if a ≤ 0 then q else
  if hn : ∃ n, dist (x (n + 1)) y < a ∧ a ≤ dist (x n) y then
  interpolate_n (fun n ↦ dist (x n) y) p (Classical.choose hn) a else p 0

open Classical in
noncomputable
def _root_.Tengoku.LeanTnorms.dist_fun_compactSupport (x : ℕ → X) (y : X) (p : ℕ → I) (q : I) : ℝ → I := fun a ↦
  if a ≤ -1 then 0 else
  if -1 ≤ a ∧ a ≤ 0 then interpolate (-1) 0 0 q a else
  if hn : ∃ n, dist (x (n + 1)) y < a ∧ a ≤ dist (x n) y then
  interpolate_n (fun n ↦ dist (x n) y) p (Classical.choose hn) a else
  if dist (x 0) y ≤ a ∧ a ≤ dist (x 0) y + 1 then
  interpolate (dist (x 0) y) (dist (x 0) y + 1) (p 0) 0 a else 0

open Classical in
noncomputable
def _root_.Tengoku.LeanTnorms.correction (x : ℕ → X) (y : X) (p : I) (q : I) : ℝ → I := fun a ↦
  if a ≤ -1 then q else
  if -1 ≤ a ∧ a ≤ 0 then interpolate (-1) 0 q 0 a else
  if ∃ n, dist (x (n + 1)) y < a ∧ a ≤ dist (x n) y then 0 else
  if dist (x 0) y ≤ a ∧ a ≤ dist (x 0) y + 1 then
  interpolate (dist (x 0) y) (dist (x 0) y + 1) 0 p a
  else p

noncomputable
def _root_.Tengoku.LeanTnorms.correction1 (x : ℕ → X) (y : X) (p : I) : ℝ → I := fun a ↦
  if a ≤ dist (x 0) y then 0
  else if dist (x 0) y ≤ a ∧ a ≤ dist (x 0) y + 1 then
  interpolate (dist (x 0) y) (dist (x 0) y + 1) 0 p a
  else p

noncomputable
def _root_.Tengoku.LeanTnorms.correction2 (q : I) : ℝ → I := fun a ↦
  if a ≤ -1 then q else
  if -1 ≤ a ∧ a ≤ 0 then interpolate (-1) 0 q 0 a
  else 0

/--
@isnad1 id=eq.2h6v.s6.ee137fc396e9 from=translated src=- shape=70c85435 vocab=c194b5ef
-/
lemma _root_.Tengoku.LeanTnorms.correction_add (x : ℕ → X) (y : X) (p : I) (q : I) (a : ℝ)
    (hxt : Filter.Tendsto x Filter.atTop (nhds y))
    (hx : StrictAnti (fun n ↦ dist (x n) y)) :
    (correction x y p q a).1  = (correction1 x y p a).1 + (correction2 q a).1 := by
  simp [correction, correction1, correction2]
  have hd : dist (x 1) y < dist (x 0) y := hx zero_lt_one
  split_ifs <;> simp
  repeat grind [dist_nonneg]
  · rename_i ha1 ha01 hn had hd
    obtain ⟨n, hn⟩ := hn
    have hn0 : dist (x n) y ≤ dist (x 0) y := StrictAnti.antitone hx (Nat.zero_le n)
    grind
  · rename_i ha1 ha01 hn had hd
    obtain ⟨n, hn⟩ := hn
    have hn0 : dist (x n) y ≤ dist (x 0) y := StrictAnti.antitone hx (Nat.zero_le n)
    grind
  · have had : a = dist (x 0) y := by grind
    rw [had, interpolate_left]
    exact lt_add_one _
  · rename_i ha1 ha01 hn had hd
    rw [tendsto_iff_dist_tendsto_zero, tendsto_order] at hxt
    apply And.right at hxt
    specialize hxt a (by grind)
    simp at hxt
    obtain ⟨m, hm⟩ := hxt
    specialize hm m (by rfl)
    contrapose! hn
    rw [← not_lt] at hd
    simp_rw [and_comm, ← not_lt]
    exact Nat.exists_not_and_succ_of_not_zero_of_exists hd (by grind)

/--
@isnad1 id=uniformc.2h5v.s6.0dcf48d627c6 from=translated src=- shape=81b80c1d vocab=0a2b9db3
-/
lemma _root_.Tengoku.LeanTnorms.correction_uniformContinuous {x : ℕ → X} {y : X} {p : I} {q : I}
    (hxt : Filter.Tendsto x Filter.atTop (nhds y))
    (hx : StrictAnti (fun n ↦ dist (x n) y)) :
    UniformContinuous (correction x y p q) := by
  let f : ℝ → I := fun a ↦ ⟨(correction1 x y p a).1 + (correction2 q a).1, by
    rw [← correction_add _ _ _ _ _ hxt hx]
    exact Subtype.coe_prop _⟩
  rw [show correction x y p q = f by ext a; rw [correction_add _ _ _ _ _ hxt hx]]
  refine UniformContinuous.subtype_mk ?_ _
  refine UniformContinuous.add ?_ ?_
  · refine UniformContinuous.comp uniformContinuous_subtype_val ?_
    exact ite_interpolate_uniformContinuous _ _ _ _ (lt_add_one _)
  · refine UniformContinuous.comp uniformContinuous_subtype_val ?_
    exact ite_interpolate_uniformContinuous _ _ _ _ (by norm_num)

/--
@isnad1 id=continuo.3h5v.s7.9e90e7e50c96 from=translated src=- shape=3be2b2b6 vocab=43f118f6
-/
lemma ContinuousOn.Icc_of_tendsto_endpoints {α β : Type*} [TopologicalSpace α]
    [LinearOrder α] [DenselyOrdered α] [OrderTopology α] [TopologicalSpace β] [RegularSpace β]
    [T2Space β] {f : α → β} {a b : α} (h : ContinuousOn f (Set.Ioo a b))
    (ha : Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds (f a)))
    (hb : Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds (f b))) :
    ContinuousOn f (Set.Icc a b) := by
  by_cases hab : a = b
  · simp [hab]
  suffices Set.EqOn f (extendFrom (Set.Ioo a b) f) (Set.Icc a b) by
    rw [continuousOn_congr this]
    exact continuousOn_Icc_extendFrom_Ioo h ha hb
  intro x hx
  symm
  rw [Set.mem_Icc] at hx
  by_cases! hax : a = x
  · subst hax
    exact eq_lim_at_left_extendFrom_Ioo (by grind) ha
  by_cases! hbx : b = x
  · subst hbx
    exact eq_lim_at_right_extendFrom_Ioo (by grind) hb
  refine extendFrom_extends h _ ?_
  grind

/--
@isnad1 id=tendsto.2h4v.s6.31a9d8e21ede from=translated src=- shape=1de20201 vocab=36a25a56
-/
lemma Metric.tendsto_nhdsWithin_Iio_of_tendsto_nhdsWithin_Ioc
    {f : ℝ → I} {a b : ℝ} {p : I} (hab : a < b)
    (h : Filter.Tendsto f (nhdsWithin b (Set.Ioc a b)) (nhds p)) :
    Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds p) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at h ⊢
  intro ε he
  specialize h ε he
  obtain ⟨δ, hd, h⟩ := h
  use min δ (dist a b)
  constructor
  · grind [Real.dist_eq]
  intro y hy hxy
  have hyo : y ∈ Set.Ioc a b := by grind [Real.dist_eq]
  exact h hyo (by grind)

/--
@isnad1 id=tendsto.2h5v.s6.b50656c62ac7 from=translated src=- shape=b02a6ac0 vocab=621198c5
-/
lemma Metric.tendsto_nhdsWithin_of_eqOn {f g : ℝ → I} {s : Set ℝ} {x : ℝ}
    {p : I} (h : Set.EqOn f g s) (hf : Filter.Tendsto f (nhdsWithin x s) (nhds p)) :
    Filter.Tendsto g (nhdsWithin x s) (nhds p) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hf ⊢
  grind

/--
@isnad1 id=tendsto.2h5v.s6.235e0df9916a from=translated src=- shape=d4b0fb11 vocab=b29a2f5e
-/
lemma Metric.tendsto_nhdsWithin_nhds_of_continuousOn {α β : Type*} [MetricSpace α] [MetricSpace β]
    {f : α → β} {s : Set α} {a : α} (ha : a ∈ s) (h : ContinuousOn f s) :
    Filter.Tendsto f (nhdsWithin a s) (nhds (f a)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  rw [Metric.continuousOn_iff] at h
  grind

/--
@isnad1 id=ne.1h4v.s5.c775c2e64560 from=translated src=- shape=808dfa09 vocab=87af80a4
-/
lemma _root_.Tengoku.LeanTnorms.ne_of_dist_strictAnti {x : ℕ → X} {y : X} (h : StrictAnti (fun n ↦ dist (x n) y))
    (n : ℕ) : x n ≠ y := by
  specialize h (lt_add_one n)
  simp only at h
  contrapose! h
  simp [h]

/--
@isnad1 id=eq.1h6v.s6.d88c8c8c76aa from=translated src=- shape=a0a062d7 vocab=24d5b049
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_apply_dist {x : ℕ → X} {y : X} {p : ℕ → I} {q : I} (n : ℕ)
    (hd : StrictAnti (fun n ↦ dist (x n) y)) :
    dist_fun_compactSupport x y p q (dist (x n) y) = p n := by
  have hd0 : dist (x n) y > 0 := lt_of_le_of_lt dist_nonneg (hd (lt_add_one n))
  have hd1 : ¬ dist (x n) y ≤ -1 := by grind
  have hd01 : ¬ (-1 ≤ dist (x n) y ∧ dist (x n) y ≤ 0) := by grind
  have hm : ∃ m, dist (x (m + 1)) y < dist (x n) y ∧ dist (x n) y ≤ dist (x m) y := by
    use n
    grind [hd (lt_add_one n)]
  simp only [dist_fun_compactSupport, hd1, hd01, interpolate_n]
  simp only [↓reduceIte, hm, ↓reduceDIte]
  suffices n = Classical.choose hm by
    rw [← this, interpolate_right]
    exact hd (lt_add_one n)
  have hn' := Classical.choose_spec hm
  refine le_antisymm ?_ ?_
  · apply And.left at hn'
    contrapose! hn'
    exact StrictAnti.antitone hd hn'
  · apply And.right at hn'
    contrapose! hn'
    exact hd hn'

/--
@isnad1 id=eq.0h5v.s5.d7f1005db420 from=translated src=- shape=239c8151 vocab=201f4c68
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_apply_zero {x : ℕ → X} {y : X} {p : ℕ → I} {q : I} :
  dist_fun_compactSupport x y p q 0 = q := by simp [dist_fun_compactSupport]

/--
@isnad1 id=eqon.1h6v.s7.f6a1b115841c from=translated src=- shape=91e2de13 vocab=e6d7c02f
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_eqOn_interpolate_Icc {x : ℕ → X} {y : X} {p : ℕ → I} {q : I} (n : ℕ)
    (hd : StrictAnti (fun n ↦ dist (x n) y)) :
    Set.EqOn (dist_fun_compactSupport x y p q)
      (interpolate (dist (x (n + 1)) y) (dist (x n) y) (p (n + 1)) (p n))
      (Set.Icc (dist (x (n + 1)) y) (dist (x n) y)) := by
  intro z hz
  rw [Set.mem_Icc] at hz
  have hz0 : z > 0 := by
    refine lt_of_lt_of_le ?_ hz.1
    exact lt_of_le_of_lt dist_nonneg (hd (lt_add_one (n + 1)))
  have hz1 : ¬ z ≤ -1 := by grind
  have hz01 : ¬ (-1 ≤ z ∧ z ≤ 0) := by grind
  by_cases! hnd : z = dist (x (n + 1)) y
  · rw [hnd, interpolate_left, dist_fun_compactSupport_apply_dist _ hd]
    exact hd (lt_add_one n)
  have hn : ∃ n, dist (x (n + 1)) y < z ∧ z ≤ dist (x n) y := by
    use n
    grind
  simp [dist_fun_compactSupport, hz1, hz01, hn, interpolate_n]
  suffices n = Classical.choose hn by rw [← this]
  have hn' := Classical.choose_spec hn
  refine le_antisymm ?_ ?_
  · apply And.left at hn'
    contrapose! hn'
    exact le_trans hz.2 <| StrictAnti.antitone hd hn'
  · apply And.right at hn'
    contrapose! hn'
    exact lt_of_le_of_lt (StrictAnti.antitone hd hn') (by grind)

/--
@isnad1 id=eqon.1h6v.s7.7e91612d9803 from=translated src=- shape=91e2de13 vocab=d87eb84a
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_eqOn_interpolate_Ioc {x : ℕ → X} {y : X} {p : ℕ → I} {q : I} (n : ℕ)
    (hd : StrictAnti (fun n ↦ dist (x n) y)) :
    Set.EqOn (dist_fun_compactSupport x y p q)
      (interpolate (dist (x (n + 1)) y) (dist (x n) y) (p (n + 1)) (p n))
      (Set.Ioc (dist (x (n + 1)) y) (dist (x n) y)) :=
  Set.EqOn.mono Set.Ioc_subset_Icc_self <| dist_fun_compactSupport_eqOn_interpolate_Icc n hd

/--
@isnad1 id=continuo.2h6v.s6.a2dda3025cc5 from=translated src=- shape=80e0031f vocab=691af9fe
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_continuousOn_dist_Icc {x : ℕ → X} {y : X} {p : ℕ → I} {q : I} (i : ℕ)
    (hxt : Filter.Tendsto x Filter.atTop (nhds y))
    (hd : StrictAnti (fun n ↦ dist (x n) y)) :
    ContinuousOn (dist_fun_compactSupport x y p q) (Set.Icc (dist (x i) y) (dist (x 0) y)) := by
  by_cases! hi0 : i = 0
  · simp [hi0]
  have hcc : Set.Icc (dist (x i) y) (dist (x 0) y) = Set.Icc (dist (x i) y) (dist (x (i - 1)) y) ∪
      Set.Icc (dist (x (i - 1)) y) (dist (x 0) y) := by
    symm
    refine Set.Icc_union_Icc_eq_Icc ?_ ?_
    · exact StrictAnti.antitone hd (by grind)
    · exact StrictAnti.antitone hd (Nat.zero_le _)
  rw [hcc, continuousOn_union_iff_of_isClosed]
  constructor
  · have hseo : Set.EqOn (dist_fun_compactSupport x y p q)
      (interpolate (dist (x (i - 1 + 1)) y) (dist (x (i - 1)) y) (p ((i - 1) + 1)) (p (i - 1)))
      (Set.Icc (dist (x (i - 1 + 1)) y) (dist (x (i - 1)) y)) := dist_fun_compactSupport_eqOn_interpolate_Icc (i - 1) hd
    simp [show i - 1 + 1 = i by grind] at hseo
    rw [continuousOn_congr hseo]
    exact ContinuousOn.mono (interpolate_continuousOn (dist (x i) y) (dist (x (i - 1)) y) _ _)
        (by grind)
  · exact dist_fun_compactSupport_continuousOn_dist_Icc _ hxt hd
  · exact isClosed_Icc
  · exact isClosed_Icc

/--
@isnad1 id=continuo.2h5v.s6.3c7a0e81e968 from=translated src=- shape=5d475b08 vocab=fa9499f0
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_continuousOn_zero_dist_Ioo {x : ℕ → X} {y : X} {p : ℕ → I} {q : I}
    (hxt : Filter.Tendsto x Filter.atTop (nhds y))
    (hd : StrictAnti (fun n ↦ dist (x n) y)) :
    ContinuousOn (dist_fun_compactSupport x y p q) (Set.Ioo 0 (dist (x 0) y)) := by
  have hoo : Set.Ioo 0 (dist (x 0) y) = ⋃ i, Set.Ioo (dist (x i) y) (dist (x 0) y) := by
    refine subset_antisymm ?_ ?_
    · intro a
      simp only [Set.mem_Ioo, Set.mem_iUnion, exists_and_right, and_imp]
      intro ha0 ha
      rw [tendsto_iff_dist_tendsto_zero, tendsto_order] at hxt
      apply And.right at hxt
      specialize hxt a ha0
      simp at hxt
      obtain ⟨n, hn⟩ := hxt
      specialize hn n (by rfl)
      grind
    · intro a
      simp only [Set.mem_iUnion, Set.mem_Ioo, exists_and_right, and_imp, forall_exists_index]
      intro n han ha0
      constructor
      · exact lt_of_le_of_lt dist_nonneg han
      · exact ha0
  rw [hoo, continuousOn_iUnion_iff_of_isOpen]
  · intro i
    exact ContinuousOn.mono (dist_fun_compactSupport_continuousOn_dist_Icc i hxt hd) (by grind)
  · intro i
    exact isOpen_Ioo

/--
@isnad1 id=continuo.3h5v.s7.00e3648fc60c from=translated src=- shape=b62f0d18 vocab=691af9fe
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_continuousOn_zero_dist_Icc {x : ℕ → X} {y : X} {p : ℕ → I} {q : I}
    (hxt : Filter.Tendsto x Filter.atTop (nhds y))
    (hd : StrictAnti (fun n ↦ dist (x n) y))
    (hpt : Filter.Tendsto p Filter.atTop (nhds q)) :
    ContinuousOn (dist_fun_compactSupport x y p q) (Set.Icc 0 (dist (x 0) y)) := by
  refine ContinuousOn.Icc_of_tendsto_endpoints ?_ ?_ ?_
  · exact ContinuousOn.mono (dist_fun_compactSupport_continuousOn_zero_dist_Ioo hxt hd) (by grind)
  · rw [dist_fun_compactSupport_apply_zero]
    simp only [tendsto_order, Filter.eventually_atTop, Subtype.forall, Set.mem_Icc,
      forall_and_index, gt_iff_lt] at ⊢ hpt
    constructor
    · apply And.left at hpt
      intro a ha0 ha1 haq
      specialize hpt a ha0 ha1 haq
      rw [Filter.Eventually, mem_nhdsWithin]
      obtain ⟨N, hN⟩ := hpt
      use Set.Ioo (-1) (dist (x N) y)
      constructor
      · exact isOpen_Ioo
      constructor
      · simp [ne_of_dist_strictAnti hd]
      · simp only [Set.Ioo_inter_Ioi, Left.neg_nonpos_iff, zero_le_one, sup_of_le_right]
        intro z hz
        rw [Set.mem_Ioo] at hz
        have hz1 : ¬ z ≤ -1 := by grind
        have hz01 : ¬ (-1 ≤ z ∧ z ≤ 0) := by grind
        have hn : ∃ n, dist (x (n + 1)) y < z ∧ z ≤ dist (x n) y := by
          rw [tendsto_iff_dist_tendsto_zero, tendsto_order] at hxt
          apply And.right at hxt
          specialize hxt z hz.1
          simp at hxt
          obtain ⟨m, hm⟩ := hxt
          specialize hm m (by rfl)
          have hzd0 : ¬ dist (x 0) y < z := by
            push Not
            refine le_trans (le_of_lt hz.2) ?_
            exact StrictAnti.antitone hd (Nat.zero_le N)
          have hm' : ∃ n, dist (x n) y < z := by use m
          simp only [← not_lt, and_comm]
          exact Nat.exists_not_and_succ_of_not_zero_of_exists hzd0 hm'
        have hn' := Classical.choose_spec hn
        simp [dist_fun_compactSupport, hz1, hz01, hn, interpolate_n]
        suffices N ≤ Classical.choose hn by
          refine lt_of_lt_of_le ?_ (min_le_interpolate _ _ _ _ _ (le_of_lt hn'.1) hn'.2 (hd (lt_add_one _)))
          grind
        apply And.left at hn'
        contrapose! hn'
        exact le_of_lt <| lt_of_lt_of_le hz.2 <| StrictAnti.antitone hd hn'
    · apply And.right at hpt
      intro a ha0 ha1 haq
      specialize hpt a ha0 ha1 haq
      rw [Filter.Eventually, mem_nhdsWithin]
      obtain ⟨N, hN⟩ := hpt
      use Set.Ioo (-1) (dist (x N) y)
      constructor
      · exact isOpen_Ioo
      constructor
      · simp [ne_of_dist_strictAnti hd]
      · simp only [Set.Ioo_inter_Ioi, Left.neg_nonpos_iff, zero_le_one, sup_of_le_right]
        intro z hz
        rw [Set.mem_Ioo] at hz
        have hz1 : ¬ z ≤ -1 := by grind
        have hz01 : ¬ (-1 ≤ z ∧ z ≤ 0) := by grind
        have hn : ∃ n, dist (x (n + 1)) y < z ∧ z ≤ dist (x n) y := by
          rw [tendsto_iff_dist_tendsto_zero, tendsto_order] at hxt
          apply And.right at hxt
          specialize hxt z hz.1
          simp at hxt
          obtain ⟨m, hm⟩ := hxt
          specialize hm m (by rfl)
          have hzd0 : ¬ dist (x 0) y < z := by
            push Not
            refine le_trans (le_of_lt hz.2) ?_
            exact StrictAnti.antitone hd (Nat.zero_le N)
          have hm' : ∃ n, dist (x n) y < z := by use m
          simp only [← not_lt, and_comm]
          exact Nat.exists_not_and_succ_of_not_zero_of_exists hzd0 hm'
        have hn' := Classical.choose_spec hn
        simp [dist_fun_compactSupport, hz1, hz01, hn, interpolate_n]
        suffices N ≤ Classical.choose hn by
          refine lt_of_le_of_lt (interpolate_le_max _ _ _ _ _ (le_of_lt hn'.1) hn'.2 (hd (lt_add_one _))) ?_
          grind
        apply And.left at hn'
        contrapose! hn'
        exact le_of_lt <| lt_of_lt_of_le hz.2 <| StrictAnti.antitone hd hn'
  · rw [dist_fun_compactSupport_apply_dist 0 hd]
    refine Metric.tendsto_nhdsWithin_Iio_of_tendsto_nhdsWithin_Ioc (hd zero_lt_one) ?_
    simp only
    suffices Set.EqOn (dist_fun_compactSupport x y p q)
        (interpolate (dist (x 1) y) (dist (x 0) y) (p 1) (p 0))
        (Set.Ioc (dist (x 1) y) (dist (x 0) y)) by
      rw [Set.eqOn_comm] at this
      refine Metric.tendsto_nhdsWithin_of_eqOn this ?_
      conv => arg 3; rw [← interpolate_right _ _ (p 1) (p 0) (hd zero_lt_one)]
      simp only
      refine Metric.tendsto_nhdsWithin_nhds_of_continuousOn (by simp [hd zero_lt_one]) ?_
      exact ContinuousOn.mono (interpolate_continuousOn (dist (x 1) y) (dist (x 0) y) _ _)
        (by grind)
    exact dist_fun_compactSupport_eqOn_interpolate_Ioc 0 hd

/--
@isnad1 id=continuo.1h5v.s6.5b88c655ca88 from=translated src=- shape=0a41c7fb vocab=dc38bafd
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_continuousOn_dist_dist {x : ℕ → X} {y : X} {p : ℕ → I} {q : I}
    (hd : StrictAnti (fun n ↦ dist (x n) y)) :
    ContinuousOn (dist_fun_compactSupport x y p q) (Set.Icc (dist (x 0) y) (dist (x 0) y + 1)) := by
  suffices Set.EqOn (interpolate (dist (x 0) y) (dist (x 0) y + 1) (p 0) 0)
      (dist_fun_compactSupport x y p q) (Set.Icc (dist (x 0) y) (dist (x 0) y + 1)) by
    rw [← continuousOn_congr this]
    exact interpolate_continuousOn _ _ _ _
  intro a ha
  rw [Set.mem_Icc] at ha
  have hxy0 : dist (x 0) y > 0 := by
    by_contra! hdx
    simp at hdx
    specialize hd zero_lt_one
    simp [hdx] at hd
    have hd' : dist (x 1) y ≥ 0 := dist_nonneg
    grind
  have ha1 : ¬a ≤ -1 := by grind
  have ha01 : ¬ (-1 ≤ a ∧ a ≤ 0) := by grind
  by_cases! han' : a = dist (x 0) y
  · simp [dist_fun_compactSupport, ha1, ha01, interpolate_n]
    subst han'
    split_ifs
    · rename_i hn
      suffices 0 = Classical.choose hn by
        rw [← this, interpolate_left, interpolate_right]
        · exact hd zero_lt_one
        · exact lt_add_one _
      have hn' := Classical.choose_spec hn
      apply And.right at hn'
      contrapose! hn'
      symm at hn'
      rw [← Nat.pos_iff_ne_zero] at hn'
      exact hd hn'
    · rfl
  have han : ¬∃ n, dist (x (n + 1)) y < a ∧ a ≤ dist (x n) y := by
    apply And.left at ha
    contrapose! ha
    obtain ⟨n, _, hn⟩ := ha
    by_cases hn0 : n = 0
    · subst hn0
      exact lt_of_le_of_ne hn han'
    refine lt_of_le_of_lt hn ?_
    rw [← ne_eq, ← Nat.pos_iff_ne_zero] at hn0
    exact hd hn0
  simp [dist_fun_compactSupport, ha1, ha01, han, ha]

/--
@isnad1 id=continuo.3h5v.s6.dc1fafd24c1a from=translated src=- shape=b1e1e6ea vocab=38578551
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_continuous {x : ℕ → X} {y : X} {p : ℕ → I} {q : I}
    (hxt : Filter.Tendsto x Filter.atTop (nhds y))
    (hd : StrictAnti (fun n ↦ dist (x n) y))
    (hpt : Filter.Tendsto p Filter.atTop (nhds q)) :
    Continuous (dist_fun_compactSupport x y p q) := by
  have hu : (Set.univ : Set ℝ) = Set.Iic (-1) ∪ Set.Icc (-1) 0 ∪ Set.Icc 0 (dist (x 0) y) ∪
      Set.Icc (dist (x 0) y) (dist (x 0) y + 1) ∪ Set.Ici (dist (x 0) y + 1) := by grind
  rw [← continuousOn_univ, hu, continuousOn_union_iff_of_isClosed,
    continuousOn_union_iff_of_isClosed, continuousOn_union_iff_of_isClosed,
    continuousOn_union_iff_of_isClosed]
  · constructor; constructor; constructor; constructor
    · suffices Set.EqOn (fun a ↦ 0) (dist_fun_compactSupport x y p q) (Set.Iic (-1)) by
        rw [← continuousOn_congr this]
        exact continuousOn_const
      intro a ha
      rw [Set.mem_Iic] at ha
      simp [dist_fun_compactSupport, ha]
    · suffices Set.EqOn (interpolate (-1) 0 0 q) (dist_fun_compactSupport x y p q) (Set.Icc (-1) 0) by
        rw [← continuousOn_congr this]
        exact interpolate_continuousOn _ _ _ _
      intro a ha
      rw [Set.mem_Icc] at ha
      simp [dist_fun_compactSupport, ha]
      by_cases! ha1 : a = -1
      · rw [ha1, interpolate_left] <;> norm_num
      have ha1 : ¬ a ≤ -1 := by grind
      simp [ha1]
    · exact dist_fun_compactSupport_continuousOn_zero_dist_Icc hxt hd hpt
    · exact dist_fun_compactSupport_continuousOn_dist_dist hd
    · suffices Set.EqOn (fun a ↦ 0) (dist_fun_compactSupport x y p q) (Set.Ici (dist (x 0) y + 1)) by
        rw [← continuousOn_congr this]
        exact continuousOn_const
      intro a ha
      rw [Set.mem_Ici] at ha
      have ha0 : 1 ≤ a := le_trans (by simp) ha
      have ha1 : ¬a ≤ -1 := by grind
      have ha01 : ¬ (-1 ≤ a ∧ a ≤ 0) := by grind
      have han : ¬∃ n, dist (x (n + 1)) y < a ∧ a ≤ dist (x n) y := by
        contrapose! ha
        obtain ⟨n, _, hn⟩ := ha
        refine lt_of_le_of_lt hn ?_
        refine lt_of_le_of_lt ?_ (lt_add_one _)
        exact StrictAnti.antitone hd (Nat.zero_le n)
      simp [dist_fun_compactSupport, ha1, ha01, han]
      by_cases! ha' : a = dist (x 0) y + 1
      · simp [ha']
      have ha' : ¬ a ≤ dist (x 0) y + 1 := by grind
      simp [ha']

  all_goals simp [isClosed_Iic, isClosed_Icc, isClosed_Ici]

/--
@isnad1 id=uniformc.3h5v.s6.6f53fdd6b4ec from=translated src=- shape=b1e1e6ea vocab=d347a242
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_compactSupport_uniformContinuous {x : ℕ → X} {y : X} {p : ℕ → I} {q : I}
    (hxt : Filter.Tendsto x Filter.atTop (nhds y))
    (hd : StrictAnti (fun n ↦ dist (x n) y))
    (hpt : Filter.Tendsto p Filter.atTop (nhds q)) :
    UniformContinuous (dist_fun_compactSupport x y p q) := by
  suffices Filter.Tendsto (dist_fun_compactSupport x y p q) (Filter.cocompact ℝ) (nhds 0) by
    exact (dist_fun_compactSupport_continuous hxt hd hpt).uniformContinuous_of_tendsto_cocompact this
  simp [tendsto_order]
  intro a ha0 ha1 ha0'
  constructor
  · use -1
    intro b hb1
    simp [dist_fun_compactSupport, hb1, ha0']
  · use dist (x 0) y + 1
    intro b hb
    have hb0 : 1 ≤ b := le_trans (by simp) hb
    have hb1 : ¬ b ≤ -1 := by grind
    have hb01 : ¬ (-1 ≤ b ∧ b ≤ 0) := by grind
    have hbn : ¬ ∃ n, dist (x (n + 1)) y < b ∧ b ≤ dist (x n) y := by
      contrapose! hb
      obtain ⟨n, _, hn⟩ := hb
      refine lt_of_le_of_lt hn ?_
      refine lt_of_le_of_lt ?_ (lt_add_one _)
      exact StrictAnti.antitone hd (Nat.zero_le n)
    by_cases! hbd : b = dist (x 0) y + 1
    · subst hbd
      simp [dist_fun_compactSupport, hb1, hb01, hbn, ha0']
    have hbn0 : ¬ (dist (x 0) y ≤ b ∧ b ≤ dist (x 0) y + 1) := by grind
    simp [dist_fun_compactSupport, hb1, hb01, hbn, hbn0, ha0']

/--
@isnad1 id=eq.0h6v.s6.73c5f47cc8f2 from=translated src=- shape=0c19f2c8 vocab=b67eb222
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_add_compactSupport {x : ℕ → X} {y : X} (p : ℕ → I) (q : I) (a : ℝ) :
    ((dist_fun x y p q) a).1 = (dist_fun_compactSupport x y p q) a + (correction x y (p 0) q) a := by
  simp [dist_fun]
  split_ifs
  · rename_i ha0
    by_cases ha1 : a ≤ -1
    · simp [dist_fun_compactSupport, correction, ha1]
    · simp [dist_fun_compactSupport, correction, ha1, ha0, le_of_lt (lt_of_not_ge ha1)]
  · rename_i ha0 hn
    have ha1 : ¬ a ≤ -1 := by grind
    have ha01 : ¬ (-1 ≤ a ∧ a ≤ 0) := by grind
    simp [dist_fun_compactSupport, correction, ha1, ha01, hn]
  · rename_i hn
    have ha1 : ¬ a ≤ -1 := by grind
    have ha01 : ¬ (-1 ≤ a ∧ a ≤ 0) := by grind
    simp [dist_fun_compactSupport, correction, ha1, ha01, hn]
    split_ifs
    · rw [interpolate_add _ _ _ _ _]
      · simp
      · grind
      · grind
      · exact lt_add_one _
    · simp

/--
@isnad1 id=uniformc.3h5v.s6.02ea6f887e52 from=translated src=- shape=b1e1e6ea vocab=d8781565
-/
lemma _root_.Tengoku.LeanTnorms.dist_fun_uniformContinuous {x : ℕ → X} {y : X} {p : ℕ → I} {q : I}
    (hxt : Filter.Tendsto x Filter.atTop (nhds y))
    (hd : StrictAnti (fun n ↦ dist (x n) y))
    (hpt : Filter.Tendsto p Filter.atTop (nhds q)) :
    UniformContinuous (dist_fun x y p q) := by
  let f : ℝ → I := fun a ↦ ⟨(dist_fun_compactSupport x y p q) a +
      (correction x y (p 0) q) a,
    by simp [← dist_fun_add_compactSupport p q]⟩
  rw [show dist_fun x y p q = f by ext a; rw [dist_fun_add_compactSupport]]
  refine UniformContinuous.subtype_mk ?_ _
  refine UniformContinuous.add ?_ ?_
  · exact UniformContinuous.comp uniformContinuous_subtype_val <| dist_fun_compactSupport_uniformContinuous hxt hd hpt
  · exact UniformContinuous.comp uniformContinuous_subtype_val <| correction_uniformContinuous hxt hd
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
