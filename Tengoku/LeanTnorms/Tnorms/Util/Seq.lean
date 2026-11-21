/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku

/-!
TODOs:
  * General proof cleanup
  * File docstring
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
variable {X : Type*} [MetricSpace X]

private lemma notMem_of_dist_lt {a b : X} {s t : Set X} {ε : ℝ} (hab : a ≠ b)
    (hz : ∀ z : X, sInf {dist z w | w ≠ z} > 0)
    (hd : dist a b < min ε (sInf (((fun z ↦ sInf {dist z w | w ≠ z}) '' s)
    ∪ ((fun z ↦ sInf {dist z w | w ≠ z}) '' t)))) : a ∉ s := by
  contrapose! hd
  rw [min_le_iff]
  right
  trans (fun z ↦ sInf {dist z w | w ≠ z}) a
  · refine csInf_le ?_ ?_
    · rw [bddBelow_def]
      use 0
      simp
      intro r hr
      rcases hr with hr | hr
      · obtain ⟨x, _, hr⟩ := hr
        subst hr
        exact le_of_lt (hz x)
      · obtain ⟨x, _, hr⟩ := hr
        subst hr
        exact le_of_lt (hz x)
    · grind
  · refine csInf_le ?_ ?_
    · rw [bddBelow_def]
      use 0
      grind [dist_nonneg]
    · grind

private lemma choice (hd : ¬ DiscreteUniformity X) (hX : ∀ x, ¬ AccPt x (⊤ : Filter X)) :
    ∀ (ε : ℝ), ε > 0 → ∀ s t : Set X, s.Finite → t.Finite →
    ∃ a : X × X, a.1 ≠ a.2 ∧ dist a.1 a.2 < ε ∧ a.1 ∉ s ∧ a.1 ∉ t ∧ a.2 ∉ s := by
  intro ε hε s t hs ht
  simp [discreteUniformity_iff_setRelId_mem_uniformity, Metric.mem_uniformity_dist] at hd
  by_cases! hne : s = ∅ ∧ t = ∅
  · simp [hne]
    simp_rw [and_comm] at hd
    exact hd ε hε
  have hz : ∀ z : X, sInf {dist z w | w ≠ z} > 0 := by
    intro z
    specialize hX z
    simp [← Filter.principal_univ, accPt_iff_nhds, Metric.mem_nhds_iff] at hX
    obtain ⟨U, δ, hδ, hzU, hz⟩ := hX
    refine lt_of_lt_of_le hδ ?_
    refine le_csInf ?_ ?_
    · specialize hd 1 zero_lt_one
      obtain ⟨a, b, hab1, hab⟩ := hd
      by_cases! haz : a ≠ z
      · use dist z a
        grind
      · use dist z b
        grind
    simp
    intro w hwz
    contrapose! hwz
    refine hz w ?_
    apply hzU
    rw [Metric.mem_ball']
    exact hwz
  let d : X → ℝ := fun z ↦ sInf {dist z w | w ≠ z}
  specialize hd (min ε (sInf (d '' s ∪ d '' t))) ?_
  · rw [lt_min_iff]
    constructor
    · exact hε
    · rw [Set.Finite.lt_csInf_iff]
      · simp [d]
        intro r hr
        rcases hr with hr | hr
        · obtain ⟨z, _, hr⟩ := hr
          rw [← hr]
          exact hz z
        · obtain ⟨z, _, hr⟩ := hr
          rw [← hr]
          exact hz z
      · exact Set.Finite.union (Set.Finite.image _ hs) (Set.Finite.image _ ht)
      · rw [Set.union_nonempty]
        by_cases! hnes : s = ∅
        · specialize hne hnes
          right
          exact Set.Nonempty.image _ hne
        · left
          exact Set.Nonempty.image _ hnes
  obtain ⟨a, b, hd, hab⟩ := hd
  use (a, b)
  constructor
  · exact hab
  constructor
  · grind
  constructor
  · exact notMem_of_dist_lt hab hz hd
  constructor
  · rw [Set.union_comm] at hd
    exact notMem_of_dist_lt hab hz hd
  · rw [dist_comm] at hd
    push Not at hab
    exact notMem_of_dist_lt hab.symm hz hd

private noncomputable
def f (hd : ¬ DiscreteUniformity X) (hX : ∀ x, ¬ AccPt x (⊤ : Filter X)) :
  (n : ℕ) → (Fin n → X × X) := fun n ↦ match n with
  | Nat.zero => Fin.elim0
  | n + 1 => fun ⟨k, _⟩ ↦ if hkn : k < n then (f hd hX n) ⟨k, hkn⟩ else
  Classical.choose (choice hd hX (1 / (n + 1 : ℝ)) Nat.one_div_pos_of_nat
  ((fun b ↦ b.1) '' Set.range (f hd hX n)) ((fun b ↦ b.2) '' Set.range (f hd hX n))
  (Set.Finite.image _ <| Set.finite_range _) (Set.Finite.image _ <| Set.finite_range _))

private lemma f_eq_of_le (hd : ¬ DiscreteUniformity X) (hX : ∀ x, ¬ AccPt x (⊤ : Filter X))
    {n m k : ℕ} (hk : k < n) (hnm : n ≤ m) : f hd hX n ⟨k, hk⟩ = f hd hX m ⟨k, by grind⟩ := by
  by_cases! hnm' : n = m
  · subst hnm'
    rfl
  have hm0 : m ≠ 0 := by grind
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  simp at hi
  subst hi
  simp [f, show k < i by grind]
  exact f_eq_of_le hd hX hk (by grind)

private lemma f_ne (hd : ¬ DiscreteUniformity X) (hX : ∀ x, ¬ AccPt x (⊤ : Filter X))
    (n : ℕ) : (f hd hX (n + 1) ⟨n, by grind⟩).1 ≠ (f hd hX (n + 1) ⟨n, by grind⟩).2 := by
  have hf : f hd hX (n + 1) ⟨n, by grind⟩ =
      Classical.choose (choice hd hX (1 / (n + 1 : ℝ)) Nat.one_div_pos_of_nat
      ((fun b ↦ b.1) '' Set.range (f hd hX n)) ((fun b ↦ b.2) '' Set.range (f hd hX n))
      (Set.Finite.image _ <| Set.finite_range _) (Set.Finite.image _ <| Set.finite_range _)) := by
    simp [f]
  have hc := Classical.choose_spec (choice hd hX (1 / (n + 1 : ℝ)) Nat.one_div_pos_of_nat
    ((fun b ↦ b.1) '' Set.range (f hd hX n)) ((fun b ↦ b.2) '' Set.range (f hd hX n))
    (Set.Finite.image _ <| Set.finite_range _) (Set.Finite.image _ <| Set.finite_range _))
  rw [hf]
  exact hc.1

/--
@isnad1 id=ex.2h1v.s7.6eb94e1a4fee from=translated src=- shape=6025561b vocab=02bd3fe9
-/
lemma _root_.Tengoku.LeanTnorms.exists_inj_djsoint_seqs_dist_tendsto_zero (hd : ¬ DiscreteUniformity X)
    (hX : ∀ x, ¬ AccPt x (⊤ : Filter X)) :
    ∃ x y : ℕ → X, Filter.Tendsto (fun n ↦ dist (x n) (y n)) Filter.atTop (nhds 0) ∧
    (Disjoint (Set.range x) (Set.range y)) ∧ Function.Injective x := by
  use (fun n ↦ (f hd hX (n + 1) ⟨n, by grind⟩).1), (fun n ↦ (f hd hX (n + 1) ⟨n, by grind⟩).2)
  constructor
  · simp [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    use N
    intro n hn
    have hnN : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := Nat.one_div_le_one_div hn
    have hf : f hd hX (n + 1) ⟨n, by grind⟩ =
        Classical.choose (choice hd hX (1 / (n + 1 : ℝ)) Nat.one_div_pos_of_nat
        ((fun b ↦ b.1) '' Set.range (f hd hX n)) ((fun b ↦ b.2) '' Set.range (f hd hX n))
        (Set.Finite.image _ <| Set.finite_range _) (Set.Finite.image _ <| Set.finite_range _)) := by
      simp [f]
    have hc := Classical.choose_spec (choice hd hX (1 / (n + 1 : ℝ)) Nat.one_div_pos_of_nat
      ((fun b ↦ b.1) '' Set.range (f hd hX n)) ((fun b ↦ b.2) '' Set.range (f hd hX n))
      (Set.Finite.image _ <| Set.finite_range _) (Set.Finite.image _ <| Set.finite_range _))
    apply And.right at hc; apply And.left at hc
    grind
  constructor
  · rw [Set.disjoint_range_iff]
    intro n m
    by_cases! hnm' : n = m
    · subst hnm'
      exact f_ne hd hX _
    by_cases! hnm : n < m
    · have hc := Classical.choose_spec (choice hd hX (1 / (m + 1 : ℝ)) Nat.one_div_pos_of_nat
        ((fun b ↦ b.1) '' Set.range (f hd hX m)) ((fun b ↦ b.2) '' Set.range (f hd hX m))
        (Set.Finite.image _ <| Set.finite_range _) (Set.Finite.image _ <| Set.finite_range _))
      repeat apply And.right at hc
      contrapose! hc
      conv at hc => rhs; simp [f]
      rw [f_eq_of_le hd hX _ hnm] at hc
      simp
      use ⟨n, by grind⟩
    · have hnm : m < n := by grind
      have hc := Classical.choose_spec (choice hd hX (1 / (n + 1 : ℝ)) Nat.one_div_pos_of_nat
        ((fun b ↦ b.1) '' Set.range (f hd hX n)) ((fun b ↦ b.2) '' Set.range (f hd hX n))
        (Set.Finite.image _ <| Set.finite_range _) (Set.Finite.image _ <| Set.finite_range _))
      apply And.right at hc; apply And.right at hc; apply And.right at hc; apply And.left at hc
      contrapose! hc
      conv at hc => lhs; simp [f]
      rw [f_eq_of_le hd hX _ hnm] at hc
      simp
      symm at hc
      use ⟨m, by grind⟩
  · intro n m hnm
    contrapose! hnm
    wlog hnm' : n < m generalizing n m
    · symm at hnm ⊢
      exact this hnm (by grind)
    have hf : f hd hX (n + 1) ⟨n, by grind⟩ = f hd hX (m + 1) ⟨n, by grind⟩ := by
      conv => rhs; simp [f, hnm']
      exact f_eq_of_le hd hX _ hnm'
    rw [hf]
    simp [f, hnm']
    have hc := Classical.choose_spec (choice hd hX (1 / (m + 1 : ℝ)) Nat.one_div_pos_of_nat
      ((fun b ↦ b.1) '' Set.range (f hd hX m)) ((fun b ↦ b.2) '' Set.range (f hd hX m))
      (Set.Finite.image _ <| Set.finite_range _) (Set.Finite.image _ <| Set.finite_range _))
    apply And.right at hc; apply And.right at hc; apply And.left at hc
    contrapose! hc
    simp
    use ⟨n, by grind⟩
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
