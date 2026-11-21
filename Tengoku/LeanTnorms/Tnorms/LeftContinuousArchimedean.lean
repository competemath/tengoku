/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku
import Tengoku.LeanTnorms.Tnorms.Util.Mathlib
import Tengoku.LeanTnorms.Tnorms.Basic.ContinuousMul
import Tengoku.LeanTnorms.Tnorms.Basic.Algebra

/-!
TODOs:
  * General proof cleanup
  * File docstring
  * Weaken typeclass assumptions?
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
local infixl:60 " ⇒ " => LImp

variable {M : Type*} [TopologicalSpace M]

section OrderClosedTopology

variable [PartialOrder M] [OrderClosedTopology M]

lemma _root_.Tengoku.LeanTnorms.eq_one_of_antitone_of_tendsto_one [One M] [IsTopOneClass M] {x : ℕ → M} (hax : Antitone x)
    (h : Filter.Tendsto x Filter.atTop (nhds 1)) : x = 1 := by
  ext n
  rw [Pi.one_apply]
  exact le_antisymm le_one <| Antitone.le_of_tendsto hax h n

theorem _root_.Tengoku.LeanTnorms.mul_tendsto_of_tendsto_one [MulOneClass M] [IsTopOneClass M] {q : M} {x y : ℕ → M}
    (hax : Antitone x) (hxt : Filter.Tendsto x Filter.atTop (nhds 1))
    (hyt : Filter.Tendsto y Filter.atTop (nhds q)) :
    Filter.Tendsto (x * y) Filter.atTop (nhds q) := by
  simp_rw [eq_one_of_antitone_of_tendsto_one hax hxt, one_mul, hyt]

theorem _root_.Tengoku.LeanTnorms.mul_tendsto_of_tendsto_one' [MulOneClass M] [IsTopOneClass M] {q : M} {x y : ℕ → M}
    (hax : Antitone x) (hxt : Filter.Tendsto x Filter.atTop (nhds 1))
    (hyt : Filter.Tendsto y Filter.atTop (nhds q)) :
    Filter.Tendsto (y * x) Filter.atTop (nhds q) := by
  simp_rw [eq_one_of_antitone_of_tendsto_one hax hxt, mul_one, hyt]

end OrderClosedTopology

section OrderTopology

variable [Preorder M] [OrderTopology M]

theorem _root_.Tengoku.LeanTnorms.mul_tendsto_zero_of_tendsto_zero [MulZeroOneClass M] [MulLeftMono M] [IsTopOneClass M]
    {x y : ℕ → M} (hxt : Filter.Tendsto x Filter.atTop (nhds 0)) :
    Filter.Tendsto (x * y) Filter.atTop (nhds 0) := by
  simp only [tendsto_order, not_lt_zero, Filter.eventually_atTop, IsEmpty.forall_iff, implies_true,
    gt_iff_lt, true_and] at hxt ⊢
  intro a ha
  obtain ⟨n, hn⟩ := hxt a ha
  use n
  intro m hnm
  exact lt_of_le_of_lt (mul_le_left _ _) <| hn m hnm

theorem _root_.Tengoku.LeanTnorms.mul_tendsto_zero_of_tendsto_zero' [MulZeroOneClass M] [MulRightMono M] [IsTopOneClass M]
    {x y : ℕ → M} (hxt : Filter.Tendsto x Filter.atTop (nhds 0)) :
    Filter.Tendsto (y * x) Filter.atTop (nhds 0) := by
  simp only [tendsto_order, not_lt_zero, Filter.eventually_atTop, IsEmpty.forall_iff, implies_true,
    gt_iff_lt, true_and] at hxt ⊢
  intro a ha
  obtain ⟨n, hn⟩ := hxt a ha
  use n
  intro m hnm
  exact lt_of_le_of_lt (mul_le_right _ _) <| hn m hnm

end OrderTopology

section PartialOrder

omit [TopologicalSpace M]

variable [MonoidWithZero M] [PartialOrder M] [IsTopOneClass M]

lemma _root_.Tengoku.LeanTnorms.nonempty_pow_gt (p q : M) (hq : q ≠ 1) : {n | p ^ n > q}.Nonempty := by
  use 0
  simp [lt_one_iff_ne_one, hq]

lemma _root_.Tengoku.LeanTnorms.bddAbove_pow_gt [MulLeftMono M] [MulArchimedeanDualWithZero M]
    (p q : M) (hp : p ≠ 1) (hq : q ≠ 0) : BddAbove {n | p ^ n > q} := by
  obtain ⟨n, hn⟩ := MulArchimedeanDualWithZero.arch hq.pos hp.lt_one
  rw [bddAbove_def]
  use n
  simp only [gt_iff_lt, Set.mem_ofPred_eq]
  intro k hk
  by_contra! hnk
  have hpnk : p ^ k ≤ p ^ n := pow_le_pow_right_of_le_one' le_one (le_of_lt hnk)
  order

lemma _root_.Tengoku.LeanTnorms.pow_sSup_gt_gt [MulLeftMono M] [MulArchimedeanDualWithZero M]
    {p : M} (hp : IsNontrivial p) {z : ℕ → M} (m : ℕ) (hz : ∀ n, z n ≠ 1) :
    (z m) ^ (sSup {n | (z m) ^ n > p}) > p := by
  suffices (sSup {n | (z m) ^ n > p}) ∈ {n | (z m) ^ n > p} by simp_all
  exact Nat.sSup_mem (nonempty_pow_gt _ _ hp.2) (bddAbove_pow_gt _ _ (hz m) hp.1)

lemma _root_.Tengoku.LeanTnorms.pow_sSup_gt_not_gt [MulLeftMono M] [MulArchimedeanDualWithZero M]
    {p : M} (hp0 : p ≠ 0) {z : ℕ → M} (m : ℕ) (hz : ∀ n, z n ≠ 1) :
    ¬ (z m) ^ (sSup {n | (z m) ^ n > p} + 1) > p := by
  suffices (sSup {n | (z m) ^ n > p}) + 1 ∉ {n | (z m) ^ n > p} by simp_all
  exact notMem_of_csSup_lt (lt_add_one (sSup {n | (z m) ^ n > p})) (bddAbove_pow_gt _ _ (hz m) hp0)

private noncomputable
def φ {P : ℕ → ℕ → Prop} (hn : ∀ n, ∃ m > n, P m n) : ℕ → ℕ
    | Nat.zero => 0
    | n + 1 => Classical.choose (hn (φ hn n))

lemma _root_.Tengoku.LeanTnorms.phi_strictMono {P : ℕ → ℕ → Prop} (hn : ∀ n, ∃ m > n, P m n) : StrictMono (φ hn) := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  exact (Classical.choose_spec (hn (φ hn n))).1

variable [TopologicalSpace M] [OrderTopology M]

lemma _root_.Tengoku.LeanTnorms.exists_next {x : ℕ → M} (hx : Filter.Tendsto x Filter.atTop (nhds 1)) (hx1 : ∀ n, x n ≠ 1)
    (n : ℕ) : ∃ m > n, x n ≤ x m := by
  contrapose! hx
  simp only [tendsto_order, Filter.eventually_atTop, gt_iff_lt, not_one_lt, IsEmpty.forall_iff,
    implies_true, and_true, not_forall, not_exists]
  use x n
  constructor
  · intro m
    use max m (n + 1), le_max_left m (n + 1)
    specialize hx (max m (n + 1)) (by grind)
    order
  · simp [hx1 n, lt_one_iff_ne_one]

lemma _root_.Tengoku.LeanTnorms.mono_of_tendsto_one {x : ℕ → M}
    (hx : Filter.Tendsto x Filter.atTop (nhds 1)) (hx1 : ∀ n, x n ≠ 1) :
    ∃ a : ℕ → M, Monotone a ∧ (∀ n : ℕ, ∃ m, a n ≤ x m) ∧
    Filter.Tendsto a Filter.atTop (nhds 1) := by
  use x ∘ (φ (exists_next hx hx1))
  constructorm* _ ∧ _
  · refine monotone_nat_of_le_succ ?_
    intro n
    exact (Classical.choose_spec ((exists_next hx hx1) (φ (exists_next hx hx1) n))).2
  · intro n
    use φ (exists_next hx hx1) (n + 1)
    exact (Classical.choose_spec ((exists_next hx hx1) (φ (exists_next hx hx1) n))).2
  · exact Filter.Tendsto.comp hx <| (phi_strictMono (exists_next hx hx1)).tendsto_atTop

end PartialOrder

theorem _root_.Tengoku.LeanTnorms.rightCont_of_leftCont_arch (M : Type*) [CompleteLinearOrder M]
    [TopologicalSpace M]
    [MonoidWithZero M] [MulLeftMono M] [MulRightMono M] [IsTopOneClass M]
    [OrderTopology M]
    -- [OrderClosedTopology M] [InfConvergenceClass M]
    [LeftContinuousMul M] [MulArchimedeanDualWithZero M]
    -- this condition also arose in ContinuousAlgebra when proving that NoZeroDivisors => Strict
    (f : ℕ → M) (h1 : Filter.Tendsto f Filter.atTop (nhds 1)) (hf1 : ∀ n, f n ≠ 1) :
    RightContinuousMul M := by
  refine RightContinuousMul.mk ?_
  nontriviality M
  intro x y p q hax hay hx hy
  by_cases! hp0 : p = 0
  · subst hp0
    rw [zero_mul]
    exact mul_tendsto_zero_of_tendsto_zero hx
  by_cases! hp1 : p = 1
  · subst hp1
    rw [one_mul]
    exact mul_tendsto_of_tendsto_one hax hx hy
  by_cases! hq0 : q = 0
  · subst hq0
    rw [mul_zero]
    exact mul_tendsto_zero_of_tendsto_zero' hy
  by_cases! hq1 : q = 1
  · subst hq1
    rw [mul_one]
    exact mul_tendsto_of_tendsto_one' hay hy hx
  by_contra! h
  obtain ⟨z, hmz, hz1, hz⟩ := mono_of_tendsto_one h1 hf1
  have hz1 : ∀ n, z n ≠ 1 := by
    simp_rw [← lt_one_iff_ne_one] at hf1 ⊢
    intro n
    obtain ⟨m, hm⟩ := hz1 n
    exact lt_of_le_of_lt hm (hf1 m)
  let u : ℕ → ℕ := fun n ↦ sSup {m | (z n) ^ m > p}
  let v : ℕ → ℕ := fun n ↦ sSup {m | (z n) ^ m > q}
  let a := ⨅ n, (x n) * (y n)
  have haz : ∀ n, a * (z n) ^ 2 ≤ (z n) ^ (u n + v n + 2) := by
    intro n
    rw [pow_add, pow_add]
    refine mul_le_mul_left ?_ _
    have ha := tendsto_atTop_iInf (Antitone.mul' hax hay)
    simp only [tendsto_order, Filter.eventually_atTop, gt_iff_lt] at hx hy
    obtain ⟨i, hi⟩ := hx.2 (z n ^ u n) (pow_sSup_gt_gt ⟨hp0, hp1⟩ n hz1)
    obtain ⟨j, hj⟩ := hy.2 (z n ^ v n) (pow_sSup_gt_gt ⟨hq0, hq1⟩ n hz1)
    specialize hi (i ⊔ j) (by grind)
    specialize hj (i ⊔ j) (by grind)
    refine le_trans (iInf_le _ (i ⊔ j)) ?_
    exact mul_le_mul' (le_of_lt hi) (le_of_lt hj)
  have hapq : p * q < a := by
    refine lt_of_le_of_ne ?_ ?_
    · rw [le_iInf_iff]
      intro i
      exact mul_le_mul' (Antitone.le_of_tendsto hax hx i) (Antitone.le_of_tendsto hay hy i)
    · contrapose! h
      rw [h]
      exact tendsto_atTop_iInf (Antitone.mul' hax hay)
  have hz2 : Monotone (fun n ↦ (z n) ^ 2) := by
    simp_rw [pow_two]
    exact Monotone.mul' hmz hmz
  have haz2 : Filter.Tendsto (fun n ↦ a * (z n) ^ 2) Filter.atTop (nhds a) := by
    nth_rw 2 [← mul_one a]
    refine monotone_continuous_mul _ (fun n ↦ a) (fun n ↦ (z n) ^ 2) a 1 monotone_const hz2
      tendsto_const_nhds ?_
    simp_rw [pow_two]
    rw [show (1 : M) = 1 * 1 by norm_num]
    exact monotone_continuous_mul _ z z 1 1 hmz hmz hz hz
  have hn : ∃ n, p * q < a * (z n) ^ 2 := by
    simp only [tendsto_order, Filter.eventually_atTop, gt_iff_lt] at haz2
    apply And.left at haz2
    obtain ⟨m, hm⟩ := haz2 (p * q) hapq
    specialize hm m (by rfl)
    use m
  have hzpq : ∀ n, ¬ (z n) ^ (u n + v n + 2) > p * q := by
    intro n
    rw [show u n + v n + 2 = (u n + 1) + (v n + 1) by ring, pow_add]
    have hp0z := pow_sSup_gt_not_gt hp0 (z := z) n hz1
    have hq0z := pow_sSup_gt_not_gt hq0 (z := z) n hz1
    rw [gt_iff_lt, not_lt] at hp0z hq0z ⊢
    exact mul_le_mul' hp0z hq0z
  grind
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
