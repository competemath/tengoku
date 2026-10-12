/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2015, Problem 6
The sequence $a_1, a_2, \dots$ of integers satisfies the conditions
1. $1 ≤ a_j ≤ 2015$ for all $j ≥ 1$,
2. $k + a_k ≠ l + a_l$ for all $1 ≤ k < l$.
Prove that there exist two positive integers $b$ and $N$ for which
$$\left|\sum_{j=m+1}^n (a_j-b)\right| ≤ 1007^2$$
for all integers $m,n$ such that $N ≤ m < n$.
-/

/-- The conditions on `a` in the problem. We reindex `a` to start from 0 rather than 1;
`N` then only has to be nonnegative rather than positive, and the sum in the problem statement
is over `Ico m n` rather than `Ioc m n`. -/
def Condition (a : ℕ → ℤ) : Prop :=
  (∀ i, a i ∈ Finset.Icc 1 2015) ∧ Function.Injective fun i ↦ i + a i

/-
# Solution
We follow solution 2 ("juggling") from https://web.evanchen.cc/exams/IMO-2015-notes.pdf.
Consider a collection of balls at different integer heights that starts out empty at time 0
and is modified at each succeeding integer time `t` as follows:
* If there is a ball at height 0 it is removed (caught)
* Then a ball is added at height $a_t$
* Then all balls have their height decreased by 1
Condition 1 ensures that all heights stay in [0, 2014]. Condition 2 ensures that the heights at any
point in time are distinct, so we can model the collection as a finset of heights of monotonically
increasing, bounded cardinality. So there is a time where the cardinality reaches a maximum;
we take `N` to be that time and `b` to be that maximum cardinality. $1 ≤ b ≤ 2015$.
Let $S_t$ be the sum of heights at time $t$. The key observation is that for all $t ≥ N$
$$S_{t+1} = S_t + a_{t+1} - b$$
because 0 must be in the set of heights at time $t$ (otherwise the cardinality will increase);
this height is replaced by $a_{t+1}$ and then all $b$ balls have their height decreased by 1. Thus
$$\left|\sum_{j=m+1}^n (a_j-b)\right| = |S_n - S_m|.$$
Now for all $t ≥ N$,
$$\sum_{i=0}^{b-1} i ≤ S_t ≤ 0 + \sum_{i=0}^{b-2} (2014-i),$$
so the absolute difference is upper-bounded by
$$\sum_{i=0}^{b-2} (2014-i) - (b-1) - \sum_{i=0}^{b-2} (b-2-i) = (b-1)(2015-b) ≤ 1007^2.$$
-/

/-- The collection of ball heights in the solution. -/
def pool (a : ℕ → ℤ) : ℕ → Finset ℤ
  | 0 => ∅
  | t + 1 => (insert (a t) ((pool a t).erase 0)).map (Equiv.subRight (1 : ℤ))

variable {a : ℕ → ℤ} (ha : Condition a) {t : ℕ}

section Pool

/--
@isnad1 id=ex.1h3v.s5.262f2836c85c from=translated src=- shape=fe50b06c vocab=66f4376e
-/
lemma exists_add_eq_of_mem_pool {z : ℤ} (hz : z ∈ pool a t) : ∃ u < t, u + a u = t + z := by
  induction t generalizing z with
  | zero => simp only [pool, Finset.notMem_empty] at hz
  | succ t ih =>
    simp_rw [pool, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.subRight_apply] at hz
    obtain ⟨y, my, ey⟩ := hz
    rw [Finset.mem_insert, Finset.mem_erase] at my; rcases my with h | h
    · use t; lia
    · obtain ⟨u, lu, hu⟩ := ih h.2
      use u; lia

include ha

/-- The ball heights are always within `[0, 2014]`.
@isnad1 id=le.1h2v.s5.d1dfe200959c from=translated src=- shape=9ce8644e vocab=4082c05b
-/
lemma pool_subset_Icc : pool a t ⊆ Finset.Icc 0 2014 := by
  induction t with
  | zero => simp only [pool, Finset.empty_subset]
  | succ t ih =>
    intro x hx
    simp_rw [pool, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.subRight_apply] at hx
    obtain ⟨y, my, ey⟩ := hx
    suffices y ∈ Finset.Icc 1 2015 by rw [Finset.mem_Icc] at this ⊢; lia
    rw [Finset.mem_insert, Finset.mem_erase] at my; rcases my with h | ⟨h₁, h₂⟩
    · exact h ▸ ha.1 t
    · replace h₂ := ih h₂
      rw [Finset.mem_Icc] at h₂ ⊢; lia

/--
@isnad1 id=not.1h2v.s4.6e1405e5fe6d from=translated src=- shape=b4d8e82f vocab=33b36d83
-/
lemma not_mem_pool_self : a t ∉ pool a t := by
  by_contra h
  obtain ⟨u, lu, hu⟩ := exists_add_eq_of_mem_pool h
  exact lu.ne (ha.2 hu)

/-- The number of balls stays unchanged if there is a ball with height 0 and increases by 1
otherwise.
@isnad1 id=eq.1h2v.s6.3cc558f791ea from=translated src=- shape=da55181b vocab=bdec6514
-/
lemma card_pool : Finset.card (pool a (t + 1)) = Finset.card (pool a t) + if 0 ∈ pool a t then 0 else 1 := by
  have nms : a t ∉ (pool a t).erase 0 := by
    rw [Finset.mem_erase, not_and_or]; exact .inr (not_mem_pool_self ha)
  rw [pool, Finset.card_map, Finset.card_insert_of_notMem nms, Finset.card_erase_eq_ite]
  split_ifs with h
  · have := Finset.card_pos.mpr ⟨0, h⟩; lia
  · rfl

/--
@isnad1 id=monotone.1h1v.s4.1a7644b1b9c6 from=translated src=- shape=bee90935 vocab=b3078fe4
-/
lemma monotone_card_pool : Monotone fun t ↦ Finset.card (pool a t) := by
  refine monotone_nat_of_le_succ fun t ↦ ?_
  have := card_pool (t := t) ha; lia

/-- There exists a point where the number of balls reaches a maximum (which follows from its
monotonicity and boundedness). We take its coordinates for the problem's `b` and `N`.
@isnad1 id=ex.1h1v.s4.2652917e0c8d from=translated src=- shape=73b863f4 vocab=f2f3f7eb
-/
lemma exists_max_card_pool : ∃ b N, ∀ t ≥ N, Finset.card (pool a t) = b :=
  converges_of_monotone_of_bounded (monotone_card_pool ha)
    (fun t ↦ by simpa using Finset.card_le_card (pool_subset_Icc ha))

end Pool

section Sums

variable {b N : ℕ} (hbN : ∀ t ≥ N, Finset.card (pool a t) = b) (ht : t ≥ N)

include ha hbN

/--
@isnad1 id=lt.2h3v.s5.66e20de4759f from=translated src=- shape=dd1ef3e9 vocab=2a364f27
-/
lemma b_pos : 0 < b := by
  by_contra! h; rw [nonpos_iff_eq_zero] at h; subst h
  replace hbN : ∀ t, Finset.card (pool a t) = 0 := fun t ↦ by
    obtain h | h := le_or_gt t N
    · have : Finset.card (pool a t) ≤ Finset.card (pool a N) := monotone_card_pool ha h
      rwa [hbN _ le_rfl, nonpos_iff_eq_zero] at this
    · exact hbN _ h.le
  have cp1 : Finset.card (pool a 1) = 1 := by
    simp_rw [card_pool ha, pool, Finset.card_empty, Finset.notMem_empty, ite_false]
  apply absurd (hbN 1); lia

include ht in
/--
@isnad1 id=mem.3h4v.s5.f76d5a7e5484 from=translated src=- shape=8c18ddf3 vocab=9c15a20b
-/
lemma zero_mem_pool : 0 ∈ pool a t := by
  have := card_pool (t := t) ha
  have := hbN (t + 1) (by lia)
  simp_all

include ht in
/-- The key observation, one term of the telescoping sum for the problem's expression.
@isnad1 id=eq.3h4v.s6.c8d46d208563 from=translated src=- shape=0d6a33d2 vocab=38530d84
-/
lemma sum_sub_sum_eq_sub : ∑ x ∈ pool a (t + 1), x - ∑ x ∈ pool a t, x = a t - b := by
  simp_rw [pool, Finset.sum_map, Equiv.coe_toEmbedding, Equiv.subRight_apply]
  have nms : a t ∉ (pool a t).erase 0 := by
    rw [Finset.mem_erase, not_and_or]; exact .inr (not_mem_pool_self ha)
  rw [Finset.sum_insert nms, Finset.sum_erase_eq_sub (h := zero_mem_pool ha hbN ht), Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_one, hbN _ ht]
  lia

/-- The telescoping sum giving the part of the problem's expression within the modulus signs.
@isnad1 id=eq.4h5v.s6.fcbdca17087a from=translated src=- shape=48644bc1 vocab=0c37aaeb
-/
lemma sum_telescope {m n : ℕ} (hm : N ≤ m) (hn : m < n) :
    ∑ j ∈ Finset.Ico m n, (a j - b) = ∑ x ∈ pool a n, x - ∑ x ∈ pool a m, x := by
  induction n, hn using Nat.le_induction with
  | base => rw [sum_sub_sum_eq_sub ha hbN hm]; simp
  | succ k lk ih =>
    rw [Finset.sum_Ico_succ_top (by lia), ih, ← sum_sub_sum_eq_sub ha hbN (by lia)]
    apply sub_add_sub_cancel'

include ht in
/--
@isnad1 id=le.3h4v.s5.a0099299b638 from=translated src=- shape=9a0e3e1d vocab=337db6f9
-/
lemma le_sum_pool : ∑ i ∈ Finset.range b, (i : ℤ) ≤ ∑ x ∈ pool a t, x := by
  convert Finset.sum_range_le_sum fun x mx ↦ (Finset.mem_Icc.mp ((pool_subset_Icc ha) mx)).1
  · rw [hbN _ ht]
  · rw [zero_add]

include ht in
/--
@isnad1 id=le.3h4v.s6.870f2d6a4b1b from=translated src=- shape=d9452ef3 vocab=a6d38b5d
-/
lemma sum_pool_le : ∑ x ∈ pool a t, x ≤ ∑ i ∈ Finset.range (b - 1), (2014 - i : ℤ) := by
  have zmp := zero_mem_pool ha hbN ht
  rw [← Finset.insert_erase zmp, Finset.sum_insert (Finset.notMem_erase _ _), zero_add]
  convert Finset.sum_le_sum_range fun x mx ↦ ?_
  · rw [Finset.card_erase_of_mem zmp, hbN _ ht]
  · exact (Finset.mem_Icc.mp ((pool_subset_Icc ha) (Finset.mem_erase.mp mx).2)).2

end Sums

namespace Imo2015P6

end Imo2015P6
