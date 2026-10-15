/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku
meta import Lean.Meta.Tactic.NormCast

/-! # IccIcoLems -/

@[expose] public section

open TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

/--
@isnad1 id=eq.0h1v.s7.94e9e1c7c8f4 from=translated src=- shape=48021f9f vocab=f4d8f7f2
-/
lemma Icc_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
  {(-(n+1) : ℤ), (n + 1 : ℤ)} := by
  ext a
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Icc, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  omega

/--
@isnad1 id=eq.1h2v.s7.dc3f6ce12561 from=translated src=- shape=e1ce1016 vocab=6b5b95b8
-/
lemma trex (f : ℤ → ℂ) (N : ℕ) (hn : 1 ≤ N) : ∑ m ∈ Finset.Icc (-N : ℤ) N, f m =
  f N + f (-N : ℤ) + ∑ m ∈ Finset.Icc (-(N - 1) : ℤ) (N - 1), f m := by
  induction N with
  | zero => aesop
  | succ N ih =>
    zify
    rw [Icc_succ, Finset.sum_union]
    · ring_nf
      rw [add_assoc]
      congr
      rw [Finset.sum_pair]
      · ring
      omega
    simp

/--
@isnad1 id=le.0h1v.s4.434366f73ae9 from=translated src=- shape=dfa3a8eb vocab=fe33c17a
-/
lemma int_add_abs_self_nonneg (n : ℤ) : 0 ≤ n + |n| := by
  rcases abs_cases n with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/--
@isnad1 id=tendsto.0h0v.s5.3e94b0268978 from=translated src=- shape=84087be5 vocab=638dc90a
-/
lemma verga : Tendsto (fun N : ℕ => Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  intro x
  refine ⟨x.natAbs + 1, ?_⟩
  simp only [Nat.cast_add, Int.natCast_natAbs, Nat.cast_one, neg_add_rev, Int.reduceNeg,
    Finset.mem_Ico, add_neg_le_iff_le_add]
  exact ⟨le_trans (by omega) (int_add_abs_self_nonneg x), Int.lt_add_one_iff.mpr (le_abs_self x)⟩
