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

lemma Icc_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
  {(-(n+1) : ℤ), (n + 1 : ℤ)} := by
  ext a
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Icc, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  omega

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

lemma int_add_abs_self_nonneg (n : ℤ) : 0 ≤ n + |n| := by
  rcases abs_cases n with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

lemma verga : Tendsto (fun N : ℕ => Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  intro x
  refine ⟨x.natAbs + 1, ?_⟩
  simp only [Nat.cast_add, Int.natCast_natAbs, Nat.cast_one, neg_add_rev, Int.reduceNeg,
    Finset.mem_Ico, add_neg_le_iff_le_add]
  exact ⟨le_trans (by omega) (int_add_abs_self_nonneg x), Int.lt_add_one_iff.mpr (le_abs_self x)⟩
