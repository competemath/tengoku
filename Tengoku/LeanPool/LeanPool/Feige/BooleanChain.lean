/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku

/-!
# Maximal chains in the Boolean lattice

A permutation `σ : Equiv.Perm (Fin m)` records the order in which elements
are inserted into a maximal chain.  The state at level `j` consists of the
first `j` elements in that order.  The lemmas below expose both the ranked
chain structure and the exact one-element insertion step needed by the mass
transport argument.
-/

@[expose] public section

open Finset

namespace Feige

/-- The level-`j` state of the maximal Boolean-lattice chain encoded by
`σ`.  Here `σ k` is the element inserted at step `k`. -/
def chainState {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin (m + 1)) :
    Finset (Fin m) :=
  (Finset.univ.filter fun k : Fin m ↦ k.val < j.val).map σ.toEmbedding

/--
@isnad1 id=iff.0h4v.s6.9ec80b27fa40 from=translated src=- shape=e7a0077e vocab=1e27712b
-/
@[simp]
theorem mem_chainState_iff {m : ℕ} (σ : Equiv.Perm (Fin m))
    (j : Fin (m + 1)) (i : Fin m) :
    i ∈ chainState σ j ↔ (σ.symm i).val < j.val := by
  simp [chainState]

/--
@isnad1 id=eq.0h2v.s5.a97c73fe18d1 from=translated src=- shape=88e933a0 vocab=36742008
-/
@[simp]
theorem chainState_zero {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    chainState σ 0 = ∅ := by
  ext i
  simp

/--
@isnad1 id=eq.0h2v.s4.8fdc7dccef6e from=translated src=- shape=b90060f1 vocab=722529ed
-/
@[simp]
theorem chainState_last {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    chainState σ (Fin.last m) = Finset.univ := by
  ext i
  simp [Fin.is_lt]

/--
@isnad1 id=eq.0h3v.s5.56ed956d41e3 from=translated src=- shape=153cc8ff vocab=0f8fff91
-/
@[simp]
theorem card_chainState {m : ℕ} (σ : Equiv.Perm (Fin m))
    (j : Fin (m + 1)) :
    (chainState σ j).card = j.val := by
  rw [chainState, Finset.card_map, Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt_succ j.isLt)

/-- States are monotone in their level.
@isnad1 id=le.1h4v.s6.3293f11ad219 from=translated src=- shape=f695f1bb vocab=b8733d29
-/
theorem chainState_mono {m : ℕ} (σ : Equiv.Perm (Fin m))
    {j k : Fin (m + 1)} (hjk : j ≤ k) :
    chainState σ j ⊆ chainState σ k := by
  intro i hi
  rw [mem_chainState_iff] at hi ⊢
  exact lt_of_lt_of_le hi hjk

/-- The element inserted at step `j` was not present before that step.
@isnad1 id=not.0h3v.s5.533315d0a9e5 from=translated src=- shape=5445ea30 vocab=8e0beb5f
-/
theorem perm_not_mem_chainState_castSucc {m : ℕ} (σ : Equiv.Perm (Fin m))
    (j : Fin m) :
    σ j ∉ chainState σ j.castSucc := by
  simp

/-- Passing from level `j` to level `j+1` inserts exactly `σ j`.
@isnad1 id=eq.0h3v.s5.7ef5d5f9156b from=translated src=- shape=46a69501 vocab=89dcfb55
-/
theorem chainState_succ {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    chainState σ j.succ = insert (σ j) (chainState σ j.castSucc) := by
  ext i
  simp only [mem_chainState_iff, mem_insert]
  constructor
  · intro hi
    change (σ.symm i).val < j.val + 1 at hi
    by_cases hEq : (σ.symm i).val = j.val
    · left
      apply σ.symm.injective
      exact Fin.ext (by simpa using hEq)
    · right
      change (σ.symm i).val < j.val
      omega
  · rintro (rfl | hi)
    · simp
    · change (σ.symm i).val < j.val at hi
      change (σ.symm i).val < j.val + 1
      omega

/-- Consecutive states differ by precisely the singleton containing the next
permutation element.
@isnad1 id=eq.0h3v.s6.6d82813b1040 from=translated src=- shape=c2540237 vocab=541ce5e9
-/
theorem chainState_succ_sdiff {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    chainState σ j.succ \ chainState σ j.castSucc = {σ j} := by
  rw [chainState_succ]
  ext i
  simp [perm_not_mem_chainState_castSucc σ j]

/-- Distinct levels are strictly nested.
@isnad1 id=lt.1h4v.s6.2cab52b275bf from=translated src=- shape=f695f1bb vocab=15f17d39
-/
theorem chainState_ssubset {m : ℕ} (σ : Equiv.Perm (Fin m))
    {j k : Fin (m + 1)} (hjk : j < k) :
    chainState σ j ⊂ chainState σ k := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨chainState_mono σ hjk.le, ?_⟩
  intro hEq
  have hcard := congrArg Finset.card hEq
  have hval : j.val = k.val := by
    simpa only [card_chainState] using hcard
  exact (ne_of_lt hjk) (Fin.ext hval)

end Feige
