/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Head and prefix weight identities

Separating the head from a finite tuple reindexes a sum bijectively.
A nonempty prefix fixes the head and then takes the corresponding prefix
of the unnormalized tail row. These identities hold for arbitrary weights.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

/--
@isnad1 id=eq.0h3v.s7.b973e499b03f from=translated src=- shape=6a7149da vocab=48a675e2
-/
theorem block_sum_cons {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) :
    (∑ x, p x) = ∑ a, ∑ z : Fin t → α, p (Fin.cons a z) := by
  calc
    _ = ∑ az : α × (Fin t → α), p (Fin.cons az.1 az.2) :=
      ((Fin.consEquiv (fun _ : Fin (t + 1) => α)).sum_comp p).symm
    _ = _ := Fintype.sum_prod_type _

/--
@isnad1 id=eq.1h5v.s6.1ee800b07439 from=translated src=- shape=ade5149e vocab=8a4e4c28
-/
theorem blockPrefix_cons {α : Type*} {i t : Nat} (h : i ≤ t)
    (a : α) (z : Fin t → α) :
    blockPrefix (Nat.succ_le_succ h) (Fin.cons a z) = Fin.cons a (blockPrefix h z) := by
  funext j
  cases j using Fin.cases <;> simp [blockPrefix]

/--
@isnad1 id=eq.1h6v.s6.5b3c0c4de071 from=translated src=- shape=7f559b88 vocab=902294eb
-/
theorem blockPrefixWeight_cons {α : Type*} [Fintype α] {i t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (h : i ≤ t) (a : α) (u : Fin i → α) :
    blockPrefixWeight p (Nat.succ_le_succ h) (Fin.cons a u) =
      blockPrefixWeight (fun z : Fin t → α => p (Fin.cons a z)) h u := by
  unfold blockPrefixWeight mapWeight
  rw [block_sum_cons, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [blockPrefix_cons h, Fin.cons_inj, ite_and]

/--
@isnad1 id=eq.1h6v.s6.02c385aa3553 from=translated src=- shape=4678ddcd vocab=eb45a825
-/
theorem blockPrefixWeight_scale {α : Type*} [Fintype α] {i t : Nat}
    (p : (Fin t → α) → ℝ) (c : ℝ) (h : i ≤ t) (u : Fin i → α) :
    blockPrefixWeight (fun x => c * p x) h u = c * blockPrefixWeight p h u := by
  unfold blockPrefixWeight mapWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases same : blockPrefix h x = u <;> simp [same]

/--
@isnad1 id=eq.0h4v.s7.edc11fe8c940 from=translated src=- shape=d2ef7357 vocab=8094057c
-/
theorem mapWeight_blockHead_apply {α : Type*} [Fintype α] {t : Nat}
    (p : (Fin (t + 1) → α) → ℝ) (a : α) :
    mapWeight (fun x => x 0) p a = ∑ z : Fin t → α, p (Fin.cons a z) := by
  unfold mapWeight
  rw [block_sum_cons, Finset.sum_comm]
  simp

end Algebraic.Cutwidth.Extractor.Internal
