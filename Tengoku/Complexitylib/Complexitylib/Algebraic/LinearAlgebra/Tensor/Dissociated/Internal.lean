/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Dissociated.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LinearAlgebra.Tensor.Periodic
public import Tengoku

/-!
# Uniform periodic tensor estimates

The checked paired-cluster lower bound supplies the rank estimate; a finite search
chooses all parameters uniformly while keeping every coefficient's binary length linear.
-/

@[expose] public section

namespace Algebraic.Tensor3.Dissociated.Internal

open Finset Filter

/-- Every fixed positive order eventually passes all finite checks. -/
theorem eventually_admissible {p : ℕ} (hp : 1 ≤ p) : ∀ᶠ k in atTop, Admissible k p := by
  filter_upwards [eventually_ge_atTop (blockLength p),
    eventually_ge_atTop (2 ^ p),
    eventually_ge_atTop (2 ^ (rowPeriod p * columnPeriod p)),
    eventually_ge_atTop ((p + 1) * (16 * (p + 1) * blockLength p + 2))]
    with k hL hpLog hperiod hcost
  exact ⟨hp, Nat.le_log_of_pow_le (by decide) (by lia), hL,
    Nat.le_log_of_pow_le (by decide) (by lia), by lia⟩

/-- An admissible order is present in the actual bounded search. -/
theorem mem_candidates {k p : ℕ} (hp : Admissible k p) : p ∈ candidates k := by
  exact mem_filter.mpr ⟨mem_range.mpr (by have := hp.2.1; lia), hp⟩

/-- The chosen order is at least any admissible order. -/
theorem le_order {k p : ℕ} (hp : Admissible k p) : p ≤ order k :=
  Finset.le_sup (f := id) (mem_candidates hp)

/-- If any order is admissible, the maximal selected order is admissible. -/
theorem admissible_order {k p : ℕ} (hp : Admissible k p) : Admissible k (order k) := by
  have h := Finset.sup_mem_of_nonempty (f := id) ⟨p, mem_candidates hp⟩
  obtain ⟨q, hq, heq⟩ := h
  have hq := (mem_filter.mp hq).2
  exact (show q = order k from heq) ▸ hq

/-- The selected orders tend to infinity; the tensor does not depend on epsilon. -/
theorem eventually_le_order (p : ℕ) : ∀ᶠ k in atTop, p ≤ order k := by
  filter_upwards [eventually_admissible (p := max p 1) (by lia)] with k hk
  exact (le_max_left p 1).trans (le_order hk)

/-- The selected order always lies in the logarithmic search range. -/
theorem order_le_log (k : ℕ) : order k ≤ Nat.log 2 (2 * k + 1) := by
  apply Finset.sup_le
  intro p hp
  exact (mem_filter.mp hp).2.2.1

/-- Above the cutoff the tensor is exactly an existing periodic tensor. -/
theorem oddTensor_eq {k : ℕ} (hk : Admissible k (order k)) :
    oddTensor k = periodicLMTensor k (rowPeriod (order k)) (columnPeriod (order k)) := by
  funext a j l
  simp only [oddTensor, oddEntry, hk, ↓reduceIte, periodicLMTensor, lmTensor, weightedShifts]
  split_ifs <;> simp [periodicWeight]

/-- Every integer coefficient has at most the dimension plus one binary digits. -/
theorem oddEntry_size_le (k a j l : ℕ) : (oddEntry k a j l).size ≤ 2 * k + 2 := by
  unfold oddEntry
  split_ifs with hk hsupport
  · rw [Nat.size_pow]
    have hrow := Nat.mod_lt a
      (show 0 < rowPeriod (order k) by unfold rowPeriod; lia)
    have hcolumn := Nat.mod_lt j
      (show 0 < columnPeriod (order k) by unfold columnPeriod; lia)
    have hcode : a % rowPeriod (order k) * columnPeriod (order k) +
        j % columnPeriod (order k) < rowPeriod (order k) * columnPeriod (order k) := by
      nlinarith [Nat.mul_le_mul_right (columnPeriod (order k)) hrow]
    have hpow : 2 ^ (a % rowPeriod (order k) * columnPeriod (order k) +
        j % columnPeriod (order k)) ≤ 2 * k + 1 :=
      Nat.pow_le_of_le_log (by lia) (hcode.le.trans hk.2.2.2.1)
    lia
  all_goals simp

/-- The padded core loses at most one dimension. -/
theorem core_bounds {m : ℕ} (hm : 0 < m) :
    2 * coreIndex m + 1 ≤ m ∧ m ≤ 2 * coreIndex m + 2 := by
  unfold coreIndex
  lia

/-- Each valid coordinate has a linear bound on its binary output size. -/
theorem entry_size_le {m a : ℕ} (ha : a < m) (j l : ℕ) :
    (entry m a j l).size ≤ m + 1 := by
  unfold entry
  split_ifs
  · exact (oddEntry_size_le _ _ _ _).trans (by have := core_bounds (by lia : 0 < m); lia)
  · simp

/-- Coordinate restriction recovers the whole odd core exactly. -/
theorem odd_borderRank_le {m : ℕ} (hm : 0 < m) :
    (oddTensor (coreIndex m)).borderRank ≤ (tensor m).borderRank := by
  let inclusion := Fin.castLE (core_bounds hm).1
  have sub : (tensor m).subtensor inclusion inclusion inclusion = oddTensor (coreIndex m) := by
    funext a j l
    simp [subtensor, tensor, entry, oddTensor, inclusion, a.isLt, j.isLt, l.isLt]
  rw [← sub]
  exact borderRank_subtensor_le inclusion inclusion inclusion (tensor m)

/-- Growing ambient dimension also grows the odd core. -/
theorem coreIndex_tendsto : Tendsto coreIndex atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (2 * k + 1)] with m hm
  unfold coreIndex
  lia

end Algebraic.Tensor3.Dissociated.Internal
