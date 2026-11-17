/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku
import Tengoku.Seed.Order.Interval.Finset.Nat
import Tengoku.Roundedrootsums.RoundedRootSums.Blocks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Block sums

This file computes the sum of integer square roots over a complete
square block.
-/

namespace RoundedRootSums

def blockSum (m : Nat) : Nat :=
  Finset.sum
    (Finset.Icc (m ^ 2) ((m + 1) ^ 2 - 1))
    (fun k => Nat.sqrt k)

/--
@isnad1 id=eq.0h1v.s5.9cef68410ea0 from=translated src=- shape=4c03d943 vocab=9a9b58af
-/
theorem blockSum_formula (m : Nat) :
    blockSum m = m * (2 * m + 1) := by
  unfold blockSum
  calc
    Finset.sum
        (Finset.Icc (m ^ 2) ((m + 1) ^ 2 - 1))
        (fun k => Nat.sqrt k)
        =
        Finset.sum
          (Finset.Icc (m ^ 2) ((m + 1) ^ 2 - 1))
          (fun _ => m) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      apply sqrt_eq_of_mem_block m k
      · exact hk'.1
      · exact Nat.lt_of_le_sub_one (by positivity) hk'.2
    _ =
        (Finset.Icc (m ^ 2) ((m + 1) ^ 2 - 1)).card * m := by
      simp
    _ = (2 * m + 1) * m := by
      have hcard :
          (Finset.Icc (m ^ 2) ((m + 1) ^ 2 - 1)).card =
            2 * m + 1 := by
        rw [Nat.card_Icc]
        have hpow :
            (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by
          ring
        rw [hpow]
        have hpos :
            1 ≤ m ^ 2 + (2 * m + 1) := by
          omega
        rw [Nat.sub_add_cancel hpos]
        omega
      rw [hcard]
    _ = m * (2 * m + 1) := by
      ring

end RoundedRootSums
