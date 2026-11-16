/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku
import Tengoku.Roundedrootsums.RoundedRootSums.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Square-root blocks

Basic characterizations of the intervals on which the integer square root
is constant.
-/

namespace RoundedRootSums

theorem sqrt_block (m k : Nat) :
    Nat.sqrt k = m ↔ m ^ 2 ≤ k ∧ k < (m + 1) ^ 2 := by
  constructor
  · intro h
    subst m
    constructor
    · simpa [pow_two] using Nat.sqrt_le k
    · have hlt : Nat.sqrt k < Nat.sqrt k + 1 := Nat.lt_succ_self _
      exact (Nat.sqrt_lt' (m := k) (n := Nat.sqrt k + 1)).mp hlt
  · intro h
    apply Nat.le_antisymm
    · have hs : Nat.sqrt k < m + 1 := by
        exact (Nat.sqrt_lt' (m := k) (n := m + 1)).mpr h.2
      omega
    · exact (Nat.le_sqrt).2 (by simpa [pow_two] using h.1)

theorem sqrt_eq_of_mem_block (m k : Nat)
    (h₁ : m ^ 2 ≤ k)
    (h₂ : k < (m + 1) ^ 2) :
    Nat.sqrt k = m := by
  exact (sqrt_block m k).2 ⟨h₁, h₂⟩

theorem sqrt_const_on_block (m t : Nat)
    (h : t < 2 * m + 1) :
    Nat.sqrt (m ^ 2 + t) = m := by
  apply sqrt_eq_of_mem_block
  · omega
  · nlinarith

end RoundedRootSums
