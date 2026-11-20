/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Headline
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.CountOdd
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.CountEven
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.SumIdentities
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The bcs coordination sequence: main theorem

Assembles the per-class level-set counts into the coordination-sequence
formula: odd shells via `bcs_coordination_odd`, even shells via
`bcs_coordination_even`, unified in `bcs_coordination_sequence`.

The statement is purely graph-theoretic: `sphere n` is the set of states of
the bcs net whose graph distance from the base vertex (least walk length) is
exactly `n`.
-/

namespace Bcs

open Finset

/-- `D` on class index 0 is `D1` (and so on): definitional dispatch.-/
theorem D_zero (x y z : Int) : D (0, x, y, z) = D1 x y z := rfl
theorem D_one (x y z : Int) : D (1, x, y, z) = D2 x y z := rfl
theorem D_two (x y z : Int) : D (2, x, y, z) = D3 x y z := rfl
theorem D_three (x y z : Int) : D (3, x, y, z) = D4 x y z := rfl
theorem D_four (x y z : Int) : D (4, x, y, z) = D5 x y z := rfl
theorem D_five (x y z : Int) : D (5, x, y, z) = D6 x y z := rfl
theorem D_six (x y z : Int) : D (6, x, y, z) = D7 x y z := rfl
theorem D_seven (x y z : Int) : D (7, x, y, z) = D8 x y z := rfl

/-- The even-parity classes (1, 5, 6, 7 in mathematical numbering; indices
0, 4, 5, 6) contribute nothing to odd shells.-/
theorem classCard_idx0_odd (n : ℕ) (hn : n % 2 = 1) : classCard 0 n = 0 := by
  unfold classCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ - heq
  rw [D_zero] at heq
  have hpar : D1 x y z % 2 = 0 := by unfold D1; split <;> omega
  rw [heq] at hpar
  omega

theorem classCard_idx4_odd (n : ℕ) (hn : n % 2 = 1) : classCard 4 n = 0 := by
  unfold classCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ - heq
  rw [D_four] at heq
  have hpar : D5 x y z % 2 = 0 := by unfold D5; omega
  rw [heq] at hpar
  omega

theorem classCard_idx5_odd (n : ℕ) (hn : n % 2 = 1) : classCard 5 n = 0 := by
  unfold classCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ - heq
  rw [D_five] at heq
  have hpar : D6 x y z % 2 = 0 := by unfold D6; omega
  rw [heq] at hpar
  omega

theorem classCard_idx6_odd (n : ℕ) (hn : n % 2 = 1) : classCard 6 n = 0 := by
  unfold classCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨x, y, z⟩ - heq
  rw [D_six] at heq
  have hpar : D7 x y z % 2 = 0 := by unfold D7; omega
  rw [heq] at hpar
  omega

/-- `classCard` at an odd-class index is the corresponding `levelCard`.-/
theorem classCard_idx1 (n : ℕ) : classCard 1 n = CountOdd.levelCard D2 n := rfl
theorem classCard_idx2 (n : ℕ) : classCard 2 n = CountOdd.levelCard D3 n := rfl
theorem classCard_idx3 (n : ℕ) : classCard 3 n = CountOdd.levelCard D4 n := rfl
theorem classCard_idx7 (n : ℕ) : classCard 7 n = CountOdd.levelCard D8 n := rfl

/-- The odd-parity classes (indices 1, 2, 3, 7) contribute nothing to even
shells: their distance functions take odd values only.-/
theorem classCard_idx1_even (n : ℕ) (hn : n % 2 = 0) : classCard 1 n = 0 :=
  CountOdd.levelCard_D2_even n hn

theorem classCard_idx2_even (n : ℕ) (hn : n % 2 = 0) : classCard 2 n = 0 :=
  CountOdd.levelCard_D3_even n hn

theorem classCard_idx3_even (n : ℕ) (hn : n % 2 = 0) : classCard 3 n = 0 :=
  CountOdd.levelCard_D4_even n hn

theorem classCard_idx7_even (n : ℕ) (hn : n % 2 = 0) : classCard 7 n = 0 :=
  CountOdd.levelCard_D8_even n hn

/-- `classCard` at an even-class index is the corresponding `levelCard`.-/
theorem classCard_idx0 (n : ℕ) : classCard 0 n = CountEven.levelCard D1 n := rfl
theorem classCard_idx4 (n : ℕ) : classCard 4 n = CountEven.levelCard D5 n := rfl
theorem classCard_idx5 (n : ℕ) : classCard 5 n = CountEven.levelCard D6 n := rfl
theorem classCard_idx6 (n : ℕ) : classCard 6 n = CountEven.levelCard D7 n := rfl

/-- Shell 0 is the base state alone.-/
theorem bcs_coordination_0 : (sphere 0).ncard = 1 := by
  rw [sphere_ncard_eq_sum]; decide +kernel

/-- Shell 1: the six nearest neighbors.-/
theorem bcs_coordination_1 : (sphere 1).ncard = 6 := by
  rw [sphere_ncard_eq_sum]; decide +kernel

/-- Shell 2 is the one genuinely exceptional value: 24, not 6·2²+2 = 26.-/
theorem bcs_coordination_2 : (sphere 2).ncard = 24 := by
  rw [sphere_ncard_eq_sum]; decide +kernel

end Bcs
