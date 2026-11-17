/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

import Tengoku.Roundedrootsums.RoundedRootSums.Definitions
import Tengoku.Roundedrootsums.RoundedRootSums.RootSum
import Tengoku.Roundedrootsums.RoundedRootSums.MainFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ceiling-root sums

This file develops sums of square roots rounded upward and
their corresponding closed formulas.
-/

open scoped BigOperators

namespace RoundedRootSums

/--
For a positive integer `k + 1`, its square root rounded upward is

`Nat.sqrt k + 1`.

Indeed,

`⌈√(k + 1)⌉ = ⌊√k⌋ + 1`.-/
def ceilSqrtSucc (k : Nat) : Nat :=
  Nat.sqrt k + 1

/--
The sum of square roots rounded upward from `1` through `n`:

`⌈√1⌉ + ⌈√2⌉ + ... + ⌈√n⌉`.-/
def ceilRootSum (n : Nat) : Nat :=
  Finset.sum (Finset.range n) ceilSqrtSucc

/--
Unfolding the definition of the ceiling-root sum.
@isnad1 id=eq.0h1v.s4.b0c6097dfcfb from=translated src=- shape=e4a55431 vocab=b2aa239b
-/
theorem ceilRootSum_unfold (n : Nat) :
    ceilRootSum n =
      Finset.sum (Finset.range n)
        (fun k => Nat.sqrt k + 1) := by
  rfl

/--
@isnad1 id=eq.0h1v.s4.01503853de79 from=translated src=- shape=941c26d4 vocab=b2aa239b
-/
theorem ceilRootSum_eq (n : Nat) :
    ceilRootSum n =
      Finset.sum (Finset.range n) (fun k => Nat.sqrt k) + n := by
  unfold ceilRootSum ceilSqrtSucc
  rw [Finset.sum_add_distrib]
  simp

/--
Adding the last term to the ordinary root sum.
@isnad1 id=eq.0h1v.s4.eeedacb3ba0b from=translated src=- shape=cb24058d vocab=42edcc74
-/
theorem rootSum_step (n : Nat) :
    rootSum n =
      rootSum (n - 1) + Nat.sqrt n := by
  cases n with
  | zero =>
      simp [rootSum]
  | succ n =>
      unfold rootSum
      simp only [Nat.succ_sub_one]
      rw [Finset.sum_range_succ]

/--
The ceiling-root sum is the ordinary root sum up to `n - 1`,
plus one for each of the `n` summands.
@isnad1 id=eq.0h1v.s4.fabc1f54db25 from=translated src=- shape=ec147368 vocab=c9d9f999
-/
theorem ceilRootSum_eq_rootSum (n : Nat) :
    ceilRootSum n = rootSum (n - 1) + n := by
  induction n with
  | zero =>
      simp [ceilRootSum, rootSum]
  | succ n ih =>
      unfold ceilRootSum
      rw [Finset.sum_range_succ]
      change
        ceilRootSum n + ceilSqrtSucc n =
          rootSum n + (n + 1)
      rw [ih]
      unfold ceilSqrtSucc
      rw [rootSum_step n]
      omega

/--
Fully explicit closed formula for the sum of square roots
rounded upward.
@isnad1 id=eq.0h1v.s7.6491540c0f62 from=translated src=- shape=a14e7a0f vocab=98e84ba8
-/
theorem ceilRootSum_explicit_formula (n : Nat) :
    ceilRootSum n =
      rootIndex (n - 1) * n -
        rootIndex (n - 1) * (rootIndex (n - 1) + 1) *
          (2 * rootIndex (n - 1) + 1) / 6
      + n := by
  cases n with
  | zero =>
      simp [ceilRootSum, rootIndex]
  | succ n =>
      rw [ceilRootSum_eq_rootSum]
      rw [rootSum_explicit_formula]
      simp

end RoundedRootSums
