/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.InsertionExpectation
public import Tengoku.LeanPool.LeanPool.Feige.TwoPointInduction
import Tengoku.LeanPool.LeanPool.Feige.ProductSplit

/-!
# Constructing a dominating chain for ordered two-point systems

This is the finite induction used to prove the two-point case of Theorem 2.1.
Its sole input is the local insertion theorem.  The product law is split at
the last coordinate, the induction hypothesis constructs a chain on the old
coordinates, and one insertion of the new coordinate completes the step.
-/

@[expose] public section

open scoped BigOperators

namespace Feige

/-- Revealing one independent Bernoulli coordinate preserves monotonicity
of a payoff on the Boolean lattice. -/
theorem monotone_revealedLastPayoff {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {g : Finset (Fin (n + 1)) → ℝ} (hg : Monotone g) :
    Monotone (revealedLastPayoff p g) := by
  intro S T hST
  unfold revealedLastPayoff
  have hlift :
      liftChainState S ⊆ liftChainState T := by
    exact Finset.map_subset_map.mpr hST
  have hlower :
      g (liftChainState S) ≤ g (liftChainState T) :=
    hg hlift
  have hupper :
      g (insert (Fin.last n) (liftChainState S)) ≤
        g (insert (Fin.last n) (liftChainState T)) := by
    exact hg (Finset.insert_subset_insert (Fin.last n) hlift)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hp1))
    (mul_le_mul_of_nonneg_left hupper hp0)

end Feige
