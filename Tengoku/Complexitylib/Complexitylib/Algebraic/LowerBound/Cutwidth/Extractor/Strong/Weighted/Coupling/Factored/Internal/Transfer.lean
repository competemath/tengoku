/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
public import Tengoku

/-!
# Transferring conditional uniformity across a repair

A repair changes a deterministic continuation by at most its total
variation cost. If the retained marginal changes, comparing to the
actual marginal costs at most the same amount once more. These bounds
hold for arbitrary real weights and also for empty output alphabets.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightDist_uniformSecond_le_of_dist_of_same_first {Tag Out : Type*}
    [Fintype Tag] [Fintype Out] {p q : Tag × Out → ℝ} {ρ ε : ℝ}
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist q (uniformSecondWeight q) ≤ ε)
    (same : firstWeight p = firstWeight q) :
    weightDist p (uniformSecondWeight p) ≤ ρ + ε := by
  have reference : uniformSecondWeight p = uniformSecondWeight q := by
    simp only [uniformSecondWeight, same]
  rw [reference]
  exact (weightDist_triangle p q (uniformSecondWeight q)).trans (add_le_add near uniform)

end Algebraic.Cutwidth.Extractor.Internal
