/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Hausdorff.Transfer
public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.Iteration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hausdorff dimension at the critical exponent

Finite plate induction gives the dimension bound for every ratio strictly
below the critical exponent. Continuity gives the endpoint dimension
inequality without asserting an endpoint maximal estimate.
-/

public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace NKBesicovitch.Hausdorff

theorem dimH_eq_of_isBesicovitch_self {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    (hB : IsBesicovitch n E) : dimH E = n := by
  obtain ⟨a, ha⟩ := hB ⊤ (by simp)
  have hball : ball a 1 ⊆ E := by
    intro x hx
    have hn : ‖x - a‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hx
    simpa using ha (x - a) (Submodule.mem_top) hn.le
  simpa using Real.dimH_of_mem_nhds (mem_of_superset (ball_mem_nhds a zero_lt_one) hball)

end NKBesicovitch.Hausdorff
