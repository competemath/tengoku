/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order.Internal

/-!
# Path decompositions of cubic graphs from edge scores

A real score on the edges of a cubic graph lists the edges in nondecreasing order. Bag `k`
of the resulting path decomposition holds the vertices with an incident edge at a position
at most `k` and another at a position at least `k`.

* `indicator_edgeStraddles_le`: a vertex straddling a threshold has at least four ordered
  pairs of distinct incident edges separated by the threshold, so the indicator of
  straddling is at most a quarter of the number of separated pairs.
* `exists_pathDecomposition_subset_edgeScore`: bag `k` lies inside the vertices with an edge
  scoring at most `t` and an edge scoring at least `t`, where `t` is the score of the `k`-th
  edge.
* `exists_pathDecomposition_of_edgeScore`: fix thresholds `a + i δ` for `i ≤ M`. If twice
  the number of edges in each tail is at most `B`, and for each `i < M` the straddling
  vertices of `a + i δ` plus twice the number of edges scoring in `[a + i δ, a + (i + 1) δ)`
  number at most `B`, then every bag has at most `B` vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

open scoped Classical in
/-- **Score-order path decomposition.** List the edges of a cubic graph in nondecreasing score
order and let bag `k` hold the vertices with an incident edge at a position at most `k` and
another at a position at least `k`. Each bag lies inside the vertices with an edge scoring at
most `t` and an edge scoring at least `t`, where `t` is the score of the `k`-th edge. -/
theorem exists_pathDecomposition_subset_edgeScore (regular : H.IsRegularOfDegree 3)
    (score : Sym2 W → ℝ) :
    ∃ D : PathDecomposition H, ∀ k, ∃ t : ℝ, D.bag k ⊆ Finset.univ.filter fun v =>
      (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧ ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e :=
  Internal.exists_pathDecomposition_subset_edgeScore H regular score

end Algebraic.Cutwidth.Gaussian
