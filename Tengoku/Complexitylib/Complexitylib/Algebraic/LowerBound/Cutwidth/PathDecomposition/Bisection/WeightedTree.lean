/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.WeightedTree.Internal

/-!
# Light adjacent pairs in weighted trees

Monien and Preis's red/black argument contracts parts of a black component
to a weighted tree. When all its leaves are sufficiently heavy, a light
adjacent pair gives the next small candidate for a positive set.

We prove their weighted-tree lemma through a forest inequality: nonnegative
weights at leaves and isolated vertices, together with nonnegative sums
across edges, force a nonnegative total. Shifting weights by a threshold
then gives a light adjacent pair whenever the total lies below that threshold
times the number of vertices. `RedBlack.Restoration` handles one local
edge-restoration step. Monien and Preis's global tree reorganization is not
formalized: `RedBlack.Clusters` proves their red/black lemma by bounded
connected partitions instead, and `Bisection.exists_bisectionBound` uses it.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.WeightedTree

open scoped Classical

end Algebraic.Cutwidth.Bisection.WeightedTree
