/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku

/-!
# Weight inequalities on forests

Monien and Preis's weighted-tree lemma finds a light adjacent pair when
the leaves are heavy. We prove the underlying inequality by deleting a
leaf, or a leaf together with its negative-weight neighbor. This avoids
choosing rooted subtrees in the weighted argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.WeightedTree.Internal

open scoped Classical

end Algebraic.Cutwidth.Bisection.WeightedTree.Internal
