/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Transitivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Topological properties of direction space

The projection embedding makes the Grassmannian Hausdorff and second countable.
Transitivity realizes every nonempty Grassmannian as a compact orbit.
-/

public section

namespace NKBesicovitch.Grassmannian

variable {n k : ℕ}

theorem isEmbedding_projection : Topology.IsEmbedding (projection (n := n) (k := k)) :=
  projection_injective.isEmbedding_induced

theorem orbit_surjective (V : Grassmannian n k) :
    Function.Surjective (fun u : Rotations n ↦ rotate u V) := exists_rotate_eq V

end NKBesicovitch.Grassmannian
