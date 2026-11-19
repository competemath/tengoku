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

/--
@isnad1 id=isembedd.0h2v.s8.19f345aebdee from=translated src=- shape=e39008af vocab=654333cd
-/
theorem isEmbedding_projection : Topology.IsEmbedding (projection (n := n) (k := k)) :=
  projection_injective.isEmbedding_induced

/--
@isnad1 id=surjecti.0h3v.s12.48fab1da4212 from=translated src=- shape=76aa4be5 vocab=aa88e604
-/
theorem orbit_surjective (V : Grassmannian n k) :
    Function.Surjective (fun u : Rotations n ↦ rotate u V) := exists_rotate_eq V

end NKBesicovitch.Grassmannian
