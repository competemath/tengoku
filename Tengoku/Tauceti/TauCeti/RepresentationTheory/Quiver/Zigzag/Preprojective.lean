/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation
public import Tengoku
import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Preprojective.Bipartite
import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Zigzag.Connected

/-!
# Signless and preprojective relations of an oriented graph

A two-colouring of a simple graph gives a source--sink orientation by directing every edge toward
its `true` endpoint. Symmetrifying this oriented quiver recovers the doubled quiver. Under that
identification, the signless relation of the graph becomes the signless relation of the
symmetrified orientation.

Since every arrow of the oriented quiver goes from a `false` vertex to a `true` vertex, the
signless/preprojective comparison needs no further arrow rescaling. Thus the signless
preprojective algebra of the doubled graph is explicitly isomorphic to the additive
preprojective algebra of its source--sink orientation.

Conversely, suppose that a unit gauge makes every corner of the preprojective relator a scalar
multiple of the corresponding signless relator. The comparison scalars change sign along every
edge. A non-bipartite graph has an odd closed walk, which would therefore force `2 = 0`. Over a
coefficient ring in which `2 ≠ 0`, a non-bipartite graph therefore admits no such comparison, for
any choice of orientation.

## Main definitions

* `SimpleGraph.Coloring.sourceSink`: the orientation directed toward colour `true`.
* `TauCeti.DoubledQuiver.orientationPathAlgebraEquiv`: the path-algebra comparison induced by
  restoring an orientation.
* `TauCeti.DoubledQuiver.orientationSignlessPreprojectiveAlgebraEquiv`: the induced comparison
  between the signless algebra of the doubled graph and the signless algebra of a symmetrified
  orientation.
* `SimpleGraph.Coloring.sourceSinkSignlessPreprojectiveAlgebraEquiv`: the comparison between the
  graph's signless algebra and the preprojective algebra of the source--sink orientation.
* `TauCeti.DoubledQuiver.Orientation.not_exists_forall_vertexCorner_eq_smul_of_not_isBipartite`:
  over coefficients with `2 ≠ 0`, a non-bipartite graph admits no cornerwise unit-gauge
  comparison.

## References

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060, for the signless relation and its comparison with the
preprojective relation of a bipartite graph.
-/

public section

attribute [local instance] Fintype.ofFinite

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u w

namespace DoubledQuiver

variable {V : Type u} {G : SimpleGraph V}

section PathAlgebra

variable (o : Orientation G) (k : Type w) [CommSemiring k] [Finite V]

end PathAlgebra

/-! ### Transporting the signless quotient -/

section Quotient

variable (o : Orientation G) (k : Type w) [CommRing k] [Finite V]

end Quotient

end DoubledQuiver

end TauCeti

namespace SimpleGraph.Coloring

open TauCeti TauCeti.DoubledQuiver TauCeti.PathAlgebra _root_.Quiver

universe u w

variable {V : Type u} {G : SimpleGraph V}

variable (C : G.Coloring Bool)

/-- The colour of a vertex of the oriented quiver, transported from the graph. -/
def sourceSinkColor (i : OrientedQuiver G C.sourceSink) : Bool :=
  C ((OrientedQuiver.vertexEquiv G C.sourceSink).symm i)

/-- The colour on the source--sink oriented quiver is the original graph colouring. -/
@[simp]
theorem sourceSinkColor_vertex (i : V) :
    C.sourceSinkColor (OrientedQuiver.vertex G C.sourceSink i) = C i := by
  rw [sourceSinkColor, OrientedQuiver.vertexEquiv_symm_vertex]

/-- Every arrow of the source--sink orientation has differently coloured endpoints. -/
theorem sourceSinkColor_ne {i j : OrientedQuiver G C.sourceSink} (a : i ⟶ j) :
    C.sourceSinkColor i ≠ C.sourceSinkColor j := by
  exact C.valid a.1

/-- Every arrow of the source--sink orientation ends at a vertex of colour `true`. -/
theorem sourceSinkColor_target_eq_true
    {i j : OrientedQuiver G C.sourceSink} (a : i ⟶ j) :
    C.sourceSinkColor j = true := by
  rw [sourceSinkColor]
  exact (mem_sourceSink_iff C _).mp a.2

/-! ### The preprojective comparison -/

variable (k : Type w) [CommRing k] [Finite V]

end SimpleGraph.Coloring

namespace TauCeti.DoubledQuiver.Orientation

open _root_.Quiver

universe u w

variable {V : Type u} {G : SimpleGraph V}

/-! ### The non-bipartite obstruction -/

end TauCeti.DoubledQuiver.Orientation
