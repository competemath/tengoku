/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.TreeComponent.Internal

/-!
# Locating a tree component for the endpoint induction

Fomin and Høie's Lemma 4, Case 3.A, uses the elementary fact that a finite
graph with fewer edges than vertices has a connected component that is a
tree. The component includes isolated vertices as one-vertex trees.
If every vertex of a prescribed boundary has at least two neighbors outside
it and the boundary has more than one third of the vertices, degree counting
produces the required edge deficit in its complement.

The quantitative version also bounds the size of a tree component in terms
of the edge deficit. It supports the small-component analysis in Monien
and Preis's red/black graph argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- A linear edge deficit forces a small tree component. No degree bound is required.
@isnad1 id=ex.1h3v.s7.393a5595e50d from=translated src=- shape=51d485db vocab=3a4337ee
-/
theorem exists_small_tree_component_of_edge_deficit {W : Type} [Fintype W]
    (H : SimpleGraph W) (M : Nat)
    (deficit : (M + 1) * H.edgeFinset.card < M * Fintype.card W) :
    ∃ C : H.ConnectedComponent, C.toSimpleGraph.IsTree ∧ Fintype.card C ≤ M :=
  PathDecomposition.Internal.exists_small_tree_component_of_edge_deficit H M deficit

/-- A graph with fewer edges than vertices has a tree component.
@isnad1 id=ex.1h2v.s6.8bc9499f18f6 from=translated src=- shape=b52be988 vocab=29f8d2fe
-/
theorem exists_tree_component_of_card_edgeFinset_lt {W : Type} [Fintype W]
    (H : SimpleGraph W) (hcard : H.edgeFinset.card < Fintype.card W) :
    ∃ C : H.ConnectedComponent, C.toSimpleGraph.IsTree :=
  PathDecomposition.Internal.exists_tree_component_of_card_edgeFinset_lt H hcard

/-- In a subcubic graph, a boundary larger than one third of the graph with
at least two outside neighbors per boundary vertex leaves fewer edges than
vertices in its complement.
@isnad1 id=lt.3h3v.s9.da48b86d6b9d from=translated src=- shape=ce3b8589 vocab=fb56e2c6
-/
theorem complement_card_edges_lt {W : Type} [Fintype W]
    (H : SimpleGraph W) (X : Finset W)
    (degree : ∀ v, H.degree v ≤ 3) (large : Fintype.card W < 3 * X.card)
    (outside : ∀ v ∈ X, 2 ≤ ((H.neighborFinset v) \ X).card) :
    (H.induce {w | w ∉ X}).edgeFinset.card < Fintype.card {w : W // w ∉ X} :=
  PathDecomposition.Internal.complement_card_edges_lt H X degree large outside

/-- The tree component required by Case 3.A of Fomin and Høie's endpoint
decomposition lemma exists under its degree and boundary-size conditions.
@isnad1 id=ex.3h3v.s8.40b9d81f9c8b from=translated src=- shape=8a7d5d5f vocab=a117bd3a
-/
theorem exists_tree_component_complement {W : Type} [Fintype W]
    (H : SimpleGraph W) (X : Finset W)
    (degree : ∀ v, H.degree v ≤ 3) (large : Fintype.card W < 3 * X.card)
    (outside : ∀ v ∈ X, 2 ≤ ((H.neighborFinset v) \ X).card) :
    ∃ C : (H.induce {w | w ∉ X}).ConnectedComponent, C.toSimpleGraph.IsTree :=
  exists_tree_component_of_card_edgeFinset_lt _
    (complement_card_edges_lt H X degree large outside)

/-- The structural alternatives in the endpoint induction: a large boundary
contains a vertex with at most one outside neighbor, or its complement has a
tree component. Either alternative permits deleting a nonempty set of vertices.
@isnad1 id=or.2h3v.s8.0b9ed3e2795a from=translated src=- shape=73987f8c vocab=a117bd3a
-/
theorem boundary_reduction {W : Type} [Fintype W]
    (H : SimpleGraph W) (X : Finset W)
    (degree : ∀ v, H.degree v ≤ 3) (large : Fintype.card W < 3 * X.card) :
    (∃ v ∈ X, ((H.neighborFinset v) \ X).card ≤ 1) ∨
      ∃ C : (H.induce {w | w ∉ X}).ConnectedComponent, C.toSimpleGraph.IsTree := by
  by_cases small : ∃ v ∈ X, ((H.neighborFinset v) \ X).card ≤ 1
  · exact Or.inl small
  · apply Or.inr
    apply exists_tree_component_complement H X degree large
    intro v hv
    have hnot : ¬ ((H.neighborFinset v) \ X).card ≤ 1 := fun h => small ⟨v, hv, h⟩
    lia

end Algebraic.Cutwidth
