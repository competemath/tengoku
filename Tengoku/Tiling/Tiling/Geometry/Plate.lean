import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Connected
import Tengoku.Tiling.Tiling.Basic
import Tengoku.Tiling.Tiling.Geometry.Plane

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/jaumededios/Tiling@00f80c7de5ac, `Tiling/Geometry/Plate.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/


/-!
# Plates of a polygonal prototiling

A polygonal prototiling consists of a family of planar prototiles and a selected set of
placements, each of whose supports is polygonal.  Its vertex graph joins distinct placements that
share a vertex of both tiles.  Its edge graph joins distinct placements whose boundaries share a
nondegenerate line segment away from the vertices of both tiles.

Sharing a vertex is not transitive: two tiles can meet a third tile at different vertices without
meeting each other.  A plate is therefore a connected component of the vertex graph.
-/

open Set
open scoped Pointwise

namespace Tiling

universe u

/-- A planar prototiling whose prototile family has polygonal support.-/
structure PolygonalProtoTiling (P : Type u) where
  /-- The labelled family of prototiles.-/
  prototiles : PrototileFamily Plane P
  /-- The selected translated and labelled copies.-/
  placements : ProtoTiling Plane P
  /-- Every prototile support is polygonal.-/
  isPolygonal : ∀ p, IsPolygonal (prototiles p).support

namespace PolygonalProtoTiling

variable {P : Type u} (A : PolygonalProtoTiling P)

/-- Replace the selected placements while keeping the polygonal prototile family fixed.-/
def withPlacements (S : ProtoTiling Plane P) : PolygonalProtoTiling P where
  prototiles := A.prototiles
  placements := S
  isPolygonal := A.isPolygonal

/--
@isnad1 id=eq.0h3v.s4.0d44bce1cf61 from=translated src=- shape=66d7608b vocab=2c67b639
-/
@[simp]
theorem withPlacements_prototiles (S : ProtoTiling Plane P) :
    (A.withPlacements S).prototiles = A.prototiles :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.fa7db0af70d8 from=translated src=- shape=44494efe vocab=a26b7243
-/
@[simp]
theorem withPlacements_placements (S : ProtoTiling Plane P) :
    (A.withPlacements S).placements = S :=
  rfl

/-- The vertices of a placed prototile, obtained by translating the vertices of its support.-/
def placedVertexSet (i : A.placements) : Set Plane :=
  i.1.1 +ᵥ vertexSet (A.prototiles i.1.2).support

/-- Two placements are vertex-connected when they share a point which is a vertex of both.-/
def VertexConnected (i j : A.placements) : Prop :=
  (A.placedVertexSet i ∩ A.placedVertexSet j).Nonempty

/-- Vertex contact is symmetric.
@isnad1 id=iff.0h4v.s5.65e27c644c71 from=translated src=- shape=8d724290 vocab=612b7ad0
-/
theorem vertexConnected_comm (i j : A.placements) :
    A.VertexConnected i j ↔ A.VertexConnected j i := by
  simp only [VertexConnected, inter_comm]

/-- Two placements are edge-connected when their frontiers share a nondegenerate open segment
which contains no vertex of either placement.-/
def EdgeConnected (i j : A.placements) : Prop :=
  ∃ a b : Plane, a ≠ b ∧
    openSegment ℝ a b ⊆
      (frontier (placedTile A.prototiles i.1) ∩ frontier (placedTile A.prototiles j.1)) \
        (A.placedVertexSet i ∪ A.placedVertexSet j)

/-- Edge contact is symmetric.
@isnad1 id=iff.0h4v.s5.d5d1b28a1d10 from=translated src=- shape=8d724290 vocab=ab3f3ab9
-/
theorem edgeConnected_comm (i j : A.placements) :
    A.EdgeConnected i j ↔ A.EdgeConnected j i := by
  constructor <;> rintro ⟨a, b, hab, hsegment⟩
  · exact ⟨a, b, hab, by simpa [inter_comm, union_comm] using hsegment⟩
  · exact ⟨a, b, hab, by simpa [inter_comm, union_comm] using hsegment⟩

/-- Two placements share a nonvertex when their supports meet away from the vertices of both.-/
def SharesNonvertex (i j : A.placements) : Prop :=
  ((placedTile A.prototiles i.1 ∩ placedTile A.prototiles j.1) \
    (A.placedVertexSet i ∪ A.placedVertexSet j)).Nonempty

/-- The graph whose edges record vertex-connected pairs of distinct placed tiles.-/
def vertexGraph : SimpleGraph A.placements :=
  SimpleGraph.fromRel A.VertexConnected

/-- The graph whose edges record edge-connected pairs of distinct placed tiles.-/
def edgeGraph : SimpleGraph A.placements :=
  SimpleGraph.fromRel A.EdgeConnected

/-- Adjacency in the vertex graph is distinctness together with geometric vertex contact.
@isnad1 id=iff.0h4v.s5.6935776b6956 from=translated src=- shape=e2d5b452 vocab=e2b0b244
-/
@[simp]
theorem vertexGraph_adj (i j : A.placements) :
    A.vertexGraph.Adj i j ↔ i ≠ j ∧ A.VertexConnected i j := by
  rw [vertexGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, hij' | hji'⟩
    · exact ⟨hij, hij'⟩
    · exact ⟨hij, (A.vertexConnected_comm j i).mp hji'⟩
  · rintro ⟨hij, hconnected⟩
    exact ⟨hij, Or.inl hconnected⟩

/-- Adjacency in the edge graph is distinctness together with geometric edge contact.
@isnad1 id=iff.0h4v.s5.df7e5537a57f from=translated src=- shape=e2d5b452 vocab=33a95b08
-/
@[simp]
theorem edgeGraph_adj (i j : A.placements) :
    A.edgeGraph.Adj i j ↔ i ≠ j ∧ A.EdgeConnected i j := by
  rw [edgeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, hij' | hji'⟩
    · exact ⟨hij, hij'⟩
    · exact ⟨hij, (A.edgeConnected_comm j i).mp hji'⟩
  · rintro ⟨hij, hconnected⟩
    exact ⟨hij, Or.inl hconnected⟩

/-- Two placements belong to the same plate when a finite walk in the vertex graph joins them.-/
abbrev SamePlate : A.placements → A.placements → Prop :=
  A.vertexGraph.Reachable

/-- A plate is a connected component of the vertex graph.-/
abbrev Plate :=
  A.vertexGraph.ConnectedComponent

/-- Reachability is equivalently equality of vertex-graph connected components.
@isnad1 id=iff.0h4v.s5.3eb22cd2adfd from=translated src=- shape=64b9203a vocab=7db4e8ed
-/
theorem samePlate_iff_component_eq (i j : A.placements) :
    A.SamePlate i j ↔
      A.vertexGraph.connectedComponentMk i = A.vertexGraph.connectedComponentMk j :=
  SimpleGraph.ConnectedComponent.eq.symm

/-- The carrier of a placement subfamily is the union of its placed supports.-/
def placementCarrier (S : Set A.placements) : Set Plane :=
  ⋃ i : S, placedTile A.prototiles (i : A.placements).1

/-- Membership in a placement-subfamily carrier is witnessed by a placement in the subfamily.
@isnad1 id=iff.0h4v.s6.4afd9c660402 from=translated src=- shape=694187b4 vocab=fef1a298
-/
@[simp]
theorem mem_placementCarrier_iff {S : Set A.placements} {x : Plane} :
    x ∈ A.placementCarrier S ↔
      ∃ i : A.placements, i ∈ S ∧ x ∈ placedTile A.prototiles i.1 := by
  rw [placementCarrier, mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.2, hi⟩
  · rintro ⟨i, hiS, hxi⟩
    exact ⟨⟨i, hiS⟩, hxi⟩

/-- The carrier of a plate is the carrier of its set of placements.

Under the local-finiteness hypotheses derived from a finite-family tiling this union is closed; the
definition itself does not require those hypotheses.-/
def plateCarrier (C : A.Plate) : Set Plane :=
  A.placementCarrier C

/-- Membership in a plate carrier is witnessed by a placement in that plate.
@isnad1 id=iff.0h4v.s6.078ae1585ef4 from=translated src=- shape=8d9204cb vocab=f3c0d3a6
-/
@[simp]
theorem mem_plateCarrier_iff {C : A.Plate} {x : Plane} :
    x ∈ A.plateCarrier C ↔
      ∃ i : A.placements, i ∈ C ∧ x ∈ placedTile A.prototiles i.1 := by
  exact A.mem_placementCarrier_iff

/-- Every placed support lies in the carrier of its vertex-graph component.
@isnad1 id=le.0h3v.s6.3b9a3e13f700 from=translated src=- shape=83e8e543 vocab=35f673bb
-/
theorem placedTile_subset_plateCarrier (i : A.placements) :
    placedTile A.prototiles i.1 ⊆
      A.plateCarrier (A.vertexGraph.connectedComponentMk i) := by
  intro x hx
  exact A.mem_plateCarrier_iff.mpr
    ⟨i, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, hx⟩

/-- Every plate carrier is nonempty.
@isnad1 id=nonempty.0h3v.s3.9134477a9f1a from=translated src=- shape=d0668016 vocab=ee062e27
-/
theorem plateCarrier_nonempty (C : A.Plate) : (A.plateCarrier C).Nonempty := by
  obtain ⟨i, hiC⟩ := C.nonempty_supp
  obtain ⟨x, hxi⟩ := (A.prototiles i.1.2).nonempty_support
  refine ⟨i.1.1 + x, A.mem_plateCarrier_iff.mpr ⟨i, hiC, ?_⟩⟩
  simpa [placedTile, mem_vadd_set_iff_neg_vadd_mem]

end PolygonalProtoTiling

end Tiling
