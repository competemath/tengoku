/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Tengoku.LeanPool.LeanPool.Schoenflies.Curve
public import Tengoku.LeanPool.LeanPool.Schoenflies.Topology
public import Tengoku.LeanPool.LeanPool.Schoenflies.Bounded
public import Tengoku.LeanPool.LeanPool.Schoenflies.Graph.Degree

/-!
# Plane graphs

There is no `PlaneGraph` type. A plane graph is an abstract `G : Graph Plane β` **together
with** a drawing `drawing : β → ℝ → Plane`, related by `IsDrawing G drawing`. The abstract
graph stays itself, so every combinatorial theorem of `Schoenflies/Graph/` applies with
nothing to project through, and "a plane graph realises an abstract finite graph" is true by
construction rather than by a theorem. Bundling would put a record projection inside every
combinatorial citation.

The vertices being plane points is what makes the definition short: that the vertices are
distinct is not a clause, it is what `V(G) : Set Plane` already means.

`IsDrawing` has three clauses. Each edge is drawn by an injective continuous parametrization on
`[0, 1]` whose endpoint values are the two ends of that edge; an edge's arc meets the vertex set
only at those two ends; and two distinct edges meet only at vertices incident with both. The
second and third are the blueprint's "distinct edges of a plane graph meet only at shared
vertices", split so that `unique_edge_at` — away from the vertices a point of the drawing lies
on exactly one edge — falls out directly. That corollary is the form the polygonal overlay
wants.

The first clause names the *parametrization*, not merely its image. The weaker reading — "the
point set of an edge is an arc between its ends" — suffices for everything about faces, and
fails for the polygonal redrawing, which must speak of the last parameter at which an edge is
inside a given square. `edge_isArcBetween` recovers the weaker reading, so consumers needing
only that are unaffected.

## Blueprint

* `IsDrawing` — a plane graph, as an abstract graph plus a drawing.
* `IsDrawing.edge_param`, `IsDrawing.edge_isArcBetween` — the parametrization, and its image.
* `IsDrawing.arcs_meet_at_vertex`, `IsDrawing.unique_edge_at` — distinct edges meet only at
  shared vertices; away from the vertices, a point lies on exactly one edge.
* `pointSet`, `IsDrawing.isCompact_pointSet`, `exterior`, `isOpen_exterior` — what a plane
  graph occupies, and the open set its faces live in.
* `face` — the component of the exterior through a point off the drawing. Named by a point
  rather than indexed, so no face has to be produced before it is spoken about.
-/

@[expose] public section

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} {base : Plane}

/-- The point set of a single edge: the image of its parametrization on `[0, 1]`. -/
def edgeArc (drawing : β → ℝ → Plane) (e : β) : Set Plane := drawing e '' I

/-- A drawing of an abstract graph in the plane.

The vertices are already plane points, so a drawing only has to say how the edges run. -/
structure IsDrawing (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop where
  /-- Each edge is drawn by an injective continuous parametrization on `[0, 1]` whose two
  endpoints are the ends of that edge.

  This says more than "the point set `edgeArc drawing e` is an arc between the ends". That
  weaker clause makes two drawings with the same point sets indistinguishable, which is fine
  for the face theory and useless for the redrawing argument: "the last parameter at which
  this edge is inside the square at `v`" is meaningless unless `drawing e` is itself the
  parametrization. `edge_isArcBetween` below recovers the weaker statement.

  Stated orientation-free — `G.IsLink e (drawing e 0) (drawing e 1)` — because `IsLink` is
  symmetric, so pinning `drawing e 0` to a *named* end of a *given* link would force the two
  ends to coincide. -/
  edge_param : ∀ ⦃e⦄, e ∈ E(G) →
    ContinuousOn (drawing e) I ∧ InjOn (drawing e) I ∧ G.IsLink e (drawing e 0) (drawing e 1)

  /-- An edge's arc meets the vertex set only at its own two ends. -/
  vertex_mem_edgeArc : ∀ ⦃e x y v⦄, G.IsLink e x y → v ∈ V(G) → v ∈ edgeArc drawing e →
    v = x ∨ v = y
  /-- Two distinct edges meet only at vertices incident with both. -/
  edge_inter : ∀ ⦃e f : β⦄, e ∈ E(G) → f ∈ E(G) → e ≠ f →
    ∀ ⦃p⦄, p ∈ edgeArc drawing e → p ∈ edgeArc drawing f →
      p ∈ V(G) ∧ G.Inc e p ∧ G.Inc f p

namespace IsDrawing

/-- The point set of an edge is an arc between its two ends — the weaker reading of
`edge_param`, and the one the face theory uses.
@isnad1 id=isarcbet.2h6v.s5.3c36feb49181 from=translated src=- shape=b20c510b vocab=a6618943
-/
theorem edge_isArcBetween (h : IsDrawing G drawing) ⦃e x y⦄ (hl : G.IsLink e x y) :
    IsArcBetween (edgeArc drawing e) x y := by
  obtain ⟨hc, hi, hlink⟩ := h.edge_param hl.edge_mem
  have base : IsArcBetween (edgeArc drawing e) (drawing e 0) (drawing e 1) :=
    ⟨drawing e, hc, hi, rfl, rfl, rfl⟩
  rcases hl.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact base
  · exact base.reverse

/--
@isnad1 id=isarc.2h4v.s5.fccd52b7331f from=translated src=- shape=0bf93a2f vocab=924fc14f
-/
theorem isArc_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsArc (edgeArc drawing e) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  exact (h.edge_isArcBetween hxy).isArc

/--
@isnad1 id=iscompac.2h4v.s6.a22f54ece7a5 from=translated src=- shape=162c9a3d vocab=14e1d615
-/
theorem isCompact_edgeArc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G)) :
    IsCompact (edgeArc drawing e) := (h.isArc_edgeArc he).isCompact

/-- The blueprint's "distinct edges of a plane graph meet only at shared vertices".
@isnad1 id=mem.6h6v.s6.563d33c7f789 from=translated src=- shape=c31669ab vocab=87efddf9
-/
theorem arcs_meet_at_vertex (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hef : e ≠ f) {p : Plane} (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    p ∈ V(G) :=
  (h.edge_inter he hf hef hpe hpf).1

/-- Away from the vertices, a point of the drawing lies on exactly one edge. This is the form
the polygonal overlay wants.
@isnad1 id=eq.6h6v.s6.19fd16d6dbd3 from=translated src=- shape=52da3809 vocab=87efddf9
-/
theorem unique_edge_at (h : IsDrawing G drawing) {e f : β} (he : e ∈ E(G)) (hf : f ∈ E(G))
    {p : Plane} (hpV : p ∉ V(G)) (hpe : p ∈ edgeArc drawing e) (hpf : p ∈ edgeArc drawing f) :
    e = f := by
  by_contra hef
  exact hpV (h.arcs_meet_at_vertex he hf hef hpe hpf)

end IsDrawing

/-! ### What a plane graph occupies -/

/-- The point set of a plane graph: its vertices together with all of its edge arcs. -/
def pointSet (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  V(G) ∪ ⋃ e ∈ E(G), edgeArc drawing e

/--
@isnad1 id=le.0h3v.s4.f66410eedfea from=translated src=- shape=a20442f2 vocab=040fcb84
-/
theorem vertexSet_subset_pointSet : V(G) ⊆ pointSet G drawing := subset_union_left

/--
@isnad1 id=le.1h4v.s5.fb1e1939c628 from=translated src=- shape=dfdbd14c vocab=2df150f0
-/
theorem edgeArc_subset_pointSet {e : β} (he : e ∈ E(G)) :
    edgeArc drawing e ⊆ pointSet G drawing :=
  subset_union_of_subset_right (subset_biUnion_of_mem he) _

/-- A finite plane graph occupies a compact set: finitely many points and finitely many
compact arcs.
@isnad1 id=iscompac.1h3v.s6.2bcbfac373a2 from=translated src=- shape=ac9543de vocab=ad71b38b
-/
theorem IsDrawing.isCompact_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsCompact (pointSet G drawing) := by
  refine (Graph.finite_vertexSet (G := G)).isCompact.union ?_
  exact (Graph.finite_edgeSet (G := G)).isCompact_biUnion fun e he => h.isCompact_edgeArc he

/--
@isnad1 id=isclosed.1h3v.s6.94354e58a836 from=translated src=- shape=ac9543de vocab=2eeefc82
-/
theorem IsDrawing.isClosed_pointSet [G.Finite] (h : IsDrawing G drawing) :
    IsClosed (pointSet G drawing) := h.isCompact_pointSet.isClosed

/-- The exterior of a plane graph: everything the drawing does not occupy. -/
def exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) : Set Plane :=
  (pointSet G drawing)ᶜ

/--
@isnad1 id=isopen.1h3v.s6.d43df0cd3087 from=translated src=- shape=ac9543de vocab=55735072
-/
theorem IsDrawing.isOpen_exterior [G.Finite] (h : IsDrawing G drawing) :
    IsOpen (exterior G drawing) := h.isClosed_pointSet.isOpen_compl

/-- A face of a plane graph, named by a point of the exterior rather than indexed: no face has
to be produced before it can be spoken about. -/
def face (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) : Set Plane :=
  connectedComponentIn (exterior G drawing) base

/--
@isnad1 id=le.0h4v.s4.d4580a935bb1 from=translated src=- shape=11bd4fb1 vocab=c5825406
-/
theorem face_subset_exterior (G : Graph Plane β) (drawing : β → ℝ → Plane) (base : Plane) :
    face G drawing base ⊆ exterior G drawing :=
  connectedComponentIn_subset _ _

/--
@isnad1 id=mem.1h4v.s5.2283b67c747a from=translated src=- shape=404fb1d5 vocab=e5d8d923
-/
theorem mem_face (h : base ∈ exterior G drawing) : base ∈ face G drawing base :=
  mem_connectedComponentIn h

/--
@isnad1 id=isopen.1h4v.s6.84ff262a208a from=translated src=- shape=a6a0ee58 vocab=de54393d
-/
theorem IsDrawing.isOpen_face [G.Finite] (h : IsDrawing G drawing) (base : Plane) :
    IsOpen (face G drawing base) :=
  Schoenflies.Plane.isOpen_connectedComponentIn h.isOpen_exterior

/--
@isnad1 id=isconnec.1h4v.s6.e928dd17011c from=translated src=- shape=ec2acd89 vocab=25e624cd
-/
theorem isConnected_face (h : base ∈ exterior G drawing) :
    IsConnected (face G drawing base) :=
  ⟨⟨base, mem_face h⟩, isPreconnected_connectedComponentIn⟩

/-- Faces partition the exterior: two faces either coincide or are disjoint.
@isnad1 id=or.0h5v.s6.1ce7623c3604 from=translated src=- shape=bcb96ee3 vocab=a7cfc9f7
-/
theorem face_eq_or_disjoint (b c : Plane) :
    face G drawing b = face G drawing c ∨ Disjoint (face G drawing b) (face G drawing c) := by
  by_cases h : (face G drawing b ∩ face G drawing c).Nonempty
  · obtain ⟨z, hzb, hzc⟩ := h
    left
    rw [face, face, connectedComponentIn_eq hzb, connectedComponentIn_eq hzc]
  · right
    exact Set.disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h)

end Graph
