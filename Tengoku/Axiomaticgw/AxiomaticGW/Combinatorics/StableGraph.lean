/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.CohFT.StableCurve
public import Tengoku.Seed.Data.Finset.Card
public import Tengoku.Seed.Data.Finset.Sort
public import Tengoku.Seed.RingTheory.PiTensorProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stable graphs

A stable graph is represented by a finite vertex type, a finite edge type,
and two branches for every edge. This treats loops and multiple edges without
quotienting half-edges. Legs retain their external labels.

The optional `StableGraphPullbacks` interface records a graph-level boundary
pullback and its invariance under the order in which internal edges are
processed. It extends, rather than strengthens, `StableCurveCohomology`.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- A connected stable graph with externally labelled legs. An edge has two
branches indexed by `Fin 2`; a loop is an edge whose two branches have the
same incident vertex.-/
structure StableGraph (S : Type) [Fintype S] where
  /-- Vertices.-/
  Vertex : Type
  /-- Internal edges.-/
  Edge : Type
  /-- The graph is finite.-/
  [vertexFintype : Fintype Vertex]
  [edgeFintype : Fintype Edge]
  /-- Vertex equality is used to form finite incidence fibres.-/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- Edge equality is used to form complete contraction orders.-/
  [edgeDecidableEq : DecidableEq Edge]
  /-- A connected stable graph has a vertex.-/
  [vertexNonempty : Nonempty Vertex]
  /-- Vertex carrying an external leg.-/
  legVertex : S → Vertex
  /-- Vertex incident to a branch of an internal edge.-/
  endpoint : Edge → Fin 2 → Vertex
  /-- Genus decorating each vertex.-/
  genus : Vertex → ℕ
  /-- Connectedness via unoriented internal edges.-/
  connected : ∀ v w, Relation.ReflTransGen
    (fun x y ↦ ∃ e, (endpoint e 0 = x ∧ endpoint e 1 = y) ∨
      (endpoint e 1 = x ∧ endpoint e 0 = y)) v w
  /-- Vertex stability, with a loop counted twice in the valence.-/
  stable : ∀ v, 3 ≤ 2 * genus v +
    Fintype.card {s : S // legVertex s = v} +
    Fintype.card {p : Edge × Fin 2 // endpoint p.1 p.2 = v}

namespace StableGraph

attribute [instance] vertexFintype edgeFintype vertexDecidableEq
  edgeDecidableEq vertexNonempty

variable {S : Type} [Fintype S]

/-- Internal half-edges are edge branches.-/
abbrev HalfEdge (G : StableGraph S) := G.Edge × Fin 2

/-- The fixed-point-free involution exchanging the two branches of an edge.-/
def mate (G : StableGraph S) : Equiv.Perm G.HalfEdge where
  toFun p := (p.1, Equiv.swap 0 1 p.2)
  invFun p := (p.1, Equiv.swap 0 1 p.2)
  left_inv p := by
    rcases p with ⟨e, i⟩
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨e, i⟩
    fin_cases i <;> rfl

@[simp]
theorem mate_edge (G : StableGraph S) (h : G.HalfEdge) :
    (G.mate h).1 = h.1 := rfl

@[simp]
theorem mate_ne (G : StableGraph S) (h : G.HalfEdge) : G.mate h ≠ h := by
  rcases h with ⟨e, i⟩
  fin_cases i <;>
    simp only [mate, Fin.isValue, Fin.zero_eta, Fin.mk_one, Equiv.coe_fn_mk,
      Equiv.swap_apply_left, Equiv.swap_apply_right, ne_eq, Prod.mk.injEq,
      Fin.one_eq_zero_iff, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, and_false,
      not_false_eq_true]

@[simp]
theorem mate_mate (G : StableGraph S) (h : G.HalfEdge) :
    G.mate (G.mate h) = h := by
  exact G.mate.left_inv h

/-- Labels on the stable-curve factor belonging to a vertex: external legs
and incident internal half-edges.-/
abbrev VertexLabel (G : StableGraph S) (v : G.Vertex) :=
  {s : S // G.legVertex s = v} ⊕
    {h : G.HalfEdge // G.endpoint h.1 h.2 = v}

/-- Valence, counting every branch of a loop.-/
def valence (G : StableGraph S) (v : G.Vertex) : ℕ :=
  Fintype.card {s : S // G.legVertex s = v} +
    Fintype.card {h : G.HalfEdge // G.endpoint h.1 h.2 = v}

theorem card_vertexLabel (G : StableGraph S) (v : G.Vertex) :
    Fintype.card (G.VertexLabel v) = G.valence v := by
  simp only [Fintype.card_sum, valence]

/-- Every vertex decoration determines a stable moduli-space factor.-/
theorem vertex_stable (G : StableGraph S) (v : G.Vertex) :
    StableArity (G.genus v) (G.VertexLabel v) := by
  rw [StableArity, G.card_vertexLabel]
  simpa only [valence, add_assoc] using G.stable v

/-- First Betti number of a connected finite graph.-/
def firstBetti (G : StableGraph S) : ℕ :=
  Fintype.card G.Edge + 1 - Fintype.card G.Vertex

/-- Arithmetic genus: the sum of vertex genera plus the graph's first Betti
number.-/
def totalGenus (G : StableGraph S) : ℕ :=
  (∑ v, G.genus v) + G.firstBetti

/-- Relabel the external legs without changing the underlying decorated
graph.-/
def relabel {T : Type} [Fintype T] (G : StableGraph S) (e : S ≃ T) :
    StableGraph T where
  Vertex := G.Vertex
  Edge := G.Edge
  legVertex := G.legVertex ∘ e.symm
  endpoint := G.endpoint
  genus := G.genus
  connected := G.connected
  stable := by
    intro v
    let legEquiv :
        {t : T // (G.legVertex ∘ e.symm) t = v} ≃
          {s : S // G.legVertex s = v} :=
      { toFun := fun t ↦ ⟨e.symm t.1, t.2⟩
        invFun := fun s ↦ ⟨e s.1, by
          simp only [Function.comp_apply, Equiv.symm_apply_apply, s.2]⟩
        left_inv := fun t ↦ by
          simp only [Function.comp_apply, Equiv.apply_symm_apply,
            Subtype.coe_eta]
        right_inv := fun s ↦ by
          simp only [Equiv.symm_apply_apply, Subtype.coe_eta] }
    rw [Fintype.card_congr legEquiv]
    exact G.stable v

@[simp]
theorem relabel_totalGenus {T : Type} [Fintype T]
    (G : StableGraph S) (e : S ≃ T) :
    (G.relabel e).totalGenus = G.totalGenus := rfl

/-- A complete ordering of the internal edges.-/
structure ContractionOrder (G : StableGraph S) where
  /-- Ordered list of internal edges.-/
  edges : List G.Edge
  /-- No edge is processed twice.-/
  nodup : edges.Nodup
  /-- Every internal edge occurs.-/
  complete : edges.toFinset = Finset.univ

/-- The order supplied by `Finset.univ.toList`.-/
noncomputable def canonicalOrder (G : StableGraph S) : G.ContractionOrder where
  edges := Finset.univ.toList
  nodup := Finset.nodup_toList _
  complete := by simp only [Finset.toList_toFinset]

/-- Any two complete edge orders differ only by a permutation.-/
theorem contractionOrder_perm (G : StableGraph S)
    (o₁ o₂ : G.ContractionOrder) : o₁.edges.Perm o₂.edges := by
  apply List.perm_of_nodup_nodup_toFinset_eq o₁.nodup o₂.nodup
  rw [o₁.complete, o₂.complete]

end StableGraph

/-- The tensor product of the stable-curve cohomologies attached to all
vertices of a stable graph.-/
abbrev StableGraphVertexCohomology
    {R : Type u} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) {S : Type} [Fintype S]
    (G : StableGraph S) :=
  PiTensorProduct R (fun v : G.Vertex ↦
    C.H (G.genus v) (G.VertexLabel v))

/-- Optional graph-level boundary pullbacks. The geometric input is an
ordered construction compatible with permutation of the complete edge list;
the public `pullback` is the resulting canonical order-independent map.-/
structure StableGraphPullbacks
    {R : Type u} [CommRing R] [Algebra ℚ R]
    (C : StableCurveCohomology R) where
  /-- Pullback obtained from one complete ordering of the graph edges.-/
  orderedPullback : ∀ {S : Type} [Fintype S] (G : StableGraph S),
    G.ContractionOrder →
      C.H G.totalGenus S →ₐ[R] StableGraphVertexCohomology C G
  /-- Disjoint gluing squares imply invariance under reordering edges. This
  is kept in the optional geometric package rather than imposed on `C`.-/
  orderedPullback_perm : ∀ {S : Type} [Fintype S]
      (G : StableGraph S) (o₁ o₂ : G.ContractionOrder),
    o₁.edges.Perm o₂.edges → orderedPullback G o₁ = orderedPullback G o₂

namespace StableGraphPullbacks

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {C : StableCurveCohomology R}

/-- Canonical graph pullback, evaluated using the canonical complete edge
order.-/
noncomputable def pullback (P : StableGraphPullbacks C)
    {S : Type} [Fintype S] (G : StableGraph S) :
    C.H G.totalGenus S →ₐ[R] StableGraphVertexCohomology C G :=
  P.orderedPullback G G.canonicalOrder

/-- Every complete contraction order computes the canonical graph pullback.-/
theorem orderedPullback_eq_pullback (P : StableGraphPullbacks C)
    {S : Type} [Fintype S] (G : StableGraph S)
    (o : G.ContractionOrder) :
    P.orderedPullback G o = P.pullback G := by
  apply P.orderedPullback_perm
  exact G.contractionOrder_perm o G.canonicalOrder

/-- In particular, graph pullback is independent of two chosen complete
contraction orders.-/
theorem orderedPullback_eq (P : StableGraphPullbacks C)
    {S : Type} [Fintype S] (G : StableGraph S)
    (o₁ o₂ : G.ContractionOrder) :
    P.orderedPullback G o₁ = P.orderedPullback G o₂ := by
  apply P.orderedPullback_perm
  exact G.contractionOrder_perm o₁ o₂

end StableGraphPullbacks

end AxiomaticGW
