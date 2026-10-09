/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicTopology.SimplicialComplex.Basic
public import Tengoku.Seed.Analysis.Convex.Hull
public import Tengoku.Seed.LinearAlgebra.AffineSpace.Independent
public import Tengoku.Seed.Order.UpperLower.Relative

/-!
# Simplicial complexes

In this file, we define simplicial complexes over `𝕜`-modules.
A (pre-) abstract simplicial complex is a downwards-closed collection of nonempty finite sets,
and a simplicial complex is such a collection identified with simplices
closed by inclusion (of vertices) and intersection (of underlying sets)
whose convex hulls "glue nicely", each finite set and its convex hull corresponding respectively
to the vertices and the underlying set of a simplex.

## Main declarations

* `SimplicialComplex 𝕜 E`: A simplicial complex in the `𝕜`-module `E`.
* `SimplicialComplex.vertices`: The zero-dimensional faces of a simplicial complex.
* `SimplicialComplex.facets`: The maximal faces of a simplicial complex.

## Notation

`K ≤ L` means that the faces of `K` are faces of `L`.

## Implementation notes

"glue nicely" usually means that the intersection of two faces (as sets in the ambient space) is a
face. Given that we store the vertices, not the faces, this would be a bit awkward to spell.
Instead, `SimplicialComplex.inter_subset_convexHull` is an equivalent condition which works on the
vertices.

## TODO

Simplicial complexes can be generalized to affine spaces once `ConvexHull` has been ported.
-/

@[expose] public section


open Finset Set

variable (𝕜 E : Type*) [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Geometry

-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
/-- A simplicial complex in a `𝕜`-module is a collection of simplices which glue nicely together.
Note that the textbook meaning of "glue nicely" is given in
`Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull`. It is mostly useless, as
`Geometry.SimplicialComplex.convexHull_inter_convexHull` is enough for all purposes. -/
@[ext]
structure SimplicialComplex extends PreAbstractSimplicialComplex E where
  /-- the vertices in each face are affine independent: this is an implementation detail -/
  indep : ∀ {s}, s ∈ faces → AffineIndependent 𝕜 ((↑) : s → E)
  inter_subset_convexHull : ∀ {s t}, s ∈ faces → t ∈ faces →
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)

namespace SimplicialComplex

variable {𝕜 E}
variable {K : SimplicialComplex 𝕜 E} {s t : Finset E} {x : E}

/--
@isnad1 id=nonempty.1h4v.s5.03eede8283aa from=seed src=0 shape=c34a14d7 vocab=924d14ce
-/
lemma nonempty_of_mem_faces (hs : s ∈ K.faces) : s.Nonempty :=
  K.isRelLowerSet_faces hs |>.1

/--
@isnad1 id=not.0h3v.s5.af44840b5a33 from=seed src=0 shape=5908dd82 vocab=7aabd753
-/
theorem empty_notMem : ∅ ∉ K.faces :=
  fun h => by simpa using nonempty_of_mem_faces h

/-- The underlying space of a simplicial complex is the union of its faces. -/
def space (K : SimplicialComplex 𝕜 E) : Set E :=
  ⋃ s ∈ K.faces, convexHull 𝕜 (s : Set E)

/--
@isnad1 id=iff.0h4v.s7.9035e2a800c8 from=seed src=0 shape=54ef9c20 vocab=1c1a6510
-/
theorem mem_space_iff : x ∈ K.space ↔ ∃ s ∈ K.faces, x ∈ convexHull 𝕜 (s : Set E) := by
  simp [space]

/--
@isnad1 id=le.1h4v.s7.69f79d5417d2 from=seed src=0 shape=d76dc70f vocab=2dbc01ec
-/
theorem convexHull_subset_space (hs : s ∈ K.faces) : convexHull 𝕜 s ⊆ K.space := by
  convert! subset_biUnion_of_mem hs
  rfl

/--
@isnad1 id=le.1h4v.s6.a2a465bc24d0 from=seed src=0 shape=9bb95354 vocab=db30b06c
-/
protected theorem subset_space (hs : s ∈ K.faces) : (s : Set E) ⊆ K.space :=
  (subset_convexHull 𝕜 _).trans <| convexHull_subset_space hs

/--
@isnad1 id=eq.2h5v.s8.5fb125dd9304 from=seed src=0 shape=0674b758 vocab=250f6743
-/
theorem convexHull_inter_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 s ∩ convexHull 𝕜 t = convexHull 𝕜 (s ∩ t : Set E) :=
  (K.inter_subset_convexHull hs ht).antisymm <|
    subset_inter (convexHull_mono Set.inter_subset_left) <|
      convexHull_mono Set.inter_subset_right

/--
@isnad1 id=mem.3h5v.s6.d51a13fd886c from=seed src=0 shape=37be61c7 vocab=566b19b1
-/
theorem down_closed {s t} (hs : s ∈ K.faces) (hst : t ⊆ s) (ht : t.Nonempty) : t ∈ K.faces :=
  (K.isRelLowerSet_faces hs).2 hst ht

/-- The conclusion is the usual meaning of "glue nicely" in textbooks. It turns out to be quite
unusable, as it's about faces as sets in space rather than simplices. Further, additional structure
on `𝕜` means the only choice of `u` is `s ∩ t` (but it's hard to prove).
@isnad1 id=or.2h5v.s8.71bee67480db from=seed src=0 shape=37c90268 vocab=e88d0966
-/
theorem disjoint_or_exists_inter_eq_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    Disjoint (convexHull 𝕜 (s : Set E)) (convexHull 𝕜 t) ∨
      ∃ u ∈ K.faces, convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 t = convexHull 𝕜 u := by
  classical
  by_contra! h
  rw [not_disjoint_iff_nonempty_inter] at h
  refine h.2 (s ∩ t) (K.down_closed hs inter_subset_left ?_) ?_
  · simpa [← coe_inter] using convexHull_nonempty_iff.1 (h.1.mono (K.inter_subset_convexHull hs ht))
  · rw [coe_inter, convexHull_inter_convexHull hs ht]

/-- Construct a simplicial complex by removing the empty face for you. -/
@[simps]
def ofErase (faces : Set (Finset E)) (indep : ∀ s ∈ faces, AffineIndependent 𝕜 ((↑) : s → E))
    (down_closed : IsLowerSet faces)
    (inter_subset_convexHull : ∀ᵉ (s ∈ faces) (t ∈ faces),
      convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)) :
    SimplicialComplex 𝕜 E where
  faces := faces \ {∅}
  indep hs := indep _ hs.1
  isRelLowerSet_faces := by
    have : faces \ {∅} = {f ∈ faces | f.Nonempty} := by grind
    simpa only [this] using down_closed.isRelLowerSet_sep Finset.Nonempty
  inter_subset_convexHull hs ht := inter_subset_convexHull _ hs.1 _ ht.1

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps]
def ofSubcomplex (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces ⊆ K.faces)
    (down_closed : IsLowerSet faces) : SimplicialComplex 𝕜 E :=
  { faces := faces
    indep := fun hs => K.indep (subset hs)
    isRelLowerSet_faces := K.isRelLowerSet_faces.mono_isLowerSet down_closed subset
    inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull (subset hs) (subset ht) }

/-! ### Vertices -/


/-- The vertices of a simplicial complex are its zero-dimensional faces. -/
def vertices (K : SimplicialComplex 𝕜 E) : Set E :=
  { x | {x} ∈ K.faces }

/--
@isnad1 id=iff.0h4v.s6.f506d0937bce from=seed src=0 shape=10d40160 vocab=6c850302
-/
theorem mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.faces := Iff.rfl

/--
@isnad1 id=eq.0h3v.s6.2ba496a11b95 from=seed src=0 shape=c404e2bf vocab=7316c2e9
-/
theorem vertices_eq : K.vertices = ⋃ k ∈ K.faces, (k : Set E) := by
  ext x
  refine ⟨fun h => mem_biUnion h <| mem_coe.2 <| mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := mem_iUnion₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| mem_coe.1 hx) (singleton_nonempty _)

/--
@isnad1 id=le.0h3v.s5.19139deb7c7a from=seed src=0 shape=6bf452f7 vocab=26045a85
-/
theorem vertices_subset_space : K.vertices ⊆ K.space :=
  vertices_eq.subset.trans <| iUnion₂_mono fun x _ => subset_convexHull 𝕜 (x : Set E)

/--
@isnad1 id=iff.2h5v.s7.4f8fff82e870 from=seed src=0 shape=fea52aff vocab=b1d4b836
-/
theorem vertex_mem_convexHull_iff (hx : x ∈ K.vertices) (hs : s ∈ K.faces) :
    x ∈ convexHull 𝕜 (s : Set E) ↔ x ∈ s := by
  refine ⟨fun h => ?_, fun h => subset_convexHull 𝕜 _ h⟩
  classical
  have h := K.inter_subset_convexHull hx hs ⟨by simp, h⟩
  by_contra H
  rwa [← coe_inter, Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_singleton_right.2 H).symm,
    coe_empty, convexHull_empty] at h

/-- A face is a subset of another one iff its vertices are.
@isnad1 id=iff.2h5v.s7.baf435a522d2 from=seed src=0 shape=f2846ade vocab=332246c4
-/
theorem face_subset_face_iff (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 (s : Set E) ⊆ convexHull 𝕜 ↑t ↔ s ⊆ t :=
  ⟨fun h _ hxs =>
    (vertex_mem_convexHull_iff
          (K.down_closed hs (Finset.singleton_subset_iff.2 hxs) <| singleton_nonempty _) ht).1
      (h (subset_convexHull 𝕜 (E := E) s hxs)),
    convexHull_mono⟩

/-! ### Facets -/


/-- A facet of a simplicial complex is a maximal face. -/
def facets (K : SimplicialComplex 𝕜 E) : Set (Finset E) :=
  { s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t }

/--
@isnad1 id=iff.0h4v.s6.21935b29d923 from=seed src=0 shape=f2ec6601 vocab=ba142cdc
-/
theorem mem_facets : s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → s = t :=
  mem_sep_iff

/--
@isnad1 id=le.0h3v.s5.e2e0b0adfe4a from=seed src=0 shape=6e97ea7e vocab=c2a3e309
-/
theorem facets_subset : K.facets ⊆ K.faces := fun _ hs => hs.1

/--
@isnad1 id=iff.1h4v.s6.5ee4f8a0315e from=seed src=0 shape=0a1beba7 vocab=07a9ae31
-/
theorem not_facet_iff_subface (hs : s ∈ K.faces) : s ∉ K.facets ↔ ∃ t, t ∈ K.faces ∧ s ⊂ t := by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push Not at hs'
    obtain ⟨t, ht⟩ := hs' hs
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (Subset.antisymm ht.2.1 hts)⟩⟩
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (Subset.refl t)

/-!
### The semilattice of simplicial complexes

`K ≤ L` means that `K.faces ⊆ L.faces`.
-/


-- `HasSSubset.SSubset.ne` would be handy here
variable (𝕜 E)

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Min (SimplicialComplex 𝕜 E) :=
  ⟨fun K L =>
    { faces := K.faces ∩ L.faces
      indep := fun hs => K.indep hs.1
      isRelLowerSet_faces := K.isRelLowerSet_faces.inter L.isRelLowerSet_faces
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }⟩

instance : SemilatticeInf (SimplicialComplex 𝕜 E) :=
  { PartialOrder.lift (fun K => K.faces) (fun _ _ => SimplicialComplex.ext) with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ hs => hs.1
    inf_le_right := fun _ _ _ hs => hs.2
    le_inf := fun _ _ _ hKL hKM _ hs => ⟨hKL hs, hKM hs⟩ }

instance hasBot : Bot (SimplicialComplex 𝕜 E) :=
  ⟨{  faces := ∅
      indep := fun hs => (Set.notMem_empty _ hs).elim
      isRelLowerSet_faces := isRelLowerSet_empty
      inter_subset_convexHull := fun hs => (Set.notMem_empty _ hs).elim }⟩

instance : OrderBot (SimplicialComplex 𝕜 E) :=
  { SimplicialComplex.hasBot 𝕜 E with bot_le := fun _ => Set.empty_subset _ }

instance : Inhabited (SimplicialComplex 𝕜 E) :=
  ⟨⊥⟩

variable {𝕜 E}

/--
@isnad1 id=eq.0h2v.s5.d42ef436d5c8 from=seed src=0 shape=18526c25 vocab=610dff14
-/
theorem faces_bot : (⊥ : SimplicialComplex 𝕜 E).faces = ∅ := rfl

/--
@isnad1 id=eq.0h2v.s5.8eaae288c7e7 from=seed src=0 shape=e35fc919 vocab=3a7baff5
-/
theorem space_bot : (⊥ : SimplicialComplex 𝕜 E).space = ∅ :=
  Set.biUnion_empty _

/--
@isnad1 id=eq.0h2v.s5.79190d0d6f89 from=seed src=0 shape=fe2d1c8e vocab=090a6373
-/
theorem facets_bot : (⊥ : SimplicialComplex 𝕜 E).facets = ∅ :=
  eq_empty_of_subset_empty facets_subset

end SimplicialComplex

end Geometry
