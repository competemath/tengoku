/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku

/-!
# Geometric triangulations

The faithful statement of "the space `S` admits a finite triangulation": `S` is homeomorphic to
the geometric realization of a finite two-dimensional simplicial complex.

The realization is concrete: for a finite vertex type `V` and a finite family `F` of faces
(3-element vertex sets), `GeometricRealization V F` is the subset of the standard simplex
`stdSimplex ℝ V` consisting of points supported on some face.  This is the classical geometric
realization by barycentric coordinates; it is a compact Hausdorff polyhedron by construction, so
the definition cannot be satisfied by junk witnesses (`Empty` face types, arbitrary `realization`
fields, and so on): the homeomorphism type pins `S` to an actual finite union of geometric
2-simplexes.

Semantic anchors (see `Moise/Countermodels.lean` and the Definition Faithfulness section of
`docs/AUTOFORMALIZATION_GUIDE.md`):

* must-imply: `GeometricTriangulation.compactSpace`, `GeometricTriangulation.t2Space`;
* positive example: the standard 2-simplex triangulates itself;
* non-example: `ℝ` and `ℚ` admit no geometric triangulation (they are not compact).
-/

@[expose] public section

/-- A finite closed cover of a preconnected set has a connected intersection graph.

This is the closed-cover counterpart of `IsPreconnected.transGen_of_iUnion`, whose open-cover
hypothesis is not available for the closed simplexes of a geometric realization.
@isnad1 id=transgen.4h5v.s6.b297a898c237 from=translated src=- shape=63cb599d vocab=c515d0ae
-/
theorem IsPreconnected.transGen_of_finite_iUnion
    {α ι : Type*} [TopologicalSpace α] [Finite ι] {s : ι → Set α}
    (hs : IsPreconnected (⋃ n, s n)) (hs' : ∀ i, IsClosed (s i))
    (i j : ι) (hi : (s i).Nonempty) (hj : (s j).Nonempty) :
    Relation.TransGen (fun a b ↦ (s a ∩ s b).Nonempty) i j := by
  by_contra hij
  let R := fun a b : ι ↦ (s a ∩ s b).Nonempty
  let S : Set ι := {k | Relation.TransGen R i k}
  let U : Set α := ⋃ k ∈ S, s k
  let V : Set α := ⋃ k ∈ Sᶜ, s k
  have hUclosed : IsClosed U := by
    exact Set.toFinite S |>.isClosed_biUnion fun k _ ↦ hs' k
  have hVclosed : IsClosed V := by
    exact Set.toFinite Sᶜ |>.isClosed_biUnion fun k _ ↦ hs' k
  have hsplit : (⋃ n, s n) = U ∪ V := iSup_split s (· ∈ S)
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    simp only [Set.mem_iUnion, exists_prop, Set.mem_compl_iff, U, V] at hxU hxV
    obtain ⟨k, hk, hxk⟩ := hxU
    obtain ⟨l, hl, hxl⟩ := hxV
    exact hl (hk.tail ⟨x, hxk, hxl⟩)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  have hiS : i ∈ S := Relation.TransGen.single ⟨a, ha, ha⟩
  have haU : a ∈ U := Set.mem_iUnion₂_of_mem hiS ha
  have hjS : j ∉ S := hij
  have hbV : b ∈ V := Set.mem_iUnion₂_of_mem hjS hb
  have hcover : (⋃ n, s n) ⊆ Vᶜ ∪ Uᶜ := by
    intro x hx
    rcases hsplit.le hx with hxU | hxV
    · exact Or.inl (fun hxV ↦ Set.disjoint_left.mp hUV hxU hxV)
    · exact Or.inr (fun hxU ↦ Set.disjoint_left.mp hUV hxU hxV)
  have hUne : ((⋃ n, s n) ∩ Vᶜ).Nonempty :=
    ⟨a, Set.mem_iUnion_of_mem i ha,
      fun haV ↦ Set.disjoint_left.mp hUV haU haV⟩
  have hVne : ((⋃ n, s n) ∩ Uᶜ).Nonempty :=
    ⟨b, Set.mem_iUnion_of_mem j hb,
      fun hbU ↦ Set.disjoint_left.mp hUV hbU hbV⟩
  obtain ⟨x, hxall, hxV, hxU⟩ := hs Vᶜ Uᶜ
    hVclosed.isOpen_compl hUclosed.isOpen_compl hcover hUne hVne
  rcases hsplit.le hxall with hxU' | hxV'
  · exact hxU hxU'
  · exact hxV hxV'

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-!
### Barycentric coordinates on the standard simplex

Mathlib replaced the set-valued `stdSimplex 𝕜 ι : Set (ι → 𝕜)` by the bundled
`Convexity.StdSimplex`, whose elements carry a `Finsupp` of weights instead of a plain
coordinate function.  Every complex in this development parametrizes its faces by honest
barycentric coordinate functions `ι → ℝ`, so the section below keeps the set-valued simplex —
and exactly the slice of its API that this project uses — as a definition of its own.  The
statements and proofs are those of the corresponding Mathlib declarations, which are now
deprecated.
-/

section StandardSimplex

variable (𝕜 : Type*) (ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with
non-negative coordinates with total sum `1`. -/
def stdSimplex : Set (ι → 𝕜) :=
  {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

/--
@isnad1 id=eq.0h2v.s6.e820dc6bf9bc from=translated src=- shape=14c8623e vocab=0704bbe2
-/
theorem stdSimplex_eq_inter :
    stdSimplex 𝕜 ι = (⋂ x, {f : ι → 𝕜 | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} := by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/--
@isnad1 id=convex.0h2v.s5.dff2b1e642cf from=translated src=- shape=61bc31f3 vocab=77fedd07
-/
theorem convex_stdSimplex [IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

variable {ι}

variable {𝕜} in
/-- All values of a function `f ∈ stdSimplex 𝕜 ι` belong to `[0, 1]`.
@isnad1 id=mem.1h4v.s6.090a5aa9b92a from=translated src=- shape=4853f296 vocab=e45e3d8e
-/
theorem mem_Icc_of_mem_stdSimplex [IsOrderedAddMonoid 𝕜] {f : ι → 𝕜}
    (hf : f ∈ stdSimplex 𝕜 ι) (x) : f x ∈ Set.Icc (0 : 𝕜) 1 :=
  ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y _ => hf.1 y) (Finset.mem_univ x)⟩

/-- `stdSimplex 𝕜 ι` is a subset of the unit cube.
@isnad1 id=le.0h2v.s6.34604793a27a from=translated src=- shape=004f934b vocab=ee528c69
-/
theorem stdSimplex_subset_Icc [IsOrderedAddMonoid 𝕜] : stdSimplex 𝕜 ι ⊆ Set.Icc 0 1 := by
  intro f h
  rw [← Set.pi_univ_Icc, Set.univ_pi_eq_iInter, Set.mem_iInter]
  simpa using fun i ↦ mem_Icc_of_mem_stdSimplex h i

variable [DecidableEq ι] [ZeroLEOneClass 𝕜]

/--
@isnad1 id=mem.0h3v.s6.111eb053d3eb from=translated src=- shape=39c98150 vocab=8a91415c
-/
theorem single_mem_stdSimplex (i : ι) : Pi.single i 1 ∈ stdSimplex 𝕜 ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩

end StandardSimplex

section StandardSimplexTopology

variable (𝕜 ι : Type*) [Fintype ι] [TopologicalSpace 𝕜] [Semiring 𝕜] [PartialOrder 𝕜]
  [OrderClosedTopology 𝕜] [ContinuousAdd 𝕜]

/-- `stdSimplex 𝕜 ι` is closed.
@isnad1 id=isclosed.0h2v.s5.3a1eaf165dd4 from=translated src=- shape=40bd7143 vocab=fd7a3cca
-/
theorem isClosed_stdSimplex : IsClosed (stdSimplex 𝕜 ι) := by
  rw [stdSimplex_eq_inter]
  apply IsClosed.inter
  · exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const

/-- `stdSimplex 𝕜 ι` is compact.
@isnad1 id=iscompac.0h2v.s6.5a2bc2b7eb55 from=translated src=- shape=321ab96f vocab=11c99a9a
-/
theorem isCompact_stdSimplex [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] :
    IsCompact (stdSimplex 𝕜 ι) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex 𝕜 ι) (stdSimplex_subset_Icc 𝕜)

/--
@isnad1 id=compacts.0h2v.s6.4846d4920ad5 from=translated src=- shape=7b234417 vocab=458d4e21
-/
instance stdSimplex.instCompactSpace_coe [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] :
    CompactSpace (stdSimplex 𝕜 ι) :=
  isCompact_iff_compactSpace.mp <| isCompact_stdSimplex 𝕜 _

end StandardSimplexTopology

namespace stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S]
  {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

@[macro_inline]
instance : FunLike (stdSimplex S X) X S where
  coe s := s.val
  coe_injective := by aesop

/--
@isnad1 id=eq.1h4v.s6.6b3807519afc from=translated src=- shape=139bbf70 vocab=69efe2fa
-/
@[ext high]
lemma ext {s t : stdSimplex S X} (h : (s : X → S) = t) : s = t := by
  ext : 1
  assumption

/--
@isnad1 id=le.0h4v.s6.c7268ea49703 from=translated src=- shape=c93d5fa6 vocab=d671feb8
-/
@[simp] lemma zero_le (s : stdSimplex S X) (x : X) : 0 ≤ s x := s.2.1 x

/--
@isnad1 id=eq.0h3v.s6.ce1c65bef834 from=translated src=- shape=41b1565e vocab=dc0061d1
-/
@[simp] lemma sum_eq_one (s : stdSimplex S X) : ∑ x, s x = 1 := s.2.2

/--
@isnad1 id=eq.0h2v.s7.c7148ffab999 from=translated src=- shape=6d3a6bee vocab=9b9e3503
-/
@[simp] lemma add_eq_one (s : stdSimplex S (Fin 2)) : s 0 + s 1 = 1 := by
  simpa only [Fin.sum_univ_two] using sum_eq_one s

section

variable [IsOrderedRing S]

/--
@isnad1 id=le.0h4v.s6.aa573ac82cba from=translated src=- shape=adbc3a8c vocab=acf09193
-/
@[simp] lemma le_one (s : stdSimplex S X) (x : X) : s x ≤ 1 := by
  rw [← sum_eq_one s]
  exact Finset.single_le_sum (by simp) (by simp)

/--
@isnad1 id=le.0h4v.s7.e957b743f3e1 from=translated src=- shape=0b402448 vocab=e953061a
-/
lemma image_linearMap (f : X → Y) :
    Set.image (FunOnFinite.linearMap S S f) (stdSimplex S X) ⊆ stdSimplex S Y := by
  classical
  rintro _ ⟨s, ⟨hs₀, hs₁⟩, rfl⟩
  refine ⟨fun y ↦ ?_, ?_⟩
  · rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (by aesop)
  · simp only [FunOnFinite.linearMap_apply_apply, ← hs₁]
    exact Finset.sum_fiberwise Finset.univ f s

/-- The map `stdSimplex S X → stdSimplex S Y` that is induced by a map `f : X → Y`. -/
noncomputable def map (f : X → Y) (s : stdSimplex S X) : stdSimplex S Y :=
  ⟨FunOnFinite.linearMap S S f s, image_linearMap f (by aesop)⟩

/--
@isnad1 id=eq.0h5v.s7.49149f2ad865 from=translated src=- shape=6513790d vocab=9871f327
-/
@[simp] lemma map_coe (f : X → Y) (s : stdSimplex S X) :
    ⇑(map f s) = FunOnFinite.linearMap S S f s := rfl

/--
@isnad1 id=eq.0h3v.s5.71d31250d0ca from=translated src=- shape=eae5a4b1 vocab=72703d69
-/
@[simp] lemma map_id_apply (x : stdSimplex S X) : map id x = x := by
  aesop

/--
@isnad1 id=eq.0h7v.s6.9b4c389844ec from=translated src=- shape=207c94e1 vocab=5ef12716
-/
lemma map_comp_apply (f : X → Y) (g : Y → Z) (x : stdSimplex S X) :
    map g (map f x) = map (g.comp f) x := by
  ext
  simp [FunOnFinite.linearMap_comp]

/-- The vertex corresponding to `x : X` in `stdSimplex S X`. -/
abbrev vertex [DecidableEq X] (x : X) : stdSimplex S X :=
  ⟨Pi.single x 1, single_mem_stdSimplex S x⟩

/--
@isnad1 id=eq.0h3v.s6.7df2fd29d576 from=translated src=- shape=c4329908 vocab=aa1c4e89
-/
@[simp] lemma vertex_coe [DecidableEq X] (x : X) :
    ⇑(vertex (S := S) x) = Pi.single x 1 := rfl

/--
@isnad1 id=eq.0h5v.s6.cc53bace0d8d from=translated src=- shape=9b0a7cec vocab=4d601ba1
-/
@[simp] lemma map_vertex [DecidableEq X] [DecidableEq Y] (f : X → Y) (x : X) :
    map (S := S) f (vertex x) = vertex (f x) := by
  aesop

/--
@isnad1 id=continuo.0h4v.s7.a914f2048976 from=translated src=- shape=5f34c7ea vocab=1e4d6d92
-/
lemma continuous_map [TopologicalSpace S] [IsTopologicalSemiring S] (f : X → Y) :
    Continuous (map (S := S) f) :=
  Continuous.subtype_mk ((FunOnFinite.continuous_linearMap S S f).comp continuous_induced_dom) _

/--
@isnad1 id=injectiv.0h2v.s5.a0843cccf538 from=translated src=- shape=ce10e8cd vocab=20885c55
-/
lemma vertex_injective [Nontrivial S] [DecidableEq X] :
    Function.Injective (vertex (S := S) (X := X)) := by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [Pi.single_eq_of_ne this] at h

end

end stdSimplex

/-- The geometric realization of a finite family `F` of faces on a finite vertex type `V`: the
points of the standard simplex on `V` whose support lies inside some face of `F`.  For a face `t`
this carves out the geometric simplex spanned by `t`, so the realization is the finite union of
the geometric simplexes of `F`, glued along shared barycentric-coordinate faces. -/
def GeometricRealization (V : Type*) [Fintype V] (F : Finset (Finset V)) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∃ t ∈ F, ∀ v ∉ t, x v = 0}

/-- The geometric simplex carried by one finite set of vertices. -/
def GeometricFace (V : Type*) [Fintype V] (t : Finset V) : Set (V → ℝ) :=
  {x | x ∈ stdSimplex ℝ V ∧ ∀ v ∉ t, x v = 0}

namespace GeometricFace

variable {V : Type*} [Fintype V] [DecidableEq V]

end GeometricFace

namespace GeometricRealization

variable {V : Type*} [Fintype V] {F : Finset (Finset V)}

/--
@isnad1 id=le.0h2v.s4.1ed9a201fca7 from=translated src=- shape=c886a842 vocab=6c9647f9
-/
theorem subset_stdSimplex : GeometricRealization V F ⊆ stdSimplex ℝ V :=
  fun _ hx => hx.1

/--
@isnad1 id=isclosed.0h2v.s4.3ea21dfc784e from=translated src=- shape=c912e23a vocab=ba93f72b
-/
theorem isClosed : IsClosed (GeometricRealization V F) := by
  have hrepr : GeometricRealization V F =
      stdSimplex ℝ V ∩ ⋃ t ∈ F, {x : V → ℝ | ∀ v ∉ t, x v = 0} := by
    ext x
    simp [GeometricRealization, Set.mem_iUnion]
  rw [hrepr]
  refine (isClosed_stdSimplex ℝ V).inter ?_
  refine Set.Finite.isClosed_biUnion F.finite_toSet ?_
  intro t _
  have hInter : {x : V → ℝ | ∀ v ∉ t, x v = 0} =
      ⋂ v ∈ {v : V | v ∉ t}, {x : V → ℝ | x v = 0} := by
    ext x
    simp
  rw [hInter]
  exact isClosed_biInter fun v _ => isClosed_eq (continuous_apply v) continuous_const

/--
@isnad1 id=iscompac.0h2v.s4.16b572df8cc5 from=translated src=- shape=c912e23a vocab=e9b92ef1
-/
theorem isCompact : IsCompact (GeometricRealization V F) :=
  (isCompact_stdSimplex ℝ V).of_isClosed_subset isClosed subset_stdSimplex

instance : CompactSpace (GeometricRealization V F) :=
  isCompact_iff_compactSpace.mp isCompact

/-- The realization of the empty face family is empty. -/
theorem eq_empty_of_no_faces : GeometricRealization V (∅ : Finset (Finset V)) = ∅ := by
  ext x
  simp [GeometricRealization]

instance : IsEmpty (GeometricRealization V (∅ : Finset (Finset V))) :=
  Set.isEmpty_coe_sort.mpr eq_empty_of_no_faces

end GeometricRealization

namespace TriangleFamily

variable {Vertex : Type*} [DecidableEq Vertex]

/-- A listed maximal face of a finite triangle family. -/
abbrev Face (faces : Finset (Finset Vertex)) :=
  {t : Finset Vertex // t ∈ faces}

/-- The two-vertex faces occurring in a finite triangle family. -/
def edges (faces : Finset (Finset Vertex)) : Finset (Finset Vertex) :=
  faces.biUnion fun t => t.powersetCard 2

/-- Two listed triangles are dual-adjacent when they share a two-vertex face. -/
def FaceAdjacent (faces : Finset (Finset Vertex)) (f g : Face faces) : Prop :=
  ∃ e : Finset Vertex, e.card = 2 ∧ e ⊆ f.1 ∧ e ⊆ g.1

/-- Two listed triangles are adjacent at `v` when they share a two-vertex face containing `v`.

Unlike `FaceAdjacent`, this relation remembers the vertex star in which the adjacency step
occurs. -/
def FaceAdjacentAtVertex (faces : Finset (Finset Vertex)) (v : Vertex)
    (f g : Face faces) : Prop :=
  ∃ e : Finset Vertex, e.card = 2 ∧ v ∈ e ∧ e ⊆ f.1 ∧ e ⊆ g.1

/-- Two listed triangles meet when their vertex sets have a common vertex. -/
def FaceIntersects (faces : Finset (Finset Vertex)) (f g : Face faces) : Prop :=
  (f.1 ∩ g.1).Nonempty

omit [DecidableEq Vertex] in
/--
@isnad1 id=faceadja.1h4v.s4.8bd1591a2436 from=translated src=- shape=d9ad36cf vocab=a3fca3d9
-/
theorem faceAdjacent_symm {faces : Finset (Finset Vertex)} {f g : Face faces}
    (h : FaceAdjacent faces f g) : FaceAdjacent faces g f := by
  rcases h with ⟨e, hecard, hef, heg⟩
  exact ⟨e, hecard, heg, hef⟩

omit [DecidableEq Vertex] in
/-- The right endpoint of a fixed-vertex adjacency step contains the fixed vertex.
@isnad1 id=mem.1h5v.s5.d7ac3c070e9f from=translated src=- shape=e9085754 vocab=788b9f49
-/
theorem mem_right_of_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (h : FaceAdjacentAtVertex faces v f g) : v ∈ g.1 := by
  rcases h with ⟨e, _hecard, hve, _hef, heg⟩
  exact heg hve

/-- Faces in different dual components share at most one vertex.
@isnad1 id=le.1h4v.s6.065fd479ac2c from=translated src=- shape=9be82ce5 vocab=728b3ed1
-/
theorem card_inter_le_one_of_not_faceAdjacent
    {faces : Finset (Finset Vertex)} {f g : Face faces}
    (h : ¬ FaceAdjacent faces f g) :
    (f.1 ∩ g.1).card ≤ 1 := by
  by_contra hcard
  have htwo : 2 ≤ (f.1 ∩ g.1).card := by omega
  obtain ⟨e, heSub, heCard⟩ := Finset.exists_subset_card_eq htwo
  apply h
  exact ⟨e, heCard, heSub.trans Finset.inter_subset_left,
    heSub.trans Finset.inter_subset_right⟩

omit [DecidableEq Vertex] in
/-- Every endpoint reached from a face containing `v` through fixed-vertex adjacency still
contains `v`.
@isnad1 id=mem.2h5v.s6.3275dfd7b5b8 from=translated src=- shape=83fe5107 vocab=22d79b3d
-/
theorem mem_of_reflTransGen_faceAdjacentAtVertex
    {faces : Finset (Finset Vertex)} {v : Vertex} {f g : Face faces}
    (hvf : v ∈ f.1)
    (h : Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g) :
    v ∈ g.1 := by
  induction h with
  | refl => exact hvf
  | tail _h hstep _ih => exact mem_right_of_faceAdjacentAtVertex hstep

/-- Every two listed triangles are connected by a finite chain of shared edges. -/
def IsDualConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ f g : Face faces, Relation.ReflTransGen (FaceAdjacent faces) f g

/-- Every pair of triangles incident to one vertex can be joined through shared edges.

For a triangulated surface this is the local connectedness assertion carried by the link of the
vertex. This compatibility predicate does not require its intermediate faces to remain incident
to that vertex; use `IsStrongVertexStarConnected` when that fixed-star invariant is needed. -/
def IsVertexStarConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ (v : Vertex) (f g : Face faces), v ∈ f.1 → v ∈ g.1 →
    Relation.ReflTransGen (FaceAdjacent faces) f g

/-- Every pair of triangles incident to one vertex can be joined by a chain whose every adjacency
step shares an edge containing that same vertex. -/
def IsStrongVertexStarConnected (faces : Finset (Finset Vertex)) : Prop :=
  ∀ (v : Vertex) (f g : Face faces), v ∈ f.1 → v ∈ g.1 →
    Relation.ReflTransGen (FaceAdjacentAtVertex faces v) f g

section Geometric

variable [Fintype Vertex]

end Geometric

/-- Regard a face of a subfamily as a face of a larger family. -/
def faceOfSubset {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces') :
    Face faces → Face faces' :=
  fun f => ⟨f.1, h f.2⟩

omit [DecidableEq Vertex] in
/--
@isnad1 id=eq.1h4v.s6.5286b7bee859 from=translated src=- shape=2f406885 vocab=dbf17765
-/
@[simp]
theorem faceOfSubset_val {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces')
    (f : Face faces) : (faceOfSubset h f).1 = f.1 :=
  rfl

omit [DecidableEq Vertex] in
/--
@isnad1 id=faceadja.2h5v.s5.38d00b9da613 from=translated src=- shape=cee582a1 vocab=4702cd66
-/
theorem faceAdjacent_faceOfSubset {faces faces' : Finset (Finset Vertex)}
    (h : faces ⊆ faces') {f g : Face faces} (hfg : FaceAdjacent faces f g) :
    FaceAdjacent faces' (faceOfSubset h f) (faceOfSubset h g) := by
  rcases hfg with ⟨e, hecard, hef, heg⟩
  exact ⟨e, hecard, hef, heg⟩

omit [DecidableEq Vertex] in
/--
@isnad1 id=refltran.2h5v.s6.c0318ad35c58 from=translated src=- shape=826a6efa vocab=295aaacd
-/
theorem reflTransGen_faceAdjacent_faceOfSubset
    {faces faces' : Finset (Finset Vertex)} (h : faces ⊆ faces') {f g : Face faces}
    (hfg : Relation.ReflTransGen (FaceAdjacent faces) f g) :
    Relation.ReflTransGen (FaceAdjacent faces') (faceOfSubset h f) (faceOfSubset h g) := by
  induction hfg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _hab hbc ih =>
      exact ih.tail (faceAdjacent_faceOfSubset h hbc)

/-- Two dual-connected face families with a cross-adjacent pair have dual-connected union.
@isnad1 id=isdualco.3h5v.s6.b969977dfb89 from=translated src=- shape=077ae4be vocab=799e964b
-/
theorem isDualConnected_union {left right : Finset (Finset Vertex)}
    (hleft : IsDualConnected left) (hright : IsDualConnected right)
    (fleft : Face left) (fright : Face right)
    (hcross : FaceAdjacent (left ∪ right)
      (faceOfSubset Finset.subset_union_left fleft)
      (faceOfSubset Finset.subset_union_right fright)) :
    IsDualConnected (left ∪ right) := by
  intro f g
  rcases Finset.mem_union.mp f.2 with hf | hf <;>
    rcases Finset.mem_union.mp g.2 with hg | hg
  · let f' : Face left := ⟨f.1, hf⟩
    let g' : Face left := ⟨g.1, hg⟩
    have hpath := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft f' g')
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face left := ⟨f.1, hf⟩
    let g' : Face right := ⟨g.1, hg⟩
    have hfirst := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft f' fleft)
    have hlast := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright fright g')
    have hpath := (hfirst.tail hcross).trans hlast
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face right := ⟨f.1, hf⟩
    let g' : Face left := ⟨g.1, hg⟩
    have hfirst := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright f' fright)
    have hlast := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_left (hleft fleft g')
    have hpath := (hfirst.tail (faceAdjacent_symm hcross)).trans hlast
    simpa [f', g', faceOfSubset] using hpath
  · let f' : Face right := ⟨f.1, hf⟩
    let g' : Face right := ⟨g.1, hg⟩
    have hpath := reflTransGen_faceAdjacent_faceOfSubset (faces' := left ∪ right)
      Finset.subset_union_right (hright f' g')
    simpa [f', g', faceOfSubset] using hpath

/-- A face from each family shares a genuine two-vertex edge in the union family. -/
def HasCrossEdge (left right : Finset (Finset Vertex)) : Prop :=
  ∃ (fleft : Face left) (fright : Face right),
      FaceAdjacent (left ∪ right)
        (faceOfSubset Finset.subset_union_left fleft)
        (faceOfSubset Finset.subset_union_right fright)

/-- Two dual-connected face families with a shared cross-edge have dual-connected union.
@isnad1 id=isdualco.3h3v.s5.ffcb786a22fc from=translated src=- shape=4a3dda75 vocab=7405fc70
-/
theorem isDualConnected_union_of_hasCrossEdge
    {left right : Finset (Finset Vertex)}
    (hleft : IsDualConnected left) (hright : IsDualConnected right)
    (hcross : HasCrossEdge left right) :
    IsDualConnected (left ∪ right) := by
  rcases hcross with ⟨fleft, fright, hcross⟩
  exact isDualConnected_union hleft hright fleft fright hcross

omit [DecidableEq Vertex] in
/-- A face family consisting of one triangle is dual-connected.
@isnad1 id=isdualco.0h2v.s4.40e94ac0523a from=translated src=- shape=cb0303a9 vocab=a22065f4
-/
theorem isDualConnected_singleton (face : Finset Vertex) :
    IsDualConnected {face} := by
  intro f g
  have hfg : f = g := by
    apply Subtype.ext
    exact (Finset.mem_singleton.mp f.2).trans (Finset.mem_singleton.mp g.2).symm
  subst g
  exact Relation.ReflTransGen.refl

/-- Adding a triangle along an edge of a dual-connected family preserves dual connectivity.
@isnad1 id=isdualco.2h4v.s7.89cfa01daa68 from=translated src=- shape=d236fa87 vocab=07afad03
-/
theorem isDualConnected_insert {faces : Finset (Finset Vertex)}
    (hfaces : IsDualConnected faces) (face : Finset Vertex) (anchor : Face faces)
    (hcross : FaceAdjacent (insert face faces)
      ⟨face, Finset.mem_insert_self face faces⟩
      (faceOfSubset (Finset.subset_insert face faces) anchor)) :
    IsDualConnected (insert face faces) := by
  apply isDualConnected_union_of_hasCrossEdge
    (isDualConnected_singleton face) hfaces
  refine ⟨⟨face, Finset.mem_singleton_self face⟩, anchor, ?_⟩
  simpa [faceOfSubset] using hcross

/-- Incidence conditions making a finite family of triangles a connected pseudomanifold with
boundary: it is nonempty, no edge has valence above two, and its dual graph is connected. -/
structure SurfaceIncidence (faces : Finset (Finset Vertex)) : Prop where
  faces_nonempty : faces.Nonempty
  edge_valence_le_two :
    ∀ e ∈ edges faces, (faces.filter fun t => e ⊆ t).card ≤ 2
  dual_connected : IsDualConnected faces

end TriangleFamily

/-- A finite triangulation of the topological space `S` by geometric 2-simplexes: a finite vertex
type, a finite family of 3-element faces, and a homeomorphism from the geometric realization of
that family onto `S`.

There is no separate `realization` field to weaken: the realization is computed from the
combinatorial data, so a `GeometricTriangulation S` exists only when `S` really is a finite
two-dimensional polyhedron. -/
structure GeometricTriangulation (S : Type*) [TopologicalSpace S] where
  /-- The (finite) vertex type of the triangulation. -/
  Vertex : Type
  /-- The vertex type is finite. -/
  [vertexFintype : Fintype Vertex]
  /-- Vertices have decidable equality. -/
  [vertexDecidableEq : DecidableEq Vertex]
  /-- The faces: each is a set of vertices spanning a geometric 2-simplex. -/
  faces : Finset (Finset Vertex)
  /-- Every face has exactly three vertices, so the complex is purely two-dimensional. -/
  faces_card : ∀ t ∈ faces, t.card = 3
  /-- The geometric realization of the face family is homeomorphic to `S`. -/
  homeo : GeometricRealization Vertex faces ≃ₜ S

attribute [instance] GeometricTriangulation.vertexFintype
attribute [instance] GeometricTriangulation.vertexDecidableEq

namespace GeometricTriangulation

variable {S : Type*} [TopologicalSpace S] (T : GeometricTriangulation S)

/-- Surface-incidence certificate for a faithful geometric triangulation. -/
abbrev SurfaceIncidence : Prop :=
  TriangleFamily.SurfaceIncidence T.faces

/-- The realization of the triangulation, as a polyhedron in barycentric coordinates. -/
abbrev realization : Set (T.Vertex → ℝ) :=
  GeometricRealization T.Vertex T.faces

include T in
/-- Must-imply anchor: a finitely triangulated space is compact.  This is what rules out the
empty/junk triangulations that satisfied the previous `SurfaceTriangulable` predicate.
@isnad1 id=compacts.0h2v.s3.cb774874c7f8 from=translated src=- shape=c612a321 vocab=bf2eceab
-/
theorem compactSpace : CompactSpace S :=
  Homeomorph.compactSpace T.homeo

include T in
/-- Must-imply anchor: a finitely triangulated space is Hausdorff (the realization is a subspace
of a finite product of lines).
@isnad1 id=t2space.0h2v.s3.089916ccea53 from=translated src=- shape=c612a321 vocab=f72071e3
-/
theorem t2Space : T2Space S :=
  Topology.IsEmbedding.t2Space (Homeomorph.isEmbedding T.homeo.symm)

/-- A triangulation of a nonempty space has at least one two-dimensional face.
@isnad1 id=nonempty.0h2v.s4.3fb8925a2df0 from=translated src=- shape=883cfd4e vocab=6b3609a5
-/
theorem faces_nonempty [Nonempty S] : T.faces.Nonempty := by
  let s : S := Classical.choice inferInstance
  rcases (T.homeo.symm s).2.2 with ⟨t, ht, _⟩
  exact ⟨t, ht⟩

/-- The edges of the triangulation: the 2-element subsets of its faces. -/
def edges : Finset (Finset T.Vertex) :=
  T.faces.biUnion fun t => t.powersetCard 2

/--
@isnad1 id=eq.1h3v.s6.22242403b92d from=translated src=- shape=a7af7210 vocab=54d876be
-/
theorem card_of_mem_edges {e : Finset T.Vertex} (he : e ∈ T.edges) : e.card = 2 := by
  rcases Finset.mem_biUnion.mp he with ⟨t, _ht, het⟩
  exact (Finset.mem_powersetCard.mp het).2

/--
@isnad1 id=mem.3h4v.s7.0d8c9db117cc from=translated src=- shape=7bcaf29e vocab=70ffca7d
-/
theorem mem_edges_of_subset_face {e t : Finset T.Vertex} (ht : t ∈ T.faces) (het : e ⊆ t)
    (he : e.card = 2) : e ∈ T.edges :=
  Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_powersetCard.mpr ⟨het, he⟩⟩

/-- The edge type of the triangulation. -/
abbrev Edge : Type :=
  {e : Finset T.Vertex // e ∈ T.edges}

/-- The triangle (face) type of the triangulation. -/
abbrev Triangle : Type :=
  {t : Finset T.Vertex // t ∈ T.faces}

/--
@isnad1 id=eq.0h3v.s6.9ebfc5ce166d from=translated src=- shape=b0b14bdc vocab=bc446484
-/
theorem edge_card (e : T.Edge) : e.1.card = 2 :=
  T.card_of_mem_edges e.2

/--
@isnad1 id=eq.0h3v.s6.d748bcafd747 from=translated src=- shape=b0b14bdc vocab=b4842e32
-/
theorem triangle_card (t : T.Triangle) : t.1.card = 3 :=
  T.faces_card t.1 t.2

/-- The chosen first endpoint of an edge. -/
noncomputable def edgeSource (e : T.Edge) : T.Vertex :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose

/-- The chosen second endpoint of an edge. -/
noncomputable def edgeTarget (e : T.Edge) : T.Vertex :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose

/--
@isnad1 id=ne.0h3v.s4.114713960683 from=translated src=- shape=d3ce82ca vocab=5b3dadd6
-/
theorem edgeSource_ne_edgeTarget (e : T.Edge) : T.edgeSource e ≠ T.edgeTarget e :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose_spec.1

/--
@isnad1 id=eq.0h3v.s6.6b9f747b2bd4 from=translated src=- shape=83df96c4 vocab=a98ee1a9
-/
theorem edge_eq_pair (e : T.Edge) : e.1 = {T.edgeSource e, T.edgeTarget e} :=
  (Finset.card_eq_two.mp (T.edge_card e)).choose_spec.choose_spec.2

/--
@isnad1 id=mem.0h3v.s6.8519fd03ced4 from=translated src=- shape=2e26e7e6 vocab=643b11f3
-/
theorem edgeSource_mem (e : T.Edge) : T.edgeSource e ∈ e.1 := by
  rw [T.edge_eq_pair e]
  simp

/--
@isnad1 id=mem.0h3v.s6.8fc57d40cc81 from=translated src=- shape=2e26e7e6 vocab=9f3d6f58
-/
theorem edgeTarget_mem (e : T.Edge) : T.edgeTarget e ∈ e.1 := by
  rw [T.edge_eq_pair e]
  simp

/-- An edge is a boundary edge when it lies in exactly one face. -/
def IsBoundaryEdge (e : T.Edge) : Prop :=
  (T.faces.filter fun t => e.1 ⊆ t).card = 1

end GeometricTriangulation

end ClassificationOfSurfaces
end Topology
end LeanEval
