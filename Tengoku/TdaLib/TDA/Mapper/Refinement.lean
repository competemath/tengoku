import Tengoku.TdaLib.TDA.Mapper.Basic
import Tengoku.TdaLib.TDA.Topology.NerveMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Refinement maps of ordinary Mapper complexes

Selected target-cover refinements act on path components and then on the
ordinary nerve.  The resulting vertex maps preserve identity and composition
and may identify Mapper vertices.
-/

namespace TDA.Mapper

open TDA.Topology
open TDA.Simplicial

noncomputable section

universe u v w z

variable {X : Type u} {Y : Type v} {I : Type w} {J : Type z}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The Mapper vertex map induced by a selected refinement of target covers.-/
def mapperMap (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : Refinement U V) : VertexMap (mapper f U) (mapper f V) :=
  nerveMap (componentRefinement f R)

/--
@isnad1 id=eq.0h9v.s7.43a5d5cb2fa4 from=translated src=- shape=8f61b497 vocab=2e9a7816
-/
@[simp]
theorem mapperMap_apply (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : Refinement U V) (a : ComponentIndex f U) :
    mapperMap f R a = (componentRefinement f R).selector a :=
  rfl

/-- A represented component is sent to the class of the same point in the
selected larger inverse image.
@isnad1 id=eq.0h10v.s9.707e8ff94932 from=translated src=- shape=405f5080 vocab=687d1449
-/
@[simp]
theorem mapperMap_mk (f : C(X, Y)) {U : I → Set Y} {V : J → Set Y}
    (R : Refinement U V) (i : I) (x : PullbackSpace f U i) :
    mapperMap f R ⟨i, ZerothHomotopy.mk x⟩ =
      ⟨R.selector i, ZerothHomotopy.mk (refinementInclusion f R i x)⟩ :=
  rfl

/-- The identity selected refinement induces the identity Mapper vertex map.
@isnad1 id=eq.0h5v.s6.3aececaf004f from=translated src=- shape=b7a104d7 vocab=c87bc19c
-/
theorem mapperMap_id (f : C(X, Y)) (U : I → Set Y) :
    mapperMap f (Refinement.id U) = VertexMap.id (mapper f U) := by
  unfold mapperMap
  rw [componentRefinement_id, nerveMap_id]
  rfl

/-- Composition of selected refinements induces composition of Mapper maps.
@isnad1 id=eq.0h11v.s7.eb797ae96408 from=translated src=- shape=acc20e6b vocab=cdabdd3e
-/
theorem mapperMap_comp {K : Type*} (f : C(X, Y))
    {U : I → Set Y} {V : J → Set Y} {W : K → Set Y}
    (R : Refinement U V) (S : Refinement V W) :
    mapperMap f (Refinement.comp R S) =
      VertexMap.comp (mapperMap f R) (mapperMap f S) := by
  unfold mapperMap
  rw [componentRefinement_comp, nerveMap_comp]
  rfl

/-- A bijective relabelling followed by its inverse induces the identity on
the reindexed Mapper complex.
@isnad1 id=eq.0h7v.s8.521dbd7fb4f9 from=translated src=- shape=73a4c299 vocab=781b890c
-/
theorem mapperMap_reindex_comp (f : C(X, Y)) (e : I ≃ J) (U : J → Set Y) :
    VertexMap.comp
        (mapperMap f (reindexRefinement e U))
        (mapperMap f (reindexRefinement_symm e U)) =
      VertexMap.id (mapper f (fun i => U (e i))) := by
  rw [← mapperMap_comp]
  have h : Refinement.comp (reindexRefinement e U)
      (reindexRefinement_symm e U) = Refinement.id (fun i => U (e i)) := by
    apply Refinement.ext
    intro i
    simp [reindexRefinement, reindexRefinement_symm]
  rw [h, mapperMap_id]

/-- The inverse relabelling followed by a bijective relabelling induces the
identity on the original Mapper complex.
@isnad1 id=eq.0h7v.s7.ad327c5c6c72 from=translated src=- shape=3466771a vocab=781b890c
-/
theorem mapperMap_reindex_symm_comp (f : C(X, Y)) (e : I ≃ J) (U : J → Set Y) :
    VertexMap.comp
        (mapperMap f (reindexRefinement_symm e U))
        (mapperMap f (reindexRefinement e U)) =
      VertexMap.id (mapper f U) := by
  rw [← mapperMap_comp]
  have h : Refinement.comp (reindexRefinement_symm e U)
      (reindexRefinement e U) = Refinement.id U := by
    apply Refinement.ext
    intro j
    simp [reindexRefinement, reindexRefinement_symm]
  rw [h, mapperMap_id]

end

end TDA.Mapper
