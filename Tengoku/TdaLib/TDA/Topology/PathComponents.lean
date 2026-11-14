import Tengoku.Seed.Topology.Connected.PathConnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generic path-component maps and inverse-image inclusions

This module collects topology-level operations on path components. Continuous maps induce
maps on `ZerothHomotopy`; nested target sets induce continuous inclusions between inverse-image
subspaces; and a path inside an inverse image identifies the corresponding subtype path
components.
-/

namespace TDA.Topology

universe u v w

section componentMap

variable {X : Type u} {Z : Type w} {W : Type*}
  [TopologicalSpace X] [TopologicalSpace Z] [TopologicalSpace W]

/-- Path components are mapped by a continuous map (raw map; carrier universes independent).-/
def componentMap (h : C(X, Z)) : ZerothHomotopy X → ZerothHomotopy Z :=
  ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (h x))
    (fun _ _ p => ZerothHomotopy.sound (p.map h.continuous))

/--
@isnad1 id=eq.0h4v.s5.9cf7faf6b784 from=translated src=- shape=73295bc4 vocab=9cbba482
-/
@[simp]
theorem componentMap_mk (h : C(X, Z)) (x : X) :
    componentMap h (ZerothHomotopy.mk x) = ZerothHomotopy.mk (h x) := rfl

/--
@isnad1 id=eq.0h1v.s4.495c4ed5bb99 from=translated src=- shape=3d9ad5e1 vocab=159bdf4a
-/
theorem componentMap_id : componentMap (ContinuousMap.id X) = id := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/--
@isnad1 id=eq.0h5v.s6.5db1fb69477c from=translated src=- shape=38e7f11c vocab=d4475475
-/
theorem componentMap_comp (k : C(Z, W)) (h : C(X, Z)) :
    componentMap (k.comp h) = componentMap k ∘ componentMap h := by
  funext c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

end componentMap

section inverseImage

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The continuous inclusion between inverse-image subspaces of arbitrary nested sets.-/
def preimageSetInclusion (f : C(X, Y)) {A B : Set Y} (hAB : A ⊆ B) :
    C({x : X // f x ∈ A}, {x : X // f x ∈ B}) where
  toFun x := ⟨x.1, hAB x.2⟩
  continuous_toFun := by fun_prop

/--
@isnad1 id=eq.1h6v.s8.4e1841f062e3 from=translated src=- shape=afd08647 vocab=a9c1398f
-/
@[simp]
theorem preimageSetInclusion_apply (f : C(X, Y)) {A B : Set Y} (hAB : A ⊆ B)
    (x : {x : X // f x ∈ A}) : (preimageSetInclusion f hAB x).1 = x.1 := rfl

/-- The raw-set inclusion associated to reflexive containment is the identity map.
@isnad1 id=eq.0h4v.s7.266703bf02a8 from=translated src=- shape=ac2cecd6 vocab=ee2e3a64
-/
theorem preimageSetInclusion_id (f : C(X, Y)) (A : Set Y) :
    preimageSetInclusion f (show A ⊆ A from subset_rfl) =
      ContinuousMap.id {x : X // f x ∈ A} := by
  ext x
  rfl

/-- Raw-set inclusions compose strictly as continuous maps.
@isnad1 id=eq.2h6v.s8.dc83a483da14 from=translated src=- shape=cbead916 vocab=2199f473
-/
theorem preimageSetInclusion_comp (f : C(X, Y)) {A B C : Set Y}
    (hAB : A ⊆ B) (hBC : B ⊆ C) :
    preimageSetInclusion f (hAB.trans hBC) =
      (preimageSetInclusion f hBC).comp (preimageSetInclusion f hAB) := by
  ext x
  rfl

/-- A path inside an inverse image identifies the corresponding subtype path components.
@isnad1 id=eq.3h6v.s8.507576a1e7d8 from=translated src=- shape=0186e1f4 vocab=55269fe3
-/
theorem mk_eq_of_joinedIn (f : C(X, Y)) (A : Set Y) {x y : X}
    (hxy : JoinedIn (f ⁻¹' A) x y) (hx : f x ∈ A) (hy : f y ∈ A) :
    (ZerothHomotopy.mk ⟨x, hx⟩ : ZerothHomotopy {x // f x ∈ A}) =
      ZerothHomotopy.mk ⟨y, hy⟩ :=
  ZerothHomotopy.sound hxy.joined_subtype.somePath

end inverseImage

end TDA.Topology
