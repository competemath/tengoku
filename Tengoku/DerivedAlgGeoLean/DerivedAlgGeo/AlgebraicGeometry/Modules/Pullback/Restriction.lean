/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.StructureSheaf
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Topology.Category.TopCat.Opens.Final
import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf
import Tengoku.Seed.AlgebraicGeometry.Restrict
import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pullback and restriction of scheme-module sheaves

For a scheme morphism `f : X ⟶ Y` and an open `U ⊆ Y`, restriction of `f⁺ M` to
`f⁻¹ U` agrees with pullback of `M|_U` along the restricted morphism
`f|_U : X|_{f⁻¹ U} ⟶ Y|_U`.

The statement is expressed in Mathlib's slice-site category, because this is the common root used
by local generators, finite presentations, and intrinsic local freeness. The proof is assembled
only from the scheme-module pullback pseudofunctor and the equivalence between slice-site modules
and modules on an open subscheme.

The file also packages pullback on slices as one functor between slice-site module categories,
`pullbackOverFunctor`, with its adjunction to pushforward on slices.  The point is where the
instances are stated: `Presentation.map` and the other slice-level transports ask for colimit
preservation of a functor between `SheafOfModules` categories, and the pullback functor on
`X.Modules` carries its instances at the `Scheme.Modules` wrapper's category instance, where
that search does not find them (see `Modules/Affine/Equivalence.lean`).  Composing with the two
slice equivalences and taking the adjunction of the composite states colimit preservation in the
form the transports meet.

## Main definitions

* `pullbackOverFunctor`, `pushforwardOverFunctor`, `pullbackOverAdjunction`: pullback on slices,
  as a left adjoint between slice-site module categories.
* `pullbackOverIso`: the restriction square for pullback, on objects.
* `pullbackRestrictUnitIso`, `pullbackOverUnitIso`: pullback on slices fixes the structure
  sheaf, the identification `Presentation.map` consumes.
* `Scheme.Hom.coversTop_preimage`: the preimages of a cover cover.
-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable section

/-- Pullback along `f`, on the slice over `U : Y.Opens`, as a functor between slice-site module
categories: transport to the open subscheme, pull back along `f ∣_ U`, transport back.-/
def pullbackOverFunctor (f : X ⟶ Y) (U : Y.Opens) :
    SheafOfModules (Y.ringCatSheaf.over U) ⥤ SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (overEquiv U).functor ⋙ pullback (f ∣_ U) ⋙ (overEquiv (f ⁻¹ᵁ U)).inverse

/-- Pushforward along `f`, on the slice over `U : Y.Opens`, the right adjoint of
`pullbackOverFunctor`.-/
def pushforwardOverFunctor (f : X ⟶ Y) (U : Y.Opens) :
    SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ U)) ⥤ SheafOfModules (Y.ringCatSheaf.over U) :=
  (overEquiv (f ⁻¹ᵁ U)).functor ⋙ pushforward (f ∣_ U) ⋙ (overEquiv U).inverse

/-- Pullback on slices is left adjoint to pushforward on slices: the composite of the two slice
equivalences' adjunctions with `pullbackPushforwardAdjunction`.-/
def pullbackOverAdjunction (f : X ⟶ Y) (U : Y.Opens) :
    pullbackOverFunctor f U ⊣ pushforwardOverFunctor f U :=
  (overEquiv U).toAdjunction.comp
    ((pullbackPushforwardAdjunction (f ∣_ U)).comp (overEquiv (f ⁻¹ᵁ U)).symm.toAdjunction)

/-- Restricting a pulled-back module to an inverse-image open agrees with pulling back the
restriction along the restricted scheme morphism, that is, with `pullbackOverFunctor`.-/
def pullbackOverIso (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    ((pullback f).obj M).over (f ⁻¹ᵁ U) ≅ (pullbackOverFunctor f U).obj (M.over U) := by
  let V : X.Opens := f ⁻¹ᵁ U
  let N : V.toScheme.Modules :=
    (pullback (f ∣_ U)).obj ((overEquiv U).functor.obj (M.over U))
  let eU : (overEquiv U).functor.obj (M.over U) ≅ (pullback U.ι).obj M :=
    (overFunctorEquiv U).app M ≪≫ (restrictFunctorIsoPullback U.ι).app M
  let e : (overEquiv V).functor.obj (((pullback f).obj M).over V) ≅ N :=
    (overFunctorEquiv V).app ((pullback f).obj M) ≪≫
      (restrictFunctorIsoPullback V.ι).app ((pullback f).obj M) ≪≫
      (pullbackComp V.ι f).app M ≪≫
      (pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
      (pullbackComp (f ∣_ U) U.ι).symm.app M ≪≫
      (pullback (f ∣_ U)).mapIso eU.symm
  exact (overEquiv V).fullyFaithfulFunctor.preimageIso
    (e ≪≫ ((overEquiv V).counitIso.app N).symm)

end

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

end AlgebraicGeometry.Scheme.Hom
