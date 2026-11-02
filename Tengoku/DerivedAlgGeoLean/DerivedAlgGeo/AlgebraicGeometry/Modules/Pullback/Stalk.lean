/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Category.Grp.Zero
import Tengoku.Seed.Algebra.Category.ModuleCat.Descent
import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Tengoku.Seed.Algebra.Module.TransferInstance
import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf
import Tengoku.Seed.CategoryTheory.Functor.ReflectsIso.Limits
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Finite
import Tengoku.Seed.Topology.Sheaves.Abelian
import Tengoku.Seed.Topology.Sheaves.Sheafify
import Tengoku.Seed.Topology.Sheaves.Skyscraper
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Limits.Preserves.Reflective
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Topology.Sheaves.ModuleStalkSheafification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Module stalks and pullback

This file equips stalks of scheme-module sheaves with their canonical local-ring
module structure. These stalk functors preserve finite limits and coproducts and jointly
reflect isomorphisms.  Pullback followed by a module stalk is identified with
the source stalk followed by extension of scalars along the local-ring map.

The pullback comparison is first constructed for presheaves via a private
module-valued skyscraper adjunction, then transported through module
sheafification.  It assumes no flatness and does not assert that pullback along
an arbitrary scheme morphism is exact.

## Main definitions

`AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor` bundles a sheaf stalk over the local ring.

## Main results

* `AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor_preservesSmallColimits`
  preserves arbitrary small colimits; the existing coproduct theorem is its
  discrete-diagram specialization.
* `AlgebraicGeometry.Scheme.Modules.preservesFiniteLimits_of_stalkwise`
  reduces finite-limit preservation to
  module stalks.
* `AlgebraicGeometry.Scheme.Modules.presheafModulePullbackStalkIso`
  compares presheaf pullback with extension of
  scalars on stalks.
* `AlgebraicGeometry.Scheme.Modules.pullbackStalkIso`
  gives the corresponding comparison for module sheaves.
* `AlgebraicGeometry.Scheme.Modules.exists_sheaf_with_stalk`
  realizes any local-ring module as a sheaf stalk.

## Implementation notes

The realization sheaf is the sheafification of the existing module skyscraper
presheaf. The proof uses the module-stalk adjunction and its comparison with
the underlying additive stalk.

## References

The stalk and skyscraper constructions extend Mathlib's module-sheaf and
topological-sheaf APIs at the pinned revision.

## Tags

module stalk, scheme module sheaf, pullback, skyscraper
-/

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

/-- The cocone of underlying rings whose point is the local ring of `X` at
`x`, specialized from the topological module-stalk construction.-/
abbrev moduleStalkRingCocone (X : Scheme.{u}) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf ⋙
      forget₂ CommRingCat RingCat) :=
  _root_.PresheafOfModules.stalkRingCocone X X.presheaf x

/-- Definitional specialization of `PresheafOfModules.stalkRingIsColimit` to
the scheme's structure presheaf.-/
abbrev moduleStalkRingIsColimit (X : Scheme.{u}) (x : X) :
    IsColimit (moduleStalkRingCocone X x) :=
  _root_.PresheafOfModules.stalkRingIsColimit X X.presheaf x

/-- Definitional specialization of `PresheafOfModules.commNeighborhoodStalkFunctor`,
using the scheme's local ring as its scalar ring.-/
abbrev neighborhoodModuleStalkFunctor (X : Scheme.{u}) (x : X) :
    _root_.PresheafOfModules.{u}
        ((OpenNhds.inclusion x).op ⋙ X.ringCatSheaf.obj) ⥤
      ModuleCat.{u} (X.presheaf.stalk x) :=
  _root_.PresheafOfModules.commNeighborhoodStalkFunctor X X.presheaf x

/-- The stalk of a presheaf of modules, bundled over the local ring.-/
abbrev presheafModuleStalkFunctor (X : Scheme.{u}) (x : X) :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      ModuleCat.{u} (X.presheaf.stalk x) :=
  _root_.PresheafOfModules.commStalkFunctor X X.presheaf x

/-- The stalk of a sheaf of modules, bundled as a module over the local ring.

This refines the usual abelian-group-valued stalk functor with the canonical
local-ring module structure.-/
abbrev moduleStalkFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  _root_.PresheafOfModules.sheafStalkFunctor X X.ringCatSheaf.obj x
    (moduleStalkRingIsColimit X x) X.ringCatSheaf.property

/-- The module map on stalks induced by the unit from a presheaf of modules
to its module sheafification.-/
abbrev presheafModuleStalkToSheafificationApp
    (X : Scheme.{u}) (x : X)
    (M : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    (presheafModuleStalkFunctor X x).obj M ⟶
      (moduleStalkFunctor X x).obj
        ((_root_.PresheafOfModules.sheafification
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj M) :=
  _root_.PresheafOfModules.stalkSheafificationApp X X.ringCatSheaf.obj x
    (moduleStalkRingIsColimit X x) X.ringCatSheaf.property M

/-- Module sheafification induces an isomorphism on every module stalk.-/
theorem presheafModuleStalkToSheafificationApp_isIso
    (X : Scheme.{u}) (x : X)
    (M : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    IsIso (presheafModuleStalkToSheafificationApp X x M) :=
  _root_.PresheafOfModules.stalkSheafificationApp_isIso X X.ringCatSheaf.obj x
    (moduleStalkRingIsColimit X x) X.ringCatSheaf.property M

/-- Taking a module stalk commutes naturally with module sheafification.-/
abbrev presheafModuleStalkSheafificationIso
    (X : Scheme.{u}) (x : X) :
    presheafModuleStalkFunctor X x ≅
      _root_.PresheafOfModules.sheafification
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) ⋙
        moduleStalkFunctor X x :=
  _root_.PresheafOfModules.stalkSheafificationIso X X.ringCatSheaf.obj x
    (moduleStalkRingIsColimit X x) X.ringCatSheaf.property

/-- Forgetting the local-ring action on
`AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor` recovers the
usual stalk of the underlying sheaf of abelian groups.-/
def moduleStalkForgetIso (X : Scheme.{u}) (x : X) :
    moduleStalkFunctor X x ⋙
        forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
  CategoryTheory.Functor.associator _ _ _

/-- Arbitrary small colimits of module sheaves are preserved by the underlying
additive sheaf stalk. The forgetful module functor reflects and preserves the
corresponding module colimits.-/
theorem moduleStalkFunctor_preservesSmallColimits
    (X : Scheme.{u}) (x : X) (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J (moduleStalkFunctor X x) := by
  let forgetModule := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  let α := 𝟙 X.ringCatSheaf.obj
  letI : PreservesColimitsOfShape J
      (PresheafOfModules.sheafification α ⋙ SheafOfModules.toSheaf X.ringCatSheaf) := by
    exact inferInstanceAs (PreservesColimitsOfShape J
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
        presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  have hF : PreservesColimitsOfShape J
      (SheafOfModules.toSheaf X.ringCatSheaf) :=
    (PresheafOfModules.sheafificationAdjunction α).preservesColimitsOfShape_of_comp_left
      (K := J) (SheafOfModules.toSheaf X.ringCatSheaf)
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hG : PreservesColimitsOfShape J G := inferInstance
  have hFG : PreservesColimitsOfShape J
      (SheafOfModules.toSheaf X.ringCatSheaf ⋙ G) := by
    exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _
      (SheafOfModules.toSheaf X.ringCatSheaf) G hF hG
  letI : PreservesColimitsOfShape J
      (moduleStalkFunctor X x ⋙ forgetModule) :=
    (preservesColimitsOfShape_iff_of_natIso (moduleStalkForgetIso X x)).mpr hFG
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (moduleStalkFunctor X x) forgetModule

/-- The established indexed-coproduct API is the discrete-diagram case of
general small-colimit preservation.-/
theorem moduleStalkFunctor_preservesColimitsOfShape
    (X : Scheme.{u}) (x : X) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (moduleStalkFunctor X x) :=
  moduleStalkFunctor_preservesSmallColimits X x (Discrete I)

/-- Finite colimits follow from the general small-colimit theorem after
transporting a finite indexing category to the scheme's universe.-/
theorem moduleStalkFunctor_preservesFiniteColimits
    (X : Scheme.{u}) (x : X) :
    PreservesFiniteColimits (moduleStalkFunctor X x) := by
  apply preservesFiniteColimits_of_preservesFiniteColimitsOfSize
  intro J _ _
  exact moduleStalkFunctor_preservesSmallColimits X x J

/-- Taking the stalk of a sheaf of modules preserves finite limits.-/
theorem moduleStalkFunctor_preservesFiniteLimits
    (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (moduleStalkFunctor X x) := by
  let forgetModule :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hF : PreservesFiniteLimits F := inferInstance
  have hG : PreservesFiniteLimits G := inferInstance
  have hFG : PreservesFiniteLimits (F ⋙ G) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ F G hF hG
  have hComposite :
      PreservesFiniteLimits (moduleStalkFunctor X x ⋙ forgetModule) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (moduleStalkForgetIso X x).symm hFG
  letI := hComposite
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleStalkFunctor X x) forgetModule

/-- The family of module-stalk functors over all points detects
isomorphisms of sheaves of modules.-/
theorem moduleStalkFunctors_jointlyReflectIsomorphisms (X : Scheme.{u}) :
    JointlyReflectIsomorphisms (moduleStalkFunctor X) where
  isIso {M N} f := by
    intro
    let M' : TopCat.Sheaf AddCommGrpCat.{u} X :=
      ⟨M.presheaf, M.isSheaf⟩
    let N' : TopCat.Sheaf AddCommGrpCat.{u} X :=
      ⟨N.presheaf, N.isSheaf⟩
    let g : M' ⟶ N' := { hom := f.mapPresheaf }
    haveI : IsIso g := by
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      have : IsIso
          ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x))
            AddCommGrpCat.{u}).map ((moduleStalkFunctor X x).map f)) :=
        inferInstance
      exact this
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    change IsIso
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map g).app (op U))
    infer_instance

/-- A functor between categories of module sheaves preserves finite limits
as soon as all of its composites with module-stalk functors do.-/
theorem preservesFiniteLimits_of_stalkwise
    {X Y : Scheme.{u}} (F : Y.Modules ⥤ X.Modules)
    (hF : ∀ x : X,
      PreservesFiniteLimits (F ⋙ moduleStalkFunctor X x)) :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := by
    letI (x : X) : PreservesFiniteLimits (moduleStalkFunctor X x) :=
      moduleStalkFunctor_preservesFiniteLimits X x
    letI (x : X) : PreservesFiniteLimits
        (F ⋙ moduleStalkFunctor X x) :=
      hF x
    refine { preservesLimit := fun {K} ↦
      { preserves := fun {c} hc ↦ ⟨?_⟩ } }
    exact (moduleStalkFunctors_jointlyReflectIsomorphisms X).jointlyReflectsLimit
      (fun x ↦ by
        change IsLimit ((F ⋙ moduleStalkFunctor X x).mapCone c)
        exact isLimitOfPreserves (F ⋙ moduleStalkFunctor X x) hc)

/-- The ring map on neighborhood diagrams induced by a scheme morphism at a
point. Its component over `V ∋ f(x)` is the restriction of the scheme map
from `Γ(V, 𝒪_Y)` to `Γ(f⁻¹(V), 𝒪_X)`.-/
def neighborhoodRingHom {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (OpenNhds.inclusion (f x)).op ⋙ Y.ringCatSheaf.obj ⟶
      (OpenNhds.map f.base x).op ⋙
        ((OpenNhds.inclusion x).op ⋙ X.ringCatSheaf.obj) where
  app V := (forget₂ CommRingCat RingCat).map (f.app V.unop.1)
  naturality V W g := by
    exact f.toRingCatSheafHom.hom.naturality
      ((OpenNhds.inclusion (f x)).op.map g)

/-- Pullback of modules along the induced map between the two neighborhood
ring diagrams.-/
abbrev neighborhoodModulePullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :=
  _root_.PresheafOfModules.pullback (neighborhoodRingHom f x)

/-- The neighborhood ring map commutes with the two stalk cocones through the
scheme morphism's map on local rings.-/
lemma neighborhoodRingHom_comp_stalkCocone {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (V : (OpenNhds (f x))ᵒᵖ) :
    (moduleStalkRingCocone Y (f x)).ι.app V ≫
        (forget₂ CommRingCat RingCat).map (f.stalkMap x) =
      (neighborhoodRingHom f x).app V ≫
        (moduleStalkRingCocone X x).ι.app
          ((OpenNhds.map f.base x).op.obj V) := by
  obtain ⟨⟨V, hxV⟩⟩ := V
  exact congr_arg (forget₂ CommRingCat RingCat).map
    (Scheme.Hom.germ_stalkMap f V x hxV)

/-- Objectwise comparison between the two right adjoints used to compute
pullback followed by the neighborhood colimit.-/
def constNeighborhoodPushforwardIsoApp {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (_root_.PresheafOfModules.constFunctor (moduleStalkRingCocone X x) ⋙
      _root_.PresheafOfModules.pushforward (neighborhoodRingHom f x)).obj N ≅
    (ModuleCat.restrictScalars (f.stalkMap x).hom ⋙
      _root_.PresheafOfModules.constFunctor
        (moduleStalkRingCocone Y (f x))).obj N :=
  _root_.PresheafOfModules.isoMk
    (fun V ↦ ModuleCat.isoMk (Iso.refl _) (fun r ↦ by
      ext m
      exact congrArg (fun s : X.presheaf.stalk x ↦ s • (show N from m))
        (CategoryTheory.congr_fun
          (neighborhoodRingHom_comp_stalkCocone f x V) r)))
    (fun {V W} g ↦ by ext m; rfl)

/-- Natural comparison between constant neighborhood modules followed by
pushforward and restriction of scalars followed by constant modules.-/
def constNeighborhoodPushforwardIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    _root_.PresheafOfModules.constFunctor (moduleStalkRingCocone X x) ⋙
        _root_.PresheafOfModules.pushforward (neighborhoodRingHom f x) ≅
      ModuleCat.restrictScalars (f.stalkMap x).hom ⋙
        _root_.PresheafOfModules.constFunctor
          (moduleStalkRingCocone Y (f x)) :=
  NatIso.ofComponents (constNeighborhoodPushforwardIsoApp f x)
    (fun {M N} g ↦ by ext V m; rfl)

/-- Pulling a module diagram back from neighborhoods of `f(x)` and taking its
neighborhood colimit agrees with first taking the stalk at `f(x)` and then
extending scalars along the local-ring map at `x`.-/
def neighborhoodModulePullbackStalkIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    neighborhoodModulePullback f x ⋙ neighborhoodModuleStalkFunctor X x ≅
      neighborhoodModuleStalkFunctor Y (f x) ⋙
        ModuleCat.extendScalars (f.stalkMap x).hom := by
  letI : InitiallySmall.{u} (OpenNhds x) :=
    initiallySmall_of_essentiallySmall _
  letI : InitiallySmall.{u} (OpenNhds (f x)) :=
    initiallySmall_of_essentiallySmall _
  letI : CommRing (moduleStalkRingCocone X x).pt :=
    inferInstanceAs (CommRing (X.presheaf.stalk x))
  letI : CommRing (moduleStalkRingCocone Y (f x)).pt :=
    inferInstanceAs (CommRing (Y.presheaf.stalk (f x)))
  change neighborhoodModulePullback f x ⋙
      _root_.PresheafOfModules.colimitFunctor (moduleStalkRingIsColimit X x) ≅
    _root_.PresheafOfModules.colimitFunctor
        (moduleStalkRingIsColimit Y (f x)) ⋙
      ModuleCat.extendScalars (f.stalkMap x).hom
  exact Adjunction.leftAdjointCompIso
    (_root_.PresheafOfModules.pullbackPushforwardAdjunction
      (neighborhoodRingHom f x))
    (_root_.PresheafOfModules.colimitAdjunction (moduleStalkRingIsColimit X x))
    ((_root_.PresheafOfModules.colimitAdjunction
      (moduleStalkRingIsColimit Y (f x))).comp
        (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))
    (constNeighborhoodPushforwardIso f x)

/-! ### The presheaf pullback-to-stalk comparison

The implementation constructs the module-valued skyscraper presheaf at a
point, proves that it is right adjoint to the module stalk functor, and uses
uniqueness of left adjoints to identify pullback followed by a stalk with
extension of scalars along the induced local-ring map. The construction is
kept private; the resulting canonical comparison is exposed below.
-/

@[reducible] private def subsingletonModule (R M : Type u) [Ring R]
    [AddCommGroup M] [Subsingleton M] : Module R M := by
  letI : SMul R M := ⟨fun _ _ ↦ 0⟩
  letI : MulAction R M := {
    one_smul := fun _ ↦ Subsingleton.elim _ _
    mul_smul := fun _ _ _ ↦ Subsingleton.elim _ _ }
  letI : DistribMulAction R M := {
    smul_zero := fun _ ↦ Subsingleton.elim _ _
    smul_add := fun _ _ _ ↦ Subsingleton.elim _ _ }
  exact {
    add_smul := fun _ _ _ ↦ Subsingleton.elim _ _
    zero_smul := fun _ ↦ Subsingleton.elim _ _ }

private theorem terminalAddCommGrpSubsingleton :
    Subsingleton (terminal AddCommGrpCat.{u}) :=
  AddCommGrpCat.subsingleton_of_isZero
    ((isZero_zero AddCommGrpCat).of_iso
      (HasZeroObject.zeroIsoTerminal (C := AddCommGrpCat)).symm)

private def moduleSkyscraperUnderlying (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := by
  classical
  exact skyscraperPresheaf x
    ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).obj N)

private def moduleSkyscraperPositiveEquiv (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X)ᵒᵖ)
    (hU : x ∈ U.unop) :
    ((moduleSkyscraperUnderlying X x N).obj U : Type u) ≃+ N := by
  classical
  exact (eqToIso (ite_eq_left hU)).addCommGroupIsoToAddEquiv

@[reducible] private def moduleSkyscraperModule (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U)
      ((moduleSkyscraperUnderlying X x N).obj U) := by
  classical
  by_cases hU : x ∈ U.unop
  · letI : Module (X.ringCatSheaf.obj.obj U) N :=
      Module.compHom N (X.presheaf.germ U.unop x hU).hom
    exact (moduleSkyscraperPositiveEquiv X x N U hU).module _
  · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
      terminalAddCommGrpSubsingleton
    letI : Module (X.ringCatSheaf.obj.obj U)
        (terminal AddCommGrpCat.{u}) :=
      subsingletonModule _ _
    exact (eqToIso (ite_eq_right hU)).addCommGroupIsoToAddEquiv.module _

private def moduleSkyscraperPresheaf (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) : X.PresheafOfModules := by
  classical
  let G := moduleSkyscraperUnderlying X x N
  letI (U : (Opens X)ᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) (G.obj U) :=
    moduleSkyscraperModule X x N U
  exact _root_.PresheafOfModules.ofPresheaf G (fun {U V} i r m ↦ by
    by_cases hV : x ∈ V.unop
    · have hU : x ∈ U.unop := i.unop.le hV
      let eU := moduleSkyscraperPositiveEquiv X x N U hU
      let eV := moduleSkyscraperPositiveEquiv X x N V hV
      letI : Module (X.ringCatSheaf.obj.obj U) N :=
        Module.compHom N (X.presheaf.germ U.unop x hU).hom
      letI : Module (X.ringCatSheaf.obj.obj V) N :=
        Module.compHom N (X.presheaf.germ V.unop x hV).hom
      have map_compat (z : G.obj U) : eV (G.map i z) = eU z := by
        have hmap : G.map i ≫
              (eqToIso (ite_eq_left hV) : G.obj V ≅
                (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N).hom =
            (eqToIso (ite_eq_left hU) : G.obj U ≅
                (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).obj N).hom := by
          simp [G, moduleSkyscraperUnderlying, skyscraperPresheaf, hU, hV]
        exact CategoryTheory.congr_fun hmap z
      apply eV.injective
      calc
        eV (G.map i (r • m)) = eU (r • m) := map_compat _
        _ = r • eU m := by
          let smulActual (a : X.ringCatSheaf.obj.obj U) (z : G.obj U) : G.obj U :=
            letI : Module (X.ringCatSheaf.obj.obj U) (G.obj U) :=
              moduleSkyscraperModule X x N U
            a • z
          let smulTransfer (a : X.ringCatSheaf.obj.obj U) (z : G.obj U) : G.obj U :=
            letI : Module (X.ringCatSheaf.obj.obj U) (G.obj U) := eU.module _
            a • z
          have hmodule : moduleSkyscraperModule X x N U = eU.module _ := by
            simp [moduleSkyscraperModule, eU, hU]
          have hsmul : smulActual = smulTransfer := by
            unfold smulActual smulTransfer
            rw [hmodule]
          change eU (smulActual r m) = r • eU m
          rw [hsmul]
          simp [smulTransfer, Equiv.smul_def]
        _ = (X.ringCatSheaf.obj.map i).hom r • eU m := by
          change (X.presheaf.germ U.unop x hU).hom r • eU m =
            (X.presheaf.germ V.unop x hV).hom
              ((X.ringCatSheaf.obj.map i).hom r) • eU m
          exact congrArg (fun s : X.presheaf.stalk x ↦ s • eU m)
            (CategoryTheory.congr_fun (X.presheaf.germ_res' i x hV) r).symm
        _ = (X.ringCatSheaf.obj.map i).hom r • eV (G.map i m) := by
          rw [map_compat]
        _ = eV ((X.ringCatSheaf.obj.map i).hom r • G.map i m) := by
          let smulActual (a : X.ringCatSheaf.obj.obj V) (z : G.obj V) : G.obj V :=
            letI : Module (X.ringCatSheaf.obj.obj V) (G.obj V) :=
              moduleSkyscraperModule X x N V
            a • z
          let smulTransfer (a : X.ringCatSheaf.obj.obj V) (z : G.obj V) : G.obj V :=
            letI : Module (X.ringCatSheaf.obj.obj V) (G.obj V) := eV.module _
            a • z
          have hmodule : moduleSkyscraperModule X x N V = eV.module _ := by
            simp [moduleSkyscraperModule, eV, hV]
          have hsmul : smulActual = smulTransfer := by
            unfold smulActual smulTransfer
            rw [hmodule]
          change (X.ringCatSheaf.obj.map i).hom r • eV (G.map i m) =
            eV (smulActual ((X.ringCatSheaf.obj.map i).hom r) (G.map i m))
          rw [hsmul]
          simp [smulTransfer, Equiv.smul_def]
    · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
        terminalAddCommGrpSubsingleton
      apply (eqToIso (ite_eq_right hV) : G.obj V ≅
        terminal AddCommGrpCat).addCommGroupIsoToAddEquiv.injective
      exact Subsingleton.elim _ _)

private def moduleSkyscraperPresheafAppIso (X : Scheme.{u}) (x : X)
    (N : ModuleCat.{u} (X.presheaf.stalk x)) (U : (Opens X)ᵒᵖ)
    (hU : x ∈ U.unop) :
    (moduleSkyscraperPresheaf X x N).obj U ≅
      (ModuleCat.restrictScalars (X.presheaf.germ U.unop x hU).hom).obj N := by
  classical
  let e := moduleSkyscraperPositiveEquiv X x N U hU
  letI : Module (X.ringCatSheaf.obj.obj U) N :=
    Module.compHom N (X.presheaf.germ U.unop x hU).hom
  apply ModuleCat.isoMk
    (eqToIso (ite_eq_left hU))
  intro r
  ext m
  let smulActual (a : X.ringCatSheaf.obj.obj U)
      (z : (moduleSkyscraperUnderlying X x N).obj U) :=
    letI : Module (X.ringCatSheaf.obj.obj U)
        ((moduleSkyscraperUnderlying X x N).obj U) :=
      moduleSkyscraperModule X x N U
    a • z
  let smulTransfer (a : X.ringCatSheaf.obj.obj U)
      (z : (moduleSkyscraperUnderlying X x N).obj U) :=
    letI : Module (X.ringCatSheaf.obj.obj U)
        ((moduleSkyscraperUnderlying X x N).obj U) := e.module _
    a • z
  have hmodule : moduleSkyscraperModule X x N U = e.module _ := by
    simp [moduleSkyscraperModule, e, hU]
  have hsmul : smulActual = smulTransfer := by
    unfold smulActual smulTransfer
    rw [hmodule]
  change (X.presheaf.germ U.unop x hU).hom r • e m = e (smulActual r m)
  rw [hsmul]
  simp [smulTransfer, Equiv.smul_def]
  rfl

private def moduleSkyscraperMapApp (X : Scheme.{u}) (x : X)
    {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N) :
    ∀ U, (moduleSkyscraperPresheaf X x M).obj U ⟶
      (moduleSkyscraperPresheaf X x N).obj U := fun U ↦ by
  classical
  by_cases hU : x ∈ U.unop
  · exact (moduleSkyscraperPresheafAppIso X x M U hU).hom ≫
      (ModuleCat.restrictScalars
        (X.presheaf.germ U.unop x hU).hom).map g ≫
      (moduleSkyscraperPresheafAppIso X x N U hU).inv
  · exact 0

private def moduleSkyscraperUnderlyingMap (X : Scheme.{u}) (x : X)
    {M N : ModuleCat.{u} (X.presheaf.stalk x)} (g : M ⟶ N) :
    moduleSkyscraperUnderlying X x M ⟶
      moduleSkyscraperUnderlying X x N := by
  classical
  exact SkyscraperPresheafFunctor.map' x
    ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map g)

private def moduleSkyscraperPushforwardIsoAppOfMem {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y)ᵒᵖ) (hV : f x ∈ V.unop) :
    ((_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
        (moduleSkyscraperPresheaf X x N)).obj V ≅
      (moduleSkyscraperPresheaf Y (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V := by
  classical
  let a := (f.app V.unop).hom
  let b := (X.presheaf.germ (f ⁻¹ᵁ V.unop) x hV).hom
  let c := (Y.presheaf.germ V.unop (f x) hV).hom
  let d := (f.stalkMap x).hom
  let ba := b.comp a
  let dc := d.comp c
  have h : ba = dc := congrArg CommRingCat.Hom.hom
    (Scheme.Hom.germ_stalkMap f V.unop x hV).symm
  exact (ModuleCat.restrictScalars a).mapIso
        (moduleSkyscraperPresheafAppIso X x N
          (op (f ⁻¹ᵁ V.unop)) hV) ≪≫
      ((ModuleCat.restrictScalarsComp' a b ba rfl).app N).symm ≪≫
      (ModuleCat.restrictScalarsCongr h).app N ≪≫
      (ModuleCat.restrictScalarsComp' c d dc rfl).app N ≪≫
      (moduleSkyscraperPresheafAppIso Y (f x)
        ((ModuleCat.restrictScalars d).obj N) V hV).symm

private def moduleSkyscraperPushforwardIsoApp {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (V : (Opens Y)ᵒᵖ) :
    ((_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
        (moduleSkyscraperPresheaf X x N)).obj V ≅
      (moduleSkyscraperPresheaf Y (f x)
        ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V := by
  classical
  by_cases hV : f x ∈ V.unop
  · exact moduleSkyscraperPushforwardIsoAppOfMem f x N V hV
  · letI : Subsingleton (terminal AddCommGrpCat.{u}) :=
      terminalAddCommGrpSubsingleton
    let L := ((_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
      (moduleSkyscraperPresheaf X x N)).obj V
    let R := (moduleSkyscraperPresheaf Y (f x)
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V
    let eL : (L : Type u) ≃+ (terminal AddCommGrpCat.{u} : Type u) :=
      (eqToIso (ite_eq_right hV) :
        (moduleSkyscraperUnderlying X x N).obj
            (op (f ⁻¹ᵁ V.unop)) ≅
          terminal AddCommGrpCat).addCommGroupIsoToAddEquiv
    let eR : (R : Type u) ≃+ (terminal AddCommGrpCat.{u} : Type u) :=
      (eqToIso (ite_eq_right hV) :
        (moduleSkyscraperUnderlying Y (f x)
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).obj V ≅
            terminal AddCommGrpCat).addCommGroupIsoToAddEquiv
    let e : (forget₂ (ModuleCat (Y.ringCatSheaf.obj.obj V)) AddCommGrpCat).obj L ≅
        (forget₂ (ModuleCat (Y.ringCatSheaf.obj.obj V)) AddCommGrpCat).obj R :=
      (eL.trans eR.symm).toAddCommGrpIso
    apply ModuleCat.isoMk e
    intro r
    ext m
    apply eR.injective
    exact Subsingleton.elim _ _

end

end AlgebraicGeometry.Scheme.Modules
