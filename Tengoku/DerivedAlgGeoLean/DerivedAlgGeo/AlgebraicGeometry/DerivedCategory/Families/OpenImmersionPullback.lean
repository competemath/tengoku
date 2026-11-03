/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.LeftDerivedPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact pullback along open immersions

Mathlib identifies module-sheaf pullback along an open immersion with
restriction and proves that restriction commutes with stalks.  Combining
that comparison with the stalkwise-to-global criterion from
`Families.FlatPullback` proves that pullback along every open immersion is
exact.  Consequently its ordinary module pullback descends to the concrete
derived fibers without an additional exactness hypothesis.

Mathlib also identifies restriction after module-sheaf pushforward with the
identity.  Applying that counit degreewise gives every complex on the open
subscheme an extension to the ambient scheme.  After localization this proves
that derived pullback along an open immersion is essentially surjective; no
exactness of pushforward is needed for this objectwise extension argument.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace SchemeBaseChange

/-- After forgetting the local-ring action, pullback followed by a stalk
along an open immersion is the ordinary stalk at the image point.-/
def openImmersionPullbackStalkForgetIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    (Scheme.Modules.pullback f ⋙ moduleStalkFunctor X x) ⋙
        forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x) :=
  CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (moduleStalkForgetIso X x) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (CategoryTheory.Functor.associator (SheafOfModules.toSheaf X.ringCatSheaf)
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
      (Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) ≪≫
    (CategoryTheory.Functor.associator (Scheme.Modules.restrictFunctor f)
      (Scheme.Modules.toPresheaf X)
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).symm ≪≫
    Scheme.Modules.restrictStalkNatIso f x

/-- Pullback along an open immersion, followed by any module-stalk functor,
preserves finite limits.
@isnad1 id=preserve.0h4v.s8.3067a7f289d7 from=translated src=- shape=065313da vocab=f5eb5449
-/
theorem openImmersionPullbackStalk_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    PreservesFiniteLimits
      (Scheme.Modules.pullback f ⋙ moduleStalkFunctor X x) := by
  let forgetX :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  let forgetY :=
    forget₂ (ModuleCat.{u} (Y.presheaf.stalk (f x))) AddCommGrpCat.{u}
  have hStalk : PreservesFiniteLimits (moduleStalkFunctor Y (f x)) :=
    moduleStalkFunctor_preservesFiniteLimits Y (f x)
  have hForget : PreservesFiniteLimits forgetY := inferInstance
  have hStalkForget : PreservesFiniteLimits
      (moduleStalkFunctor Y (f x) ⋙ forgetY) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hStalk hForget
  let e : moduleStalkFunctor Y (f x) ⋙ forgetY ≅
      Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x) :=
    moduleStalkForgetIso Y (f x) ≪≫
      (CategoryTheory.Functor.associator (SheafOfModules.toSheaf Y.ringCatSheaf)
        (TopCat.Sheaf.forget AddCommGrpCat.{u} Y)
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x))).symm
  have hRight : PreservesFiniteLimits
      (Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ e hStalkForget
  have hComposite : PreservesFiniteLimits
      ((Scheme.Modules.pullback f ⋙ moduleStalkFunctor X x) ⋙ forgetX) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (openImmersionPullbackStalkForgetIso f x).symm hRight
  letI := hComposite
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Scheme.Modules.pullback f ⋙ moduleStalkFunctor X x) forgetX

/-- Module-sheaf pullback along an open immersion preserves finite limits.
@isnad1 id=preserve.0h4v.s6.19086dcc8264 from=translated src=- shape=90c772b7 vocab=147684e8
-/
theorem openImmersionModulePullback_preservesFiniteLimits
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] : PreservesFiniteLimits (modulePullback f) :=
  preservesFiniteLimits_of_stalkwise (modulePullback f)
    (openImmersionPullbackStalk_preservesFiniteLimits f.left)

/-- Pullback along an open immersion of scheme base changes is exact.
@isnad1 id=isexactp.0h4v.s5.bf959b3a6e5b from=translated src=- shape=1f9e9c89 vocab=6460ec53
-/
theorem isExactPullback_of_isOpenImmersion
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] : IsExactPullback f := by
  letI : PreservesFiniteLimits (modulePullback f) :=
    openImmersionModulePullback_preservesFiniteLimits f
  exact IsExactPullback.of_preservesFiniteLimits f

/-- Exact pullback along open immersions is available to the derived
pullback API without a caller-supplied exactness instance.
@isnad1 id=isexactp.0h4v.s5.bf959b3a6e5b from=translated src=- shape=1f9e9c89 vocab=6460ec53
-/
instance (priority := 900) isExactPullbackOfIsOpenImmersion
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] : IsExactPullback f :=
  isExactPullback_of_isOpenImmersion f

/-! ## Essential surjectivity -/

/-- Pushforward followed by pullback along an open immersion is naturally
isomorphic to the identity on module sheaves.  The point is that pullback is
restriction in this case, and Mathlib's restriction--pushforward adjunction
has invertible counit.-/
def openImmersionModulePullbackPushforwardIso
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] :
    modulePushforward f ⋙ modulePullback f ≅ 𝟭 T.left.Modules :=
  (Functor.isoWhiskerLeft (modulePushforward f)
      (Scheme.Modules.restrictFunctorIsoPullback f.left)).symm ≪≫
    Scheme.Modules.restrictFunctorAdjCounitIso f.left

/-- Extend a complex on an open subscheme termwise by module-sheaf
pushforward.  Pushforward need not be exact: this functor is used only to
choose an ambient representative whose pullback is the original complex.-/
abbrev openImmersionComplexExtension
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U) :
    CochainComplex T.left.Modules ℤ ⥤ CochainComplex U.left.Modules ℤ :=
  (modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Pulling back the termwise extension of a complex from an open subscheme
recovers that complex.-/
def openImmersionComplexPullbackExtensionIso
    {S : Scheme.{u}} {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsOpenImmersion f.left] :
    openImmersionComplexExtension f ⋙ complexPullback f ≅
      𝟭 (CochainComplex T.left.Modules ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (openImmersionModulePullbackPushforwardIso f) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso T.left.Modules (ComplexShape.up ℤ)

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
