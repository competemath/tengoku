/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Tengoku.Seed.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.Colimits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `SheafOfModules.toSheaf` preserves colimits, and hence epimorphisms

`SheafOfModules.toSheaf R : SheafOfModules R ⥤ Sheaf J AddCommGrpCat` sends a sheaf of modules
to its underlying sheaf of abelian groups. Mathlib records that it is faithful, additive and
`PreservesFiniteLimits` (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean`), but says
nothing about colimits, and in particular nothing about epimorphisms. Faithfulness gives only
*reflection* of epimorphisms, which is the direction already used in
`Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Criterion.lean`.

Upstreaming this file adds `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` to
`Mathlib/Algebra/Category/ModuleCat/Sheaf/Colimits.lean`, whose closure is **1451** Mathlib
modules — **4** new ones, measured with `scripts/import_cost.py`. Its two other imports are
already in that closure.

This file supplies the other direction. It matters because an epimorphism of sheaves of
abelian groups is locally surjective on sections
(`CategoryTheory.Sheaf.isLocallySurjective_of_epi_addCommGrp`), whereas an epimorphism of
sheaves of modules carries no such information until it is transported across `toSheaf`.

## The argument

`SheafOfModules R` is the reflective subcategory of `PresheafOfModules R.obj` cut out by the
sheafification functor `L := PresheafOfModules.sheafification (𝟙 R.obj)`: the counit of
`PresheafOfModules.sheafificationAdjunction` is an isomorphism, so every sheaf of modules `M`
is `L` of its own underlying presheaf, and every diagram `F` in `SheafOfModules R` is
isomorphic to `(F ⋙ forget R) ⋙ L`. A colimit of such a diagram is therefore `L` of a colimit
computed in presheaves, and

```
L ⋙ SheafOfModules.toSheaf R  ≅  PresheafOfModules.toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat
```

is `PresheafOfModules.sheafificationCompToSheaf`, which is literally `Iso.refl _`. Both `L`
(a left adjoint) and the right-hand composite (a colimit-preserving functor followed by a left
adjoint) preserve colimits, and that is enough: `toSheaf R` sends the colimit cocone of
`(F ⋙ forget R) ⋙ L` — which is `L` applied to a colimit cocone in presheaves — to a colimit
cocone.

Note that the analogous statement for the *presheaf* level is false, and is the reason none of
the obvious shortcuts work: `PresheafOfModules.toPresheaf` composed with `sheafToPresheaf` does
**not** preserve epimorphisms, because an epimorphism of sheaves is only locally surjective, not
objectwise surjective.

## Main results

- `SheafOfModules.preservesColimitsOfShape_toSheaf`
- `SheafOfModules.preservesFiniteColimits_toSheaf`
- `SheafOfModules.preservesEpimorphisms_toSheaf`
-/

@[expose] public section

universe w' w v v' u u'

open CategoryTheory Limits

namespace SheafOfModules

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The functor sending a sheaf of modules to its underlying sheaf of abelian groups preserves
colimits of shape `K`, whenever `AddCommGrpCat` has them. -/
noncomputable instance preservesColimitsOfShape_toSheaf (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (toSheaf.{v} R) where
  preservesColimit {F} := by
    have hL : PreservesColimitsOfShape K (PresheafOfModules.sheafification.{v} (𝟙 R.obj)) :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).leftAdjoint_preservesColimits.1
    have hLT : PreservesColimitsOfShape K
        (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R) :=
      preservesColimitsOfShape_of_natIso (PresheafOfModules.sheafificationCompToSheaf _).symm
    have : PreservesColimit ((F ⋙ forget R) ⋙ PresheafOfModules.sheafification.{v} (𝟙 R.obj))
        (toSheaf.{v} R) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves _ (colimit.isColimit (F ⋙ forget R)))
        (isColimitOfPreserves
          (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R)
          (colimit.isColimit (F ⋙ forget R)))
    let e : F ≅ (F ⋙ forget R) ⋙ PresheafOfModules.sheafification.{v} (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    exact preservesColimit_of_iso_diagram _ e.symm

/-- The functor sending a sheaf of modules to its underlying sheaf of abelian groups is right
exact. Together with Mathlib's `PreservesFiniteLimits` instance it is therefore exact. -/
noncomputable instance preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (toSheaf.{v} R) where

end

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The underlying morphism of sheaves of abelian groups of an epimorphism of sheaves of
modules is an epimorphism.**

Mathlib records the reflection of epimorphisms along `toSheaf R`, which is formal from
faithfulness; this is the preservation, which is not. It follows from right exactness: in an
abelian category a morphism is an epimorphism exactly when its cokernel vanishes, and
`toSheaf R` preserves cokernels. -/
instance preservesEpimorphisms_toSheaf : (toSheaf.{v} R).PreservesEpimorphisms where
  preserves {_ _} f hf :=
    have : Epi f := hf
    Preadditive.epi_of_isZero_cokernel _
      (IsZero.of_iso (Functor.map_isZero _ (isZero_cokernel_of_epi f))
        (PreservesCokernel.iso (toSheaf.{v} R) f).symm)

end

end SheafOfModules
