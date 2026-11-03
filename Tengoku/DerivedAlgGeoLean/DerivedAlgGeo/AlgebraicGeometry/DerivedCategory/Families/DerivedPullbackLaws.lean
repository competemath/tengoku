/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPullbackCoherence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pseudofunctor laws for exact derived pullback

The complex-level pullback unit and associativity laws are inherited degreewise
from Mathlib's module-sheaf pullback pseudofunctor.  Localization then transports
those laws to exact pullback on the concrete derived fibers.  Equality congruence
is lifted through the same localization so the laws have canonical, typed
right-hand sides even when composition is only propositionally equal.

This file proves the left-unit, right-unit, and associativity (pentagon) laws for
the exact derived pullback compositor.  It does not yet prove compatibility of
these isomorphisms with the triangulated shift, characterize exact pullback by a
geometric flatness criterion, or construct nonexact left-derived pullback.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h8v.s14.08124709e676 from=translated src=- shape=93fd4c33 vocab=4953abfe
-/
@[reassoc]
theorem complexPullback_associativity
    {T U V W : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) (h : V ⟶ W) :
    (complexPullbackComp f (g ≫ h)).inv ≫
      CategoryTheory.Functor.whiskerRight (complexPullbackComp g h).inv _ ≫
        (CategoryTheory.Functor.associator _ _ _).hom ≫
          CategoryTheory.Functor.whiskerLeft _ (complexPullbackComp f g).hom ≫
            (complexPullbackComp (f ≫ g) h).hom =
      eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  exact congr_app
    (Scheme.Modules.pseudofunctor_associativity f.left g.left h.left)
    (K.X n)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s13.0ee443e34494 from=translated src=- shape=6f9aeaf9 vocab=fde450ce
-/
@[reassoc]
theorem complexPullback_left_unitality
    {T U : SchemeBaseChange S} (f : T ⟶ U) :
    (complexPullbackComp f (𝟙 U)).inv ≫
      CategoryTheory.Functor.whiskerRight (complexPullbackId U).hom (complexPullback f) ≫
        (CategoryTheory.Functor.leftUnitor _).hom =
      eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  exact congr_app
    (Scheme.Modules.pseudofunctor_left_unitality f.left)
    (K.X n)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h4v.s13.022d82938b21 from=translated src=- shape=5d261f1a vocab=14ab3b16
-/
@[reassoc]
theorem complexPullback_right_unitality
    {T U : SchemeBaseChange S} (f : T ⟶ U) :
    (complexPullbackComp (𝟙 T) f).inv ≫
      CategoryTheory.Functor.whiskerLeft (complexPullback f) (complexPullbackId T).hom ≫
        (CategoryTheory.Functor.rightUnitor _).hom =
      eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  exact congr_app
    (Scheme.Modules.pseudofunctor_right_unitality f.left)
    (K.X n)

/-- Equality of scheme base-change morphisms induces a canonical isomorphism
between their pullback functors on cochain complexes.-/
def complexPullbackCongr {T U : SchemeBaseChange S}
    {f g : T ⟶ U} (h : f = g) :
    complexPullback f ≅ complexPullback g := by
  subst g
  exact Iso.refl _

/-- Equality of exact scheme base-change morphisms induces a canonical
isomorphism between their derived pullback functors.-/
def derivedPullbackCongr {T U : SchemeBaseChange S}
    {f g : T ⟶ U} [IsExactPullback f] [IsExactPullback g]
    (h : f = g) : derivedPullback f ≅ derivedPullback g := by
  letI : Localization.Lifting (SchemeDerivedCategory.Q U.left)
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
      (complexPullback f ⋙ SchemeDerivedCategory.Q T.left)
      (derivedPullback f) := ⟨derivedPullbackFactors f⟩
  letI : Localization.Lifting (SchemeDerivedCategory.Q U.left)
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
      (complexPullback g ⋙ SchemeDerivedCategory.Q T.left)
      (derivedPullback g) := ⟨derivedPullbackFactors g⟩
  exact Localization.liftNatIso (SchemeDerivedCategory.Q U.left)
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
    (complexPullback f ⋙ SchemeDerivedCategory.Q T.left)
    (complexPullback g ⋙ SchemeDerivedCategory.Q T.left)
    (derivedPullback f) (derivedPullback g)
    (CategoryTheory.Functor.isoWhiskerRight (complexPullbackCongr h)
      (SchemeDerivedCategory.Q T.left))

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
