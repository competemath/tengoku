/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.AlgebraicGeometry.ResidueField
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.Scheme

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residue-field fibers of a scheme-indexed categorical family

For a scheme base change `T ⟶ S` and a point `x : T`, Mathlib constructs the
canonical morphism `Spec κ(x) ⟶ T`.  This file regards its composite with
`T ⟶ S` as an object of `Over S`, then evaluates a client-supplied
`SchemeTriangulatedFiberFamily S` there. The family's contravariant
pseudofunctor supplies categorical and Grothendieck-group restriction to the
residue fiber.

The residue-field schemes and morphisms are genuine geometric objects.  The
triangulated categories and pullback functors remain client data: no derived
category, derived base-change theorem, geometric slicing witness, relative HN
structure, openness, boundedness, moduli construction, or Theorem 22.2
conclusion is asserted.
-/

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u w

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The residue-field base change of `T ⟶ S` at a point of `T`.-/
def residue (T : SchemeBaseChange S) (x : T.left) : SchemeBaseChange S :=
  Over.mk (T.left.fromSpecResidueField x ≫ T.hom)

/--
@isnad1 id=eq.0h3v.s5.8adfc8d2a7c1 from=translated src=- shape=b213dbaf vocab=3777862e
-/
@[simp]
theorem residue_left (T : SchemeBaseChange S) (x : T.left) :
    (T.residue x).left = Spec (T.left.residueField x) :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.31162a8b0301 from=translated src=- shape=24c376d4 vocab=1ded6979
-/
@[simp]
theorem residue_hom (T : SchemeBaseChange S) (x : T.left) :
    (T.residue x).hom = T.left.fromSpecResidueField x ≫ T.hom :=
  rfl

/-- The canonical morphism from a residue-field base change to the original
scheme over `S`.-/
def residueTo (T : SchemeBaseChange S) (x : T.left) : T.residue x ⟶ T :=
  Over.homMk (T.left.fromSpecResidueField x) (by rfl)

/--
@isnad1 id=eq.0h3v.s5.388405e0c475 from=translated src=- shape=d40de3dd vocab=e3498b61
-/
@[simp]
theorem residueTo_left (T : SchemeBaseChange S) (x : T.left) :
    (T.residueTo x).left = T.left.fromSpecResidueField x :=
  rfl

end SchemeBaseChange

namespace SchemeTriangulatedFiberFamily

variable {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)

/-- The triangulated residue fiber over a point of a scheme base change.-/
abbrev ResidueFiber (T : SchemeBaseChange S) (x : T.left) : Type w :=
  F.Fiber (T.residue x)

/-- Restriction from the category over `T` to its residue fiber at `x`.-/
abbrev pullToResidue (T : SchemeBaseChange S) (x : T.left) :
    F.Fiber T ⥤ F.ResidueFiber T x :=
  F.pull (T.residueTo x)

/-- Pullback on Grothendieck groups from `T` to its residue fiber.-/
abbrev pullK₀ToResidue (T : SchemeBaseChange S) (x : T.left) :
    K₀ (F.Fiber T) →+ K₀ (F.ResidueFiber T x) :=
  F.pullK₀ (T.residueTo x)

/--
@isnad1 id=eq.0h5v.s13.7039eee53a31 from=translated src=- shape=0b118bf9 vocab=32bc2554
-/
theorem pullK₀ToResidue_of (T : SchemeBaseChange S) (x : T.left)
    (E : F.Fiber T) :
    F.pullK₀ToResidue T x (K₀.of _ E) =
      K₀.of _ ((F.pullToResidue T x).obj E) :=
  F.pullK₀_of (T.residueTo x) E

end SchemeTriangulatedFiberFamily

end

end AlgebraicGeometry.DerivedCategory.Families
