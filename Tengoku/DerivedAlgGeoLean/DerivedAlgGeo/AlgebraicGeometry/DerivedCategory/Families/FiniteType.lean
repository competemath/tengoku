/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.FiniteType
import Tengoku.Seed.AlgebraicGeometry.Morphisms.QuasiCompact
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.Scheme

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-type scheme base changes

This neutral geometric predicate is shared by derived-category families,
moduli problems, and stability applications. It does not impose stability data.
-/

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory AlgebraicGeometry

universe u

/-- A scheme base change is of finite type when its structure morphism is
locally of finite type and quasi-compact.-/
def IsFiniteTypeBaseChange {S : Scheme.{u}} (T : SchemeBaseChange S) : Prop :=
  LocallyOfFiniteType T.hom ∧ QuasiCompact T.hom

end AlgebraicGeometry.DerivedCategory.Families
