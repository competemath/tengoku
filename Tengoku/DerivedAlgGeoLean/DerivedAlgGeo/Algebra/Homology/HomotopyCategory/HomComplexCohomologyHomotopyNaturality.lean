/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyClassLocalization
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyHomotopy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Degree-zero class localization in the homotopy category

The degree-zero class-localization map commutes with the functor on homotopy
categories induced by degreewise module localization. This additive square
requires no boundedness, finite-presentation, or K-projectivity hypotheses.
It is not a derived-Hom localization or geometric base-change theorem.

The class-to-homotopy equivalence and its cocycle formula come from the neutral
`HomComplexCohomologyHomotopy` leaf; only the localization square is proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (S : Submonoid R)

private abbrev localizedComplex (E : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj E

private def localizedCocycle (z : Cocycle P Q 0) :
    Cocycle (localizedComplex S P) (localizedComplex S Q) 0 :=
  Cocycle.mk ((cochainLocalizedMap P Q 0 S) z.1) 1 rfl (by
    rw [← cochainLocalizedMap_delta P Q 0 S 1 z.1, Cocycle.δ_eq_zero, map_zero])

end

end CochainComplex.HomComplex
