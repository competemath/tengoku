/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyNaturality
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Degree-zero Hom-complex cohomology classes under localization

The class map induced by degreewise localization agrees, through the linear
class/quotient equivalences, with the localized map on the concrete degree-zero
kernel/range quotient. Exactness of module localization then makes this class
map a localization map. A half-bounded specialization needs finite presentation
only for source terms in `Finset.Icc (c - 1) b`.

This does not identify derived-category Homs or establish geometric base change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (S : Submonoid R)

private abbrev localized (E : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj E

private theorem cochainLocalizedMap_square (i j : ℤ) :
    (δ_hom R (localized S P) (localized S Q) i j).comp
      (cochainLocalizedMap P Q i S) =
    (cochainLocalizedMap P Q j S).comp (δ_hom R P Q i j) := by
  apply LinearMap.ext
  intro γ
  change δ i j ((cochainLocalizedMap P Q i S) γ) =
    (cochainLocalizedMap P Q j S) (δ i j γ)
  exact (cochainLocalizedMap_delta P Q i S j γ).symm

/-- The degree-zero map on Hom-complex cohomology classes induced by
degreewise localization of both complexes.-/
def cohomologyClassLocalizedMap :
    CohomologyClass P Q 0 →ₗ[R]
      CohomologyClass (localized S P) (localized S Q) 0 :=
  cohomologyClassMapLinear P Q 0 (localized S P) (localized S Q)
    (cochainLocalizedMap P Q (0 - 1) S)
    (cochainLocalizedMap P Q 0 S)
    (cochainLocalizedMap P Q (0 + 1) S)
    (cochainLocalizedMap_square P Q S (0 - 1) 0)
    (cochainLocalizedMap_square P Q S 0 (0 + 1))

end

end CochainComplex.HomComplex
