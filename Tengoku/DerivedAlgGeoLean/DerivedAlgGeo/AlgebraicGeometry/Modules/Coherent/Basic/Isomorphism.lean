/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Basic.Definitions
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Presentation.Isomorphism

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Isomorphism invariance of coherent sheaves

Finite presentation is invariant under isomorphism on an arbitrary ringed site by
`Algebra.Category.ModuleCat.Sheaf.Presentation.Isomorphism`. This geometric consumer records
that coherent sheaves on a scheme are therefore closed under isomorphisms in the ambient category
of sheaves of modules.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Coherent sheaves on `X` are closed under isomorphisms in `X.Modules`.
@isnad1 id=isclosed.0h1v.s3.33c33e0007ea from=translated src=- shape=fc2c1e2b vocab=23799ec7
-/
instance coherent_isClosedUnderIsomorphisms :
    (coherent X).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    change SheafOfModules.IsFinitePresentation N
    change SheafOfModules.IsFinitePresentation M at hM
    exact SheafOfModules.IsFinitePresentation.of_iso
      (R := X.ringCatSheaf) (M := M) (N := N) e hM

end AlgebraicGeometry.Scheme
