import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.GradedModuleHomCategory
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Graded.GradedSubmodule
import Tengoku.Seed.CategoryTheory.Idempotents.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Splitting homogeneous idempotents of graded modules -/

set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.Graded.FiniteGradedModule

universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/-- The image of a degree-zero endomorphism as a finite graded module.-/
def imageObject (X : FiniteGradedModule.{u,v} R) (f : X.module →ₗ[A] X.module)
    (hf : X.grading.Homogeneous X.grading 0 f) : FiniteGradedModule.{u,v} R where
  module := ModuleCat.of A f.range
  finite := Module.Finite.of_injective (f.range.subtype.restrictScalars k) Subtype.val_injective
  grading := X.grading.rangeGrading X.grading f hf

end MagnitudeConjecture.Graded.FiniteGradedModule
