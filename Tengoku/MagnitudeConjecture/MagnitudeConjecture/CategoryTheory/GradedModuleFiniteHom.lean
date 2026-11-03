import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.GradedModuleHomCategory
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite-dimensional Hom spaces of graded modules -/

set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.Graded.FiniteGradedModule

universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable {R : VectorGrading k A}

/--
@isnad1 id=finitedi.0h5v.s7.685183ee0981 from=translated src=- shape=94522017 vocab=d7b3458a
-/
instance finiteHom (X Y : FiniteGradedModule.{u,v} R) : FiniteDimensional k (X ⟶ Y) := by
  change FiniteDimensional k (X.module →ₗ[A] Y.module)
  exact Module.Finite.of_injective
    (LinearMap.restrictScalarsₗ k A X.module Y.module k) (LinearMap.restrictScalars_injective k)

end MagnitudeConjecture.Graded.FiniteGradedModule
