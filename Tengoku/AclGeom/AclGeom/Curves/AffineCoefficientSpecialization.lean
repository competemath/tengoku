/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.PointwiseFaithfulness
import Tengoku.Seed.LinearAlgebra.TensorProduct.Basis
import Tengoku.Seed.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Tengoku.Seed.FieldTheory.Finiteness
import Tengoku.Seed.Data.Fin.VecNotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rational affine coefficients from point specializations

**Status:** proved algebraic inputs for `SchemeAffineParameters` (#21). The Cramer criterion
constructs a nonzero common denominator from pointwise affine tensor identities over an ACF
base. The two-parameter criterion proves a finite field extension and transcendence basis.
Its algebraicity and rank premises are explicit; the actual group consumer derives them.
These are algebraic criteria, not a scheme finite-cover or full curve-action classifier.
-/

namespace AclGeom.AffineCoefficients

noncomputable section

open scoped TensorProduct

section Evaluation

variable {k F A : Type*} [CommRing k] [CommRing F] [Algebra k F]
  [CommRing A] [Algebra k A]

/-- Evaluate only the parameter coefficients. Named consumers: the Cramer criterion and
 the actual parameter/point function-field comparison.-/
def tensorPointEval (φ : A →ₐ[k] k) : A ⊗[k] F →ₐ[k] F :=
  Algebra.TensorProduct.lift ((Algebra.ofId k F).comp φ) (AlgHom.id k F)
    (fun _ _ ↦ Commute.all _ _)

/-- Evaluating coefficients specializes scalar multiplication as well.
 Named consumer: the localized affine formula for the actual point action.-/
theorem tensorPointEval_smul (φ : A →ₐ[k] k) (a : A) (z : A ⊗[k] F) :
    tensorPointEval φ (a • z) = φ a • tensorPointEval φ z := by
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  change tensorPointEval φ ((a ⊗ₜ[k] (1 : F)) * z) = φ a • tensorPointEval φ z
  rw [map_mul, Algebra.smul_def]
  have h_eval : tensorPointEval φ (a ⊗ₜ[k] (1 : F)) = algebraMap k F (φ a) := by
    change algebraMap k F (φ a) * 1 = _
    exact mul_one _
  rw [h_eval]

end Evaluation

variable {k F A : Type*} [Field k] [Field F] [Algebra k F]
  [CommRing A] [Algebra k A]

end

end AclGeom.AffineCoefficients

namespace AclGeom.AffineCoefficients

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin

end

end AclGeom.AffineCoefficients
