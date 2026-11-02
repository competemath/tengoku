/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.AffineRelativeProj
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ProjectiveSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Affine charts of projective bundles

On an affine open on which a finite locally free sheaf has rank `n + 1` and a chosen frame, its
symmetric algebra is the standard graded polynomial ring in `n + 1` variables.  This file places
that polynomial algebra in the affine relative-Proj package.  It is the local object glued in the
projective-bundle consumer of the scoped relative-Proj construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace SchemeProjectiveSpace

local instance (R : Type u) [CommRing R] (n : ℕ) :
    GradedAlgebra (grading R n) := MvPolynomial.gradedAlgebra

/-- The degree-zero identification of the standard graded polynomial ring, including its
coefficient-algebra compatibility.-/
noncomputable def degreeZeroAlgEquiv (R : Type u) [CommRing R] (n : ℕ) :
    grading R n 0 ≃ₐ[R] R :=
  { degreeZeroEquiv R n with
    commutes' := by
      intro r
      change MvPolynomial.constantCoeff (MvPolynomial.C r) = r
      simp }

/-- The affine relative-Proj datum for a trivial rank-`n + 1` projective bundle over `U`.-/
noncomputable def trivialProjectiveBundleAffineData (X : Scheme.{u}) (U : X.affineOpens)
    (n : ℕ) : SchemeRelativeProj.AffineData X U where
  A := Polynomial Γ(X, U.1) n
  grading := grading Γ(X, U.1) n
  degreeZeroEquiv := degreeZeroAlgEquiv Γ(X, U.1) n

@[simp]
theorem trivialProjectiveBundleAffineData_scheme (X : Scheme.{u}) (U : X.affineOpens)
    (n : ℕ) :
    (trivialProjectiveBundleAffineData X U n).scheme = space Γ(X, U.1) n :=
  rfl

end SchemeProjectiveSpace
