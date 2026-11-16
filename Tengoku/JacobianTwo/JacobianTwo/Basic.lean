/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.Seed.Algebra.MvPolynomial.PDeriv
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shared polynomial-map definitions

This module keeps the finite-dimensional formal Jacobian construction separate
from the specific announced map.
-/

noncomputable section

namespace JacobianTwo

/-- A polynomial self-map of affine `n`-space over `R`.-/
abbrev PolynomialMap (n : Nat) (R : Type*) [CommSemiring R] :=
  Fin n → MvPolynomial (Fin n) R

/-- The formal Jacobian matrix of a polynomial self-map. Rows index outputs;
columns index source variables.-/
def formalJacobian {n : Nat} {R : Type*} [CommSemiring R]
    (F : PolynomialMap n R) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) R) :=
  fun i j ↦ MvPolynomial.pderiv j (F i)

/-- Evaluate every coordinate of a polynomial map at a point.-/
def evalMap {n : Nat} {R : Type*} [CommSemiring R]
    (F : PolynomialMap n R) (p : Fin n → R) : Fin n → R :=
  fun i ↦ MvPolynomial.eval p (F i)

end JacobianTwo
