module
public import Tengoku.SpherePackingExt.SpherePacking.MagicFunction.IntegralParametrisations
import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.DerivHelpers
public import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
public import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exponential bookkeeping for special values

Both the `a`- and `b`-special-value files use the same exponential `exp(π i u z)` and the same
periodicity-by-1 identities along the standard contour parametrisations `z₁'`, `z₃'`, `z₅'`.

This file factors these shared definitions/lemmas into one place to avoid import-time name
collisions when mixing the `A.SpecialValues` and `B.SpecialValues` developments.
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped Real
open Complex
open MagicFunction.Parametrisations

namespace SpecialValuesAux

/-- Exponential factor `exp(π i u z)` used throughout the contour-integral decompositions.-/
@[expose]
public def expU (u : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (u : ℂ) * z)

/-- Additivity in the contour variable for `expU`: `expU u (z + w) = expU u z * expU u w`.-/
public lemma expU_add (u : ℝ) (z w : ℂ) : expU u (z + w) = expU u z * expU u w := by
  simp [expU, mul_add, mul_assoc, Complex.exp_add]

/-- The special case of `expU_add` for `w = 1`.-/
public lemma expU_add_one_mul (u : ℝ) (z : ℂ) :
    expU u (z + 1) = expU u z * expU u 1 := by
  simpa using expU_add (u := u) (z := z) (w := (1 : ℂ))

/-- Rearrangement of `expU_add_one_mul` isolating `expU u z`.-/
public lemma expU_add_one_mul_inv (u : ℝ) (z : ℂ) (hw : expU u 1 ≠ 0) :
    expU u z = expU u (z + 1) * (expU u 1)⁻¹ := by
  have h := congrArg (fun w : ℂ => w * (expU u 1)⁻¹) (expU_add_one_mul (u := u) (z := z))
  simpa [mul_assoc, hw] using h.symm

end SpecialValuesAux

end

end SpherePacking.Dim24
