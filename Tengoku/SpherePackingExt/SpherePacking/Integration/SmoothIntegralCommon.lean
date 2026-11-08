module
public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.DerivHelpers
public import Tengoku.SpherePackingExt.SpherePacking.Integration.DifferentiationUnderIntegral
public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.IteratedDeriv
import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.ExpBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smoothness and decay for integrals on `(0, 1)`

This file is a small wrapper around:
- `SpherePacking.Integration.DifferentiationUnderIntegral` (differentiate under the integral sign),
- `SpherePacking.ForMathlib.IteratedDeriv` (package smoothness from a `HasDerivAt` recurrence).

It also provides a standard one-sided decay argument for integrals whose exponential factor has a
uniform norm formula such as `‖cexp ((x : ℂ) * coeff t)‖ = exp (-π * x)`.
-/

namespace SpherePacking.Integration.SmoothIntegralCommon

noncomputable section

open scoped Interval
open Complex Real Set MeasureTheory Filter intervalIntegral
open SpherePacking.Integration.DifferentiationUnderIntegral

variable {coeff hf : ℝ → ℂ}

/-- The basic family of interval integrals, with the `n`-th derivative integrand `gN n`.-/
@[expose] public def I (n : ℕ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, gN (coeff := coeff) (hf := hf) n x t

end

end SpherePacking.Integration.SmoothIntegralCommon
