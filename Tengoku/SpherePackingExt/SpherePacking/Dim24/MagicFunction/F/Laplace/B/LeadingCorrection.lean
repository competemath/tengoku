module
public import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.MagicFunction.F.Laplace.KernelTools

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Leading correction for the Laplace B-kernel

This file defines the explicit leading term subtracted from `BKernel` on the tail `t ≥ 1` and
evaluates its Laplace transform in the convergent range `u > 2`.

## Main definitions
* `BleadBase`
* `Blead`

## Main statement
* `integral_Ioi_one_Blead_mul_exp_neg_pi`
-/

namespace SpherePacking.Dim24.LaplaceBleading

noncomputable section

open scoped Real
open scoped Topology

open Filter Set MeasureTheory Real

/-- The scalar part of the leading term subtracted from `BKernel` on the tail `t ≥ 1`.-/
@[expose] public def BleadBase (t : ℝ) : ℝ :=
  (1 / 39 : ℝ) * t - (10 / (117 * Real.pi) : ℝ)

/-- The full leading term `((1/39) t - 10/(117π)) e^{2π t}`.-/
@[expose] public def Blead (t : ℝ) : ℝ :=
  BleadBase t * Real.exp (2 * Real.pi * t)

lemma integral_Ioi_one_exp_neg_mul (c : ℝ) (hc : 0 < c) :
    (∫ t : ℝ in Ioi (1 : ℝ), Real.exp (-c * t)) = Real.exp (-c) / c := by
  simpa [neg_mul, mul_assoc, div_eq_mul_inv] using
    (integral_exp_mul_Ioi (a := -c) (by linarith) (c := (1 : ℝ)))

end

end SpherePacking.Dim24.LaplaceBleading
