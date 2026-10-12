/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Code4me2
-/

module

public import Tengoku.LeanPool.LeanPool.NavierStokesAndEuler.ForMathlib.SmoothCutoff
public import Tengoku

/-!
# The homogeneous `H¹ → L⁶` inequality on `ℝ³`

Mathlib's Gagliardo–Nirenberg–Sobolev inequality
`eLpNorm_le_eLpNorm_fderiv_of_eq_inner` bounds the `L⁶` norm of a compactly
supported `C¹` function on `ℝ³` by `sobolevConstant` times the `L²` norm of its
derivative.  This module fixes that constant once for both libraries and removes
the support hypothesis: multiplying by the dilated cutoffs of `NavierStokesAndEuler.SmoothCutoff`
costs a derivative error `derivativeConstant 1 / R * ‖f‖₂` that vanishes as
`R → ∞`, and Fatou's lemma (`Lp.eLpNorm_lim_le_liminf_eLpNorm`) passes to the
limit.  The result `eLpNorm_six_le` needs only `f ∈ L²`; when the derivative is
also in `L²`, `memLp_six` and the real-valued forms follow.

The exponents and spatial dimension are fixed, while the codomain is any real
inner-product space. The compact-support, extended-norm, membership, and
real-valued formulations share the same constant.
-/

public section

noncomputable section

open MeasureTheory Filter NavierStokesAndEuler.SmoothCutoff
open scoped ContDiff ENNReal NNReal Topology

namespace NavierStokesAndEuler.SobolevThreeDimensional

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The fixed whole-space `H¹ → L⁶` Sobolev constant in dimension three. -/
@[expose] def sobolevConstant : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure ℝ³) 2

theorem sobolevConstant_nonneg : 0 ≤ (sobolevConstant : ℝ) := NNReal.coe_nonneg _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end NavierStokesAndEuler.SobolevThreeDimensional
