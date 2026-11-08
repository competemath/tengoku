module

public import Tengoku.Seed.Analysis.Calculus.ParametricIntegral
public import Tengoku.Seed.Analysis.Normed.Group.Basic
public import Tengoku.Seed.Data.Complex.Basic
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
public import Tengoku.Seed.Order.Interval.Set.UnorderedInterval
public import Tengoku.SpherePackingExt.SpherePacking.Integration.Measure
import Tengoku.Seed.Topology.Basic
import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.DerivHelpers
import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.IteratedDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differentiation under the integral sign on `(0, 1)`

This file provides lemmas for differentiating functions of the form
`x ↦ ∫ t in Ioo (0 : ℝ) 1, hf t * exp (x * coeff t)`.

It is dimension-agnostic and is used by both the dimension-8 and dimension-24 developments.
-/

namespace SpherePacking.Integration.DifferentiationUnderIntegral
noncomputable section

open scoped Topology Interval
open Complex Real Set MeasureTheory Filter intervalIntegral
open SpherePacking.Integration (μIoo01)

variable {coeff hf : ℝ → ℂ}

/-- The basic integrand `t ↦ hf t * exp (x * coeff t)` on `(0, 1)`.-/
@[expose] public def g (x t : ℝ) : ℂ := hf t * cexp ((x : ℂ) * coeff t)

/-- The auxiliary integrand `gN n`, corresponding to the `n`-th derivative in `x`.-/
@[expose] public def gN (n : ℕ) (x t : ℝ) : ℂ :=
  (coeff t) ^ n * g (coeff := coeff) (hf := hf) x t

lemma norm_cexp_mul_coeff_le
    (coeff_norm_le : ∀ t : ℝ, ‖coeff t‖ ≤ 2 * Real.pi)
    {x x₀ : ℝ} (t : ℝ) (hx : x ∈ Metric.ball x₀ (1 : ℝ)) :
    ‖cexp ((x : ℂ) * coeff t)‖ ≤ Real.exp ((|x₀| + 1) * (2 * Real.pi)) :=
  SpherePacking.ForMathlib.norm_cexp_ofReal_mul_le_exp_mul_of_norm_le (c := coeff t)
    (B := (2 * Real.pi)) (coeff_norm_le t) hx

end

end SpherePacking.Integration.DifferentiationUnderIntegral
