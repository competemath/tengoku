/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.CauchyFormula
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.PowerSeries
import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.Analysis.Complex.TaylorSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Taylor expansion on a complex disc

This file explicitly bridges `HolomorphicOnTextbook` to Mathlib differentiability before using
Mathlib's analytic machinery. It never treats `AnalyticAt` as the library's textbook definition.

Current entry:

* `complex-analysis.series.taylor`: Taylor expansion on a specified open disc, the derivative and
  circle-integral coefficient formulas, and uniqueness of local power-series coefficients.
-/

open scoped ENNReal

noncomputable section

namespace SandronesLibrary.ComplexAnalysis

/-- The `n`th Taylor coefficient of `f` at the specified centre `c`.

> **Entry**: complex-analysis.series.taylor-/
def taylorCoefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ)⁻¹ * iteratedDeriv n f c

/-- The Taylor-series sum, expressed through this library's complex power-series interface.

> **Entry**: complex-analysis.series.taylor-/
def taylorExpansion (f : ℂ → ℂ) (c z : ℂ) : ℂ :=
  complexPowerSeries (taylorCoefficient f c) c z

/-- A textbook-holomorphic function on `ball c R` is the sum of its Taylor series centred at `c`
at every point of that same disc. This guarantees convergence throughout the given disc; it does
not assert that `R` is the exact or maximal radius of convergence.

> **Entry**: complex-analysis.series.taylor-/
theorem hasSum_taylorSeries_on_ball {f : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hf : HolomorphicOnTextbook f (Metric.ball c R)) (hz : z ∈ Metric.ball c R) :
    HasSum (fun n : ℕ ↦ taylorCoefficient f c n * (z - c) ^ n) (f z) := by
  have hd : DifferentiableOn ℂ f (Metric.ball c R) :=
    (holomorphicOnTextbook_iff_differentiableOn Metric.isOpen_ball).mp hf
  simpa [taylorCoefficient, mul_comm, mul_left_comm, mul_assoc] using
    Complex.hasSum_taylorSeries_on_ball hd hz

/-- Pointwise equality between a holomorphic function and its Taylor expansion on the stated open
disc.

> **Entry**: complex-analysis.series.taylor-/
theorem taylorExpansion_eq_on_ball {f : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hf : HolomorphicOnTextbook f (Metric.ball c R)) (hz : z ∈ Metric.ball c R) :
    taylorExpansion f c z = f z := by
  rw [taylorExpansion, complexPowerSeries_eq_tsum]
  exact (hasSum_taylorSeries_on_ball hf hz).tsum_eq

/-- Cauchy's formula identifies the derivative-defined Taylor coefficient with its circle-integral
formula. Holomorphy is assumed on the closed disc so that the boundary integral is available.

> **Entry**: complex-analysis.series.taylor-/
theorem taylorCoefficient_eq_circleIntegral {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : HolomorphicOnTextbook f (Metric.closedBall c R)) (hR : 0 < R) (n : ℕ) :
    taylorCoefficient f c n =
      (∮ z in C(c, R), f z / (z - c) ^ (n + 1)) / (2 * Real.pi * Complex.I) := by
  rw [cauchy_integral_formula_iteratedDeriv hf hR n]
  simp only [taylorCoefficient]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- Local power-series coefficients of a complex function at a fixed centre are unique. Thus the
derivative-defined Taylor coefficients cannot be replaced by a different local coefficient sequence
representing the same function at the same centre.

> **Entry**: complex-analysis.series.taylor-/
theorem powerSeriesCoefficients_unique {f : ℂ → ℂ} {c : ℂ} {a b : ℕ → ℂ}
    (ha : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) c)
    (hb : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ b) c) :
    a = b := by
  have hseries := ha.eq_formalMultilinearSeries hb
  funext n
  have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n) hseries
  simpa using hn

end SandronesLibrary.ComplexAnalysis
