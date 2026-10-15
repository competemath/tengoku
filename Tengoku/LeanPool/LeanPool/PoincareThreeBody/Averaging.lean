/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.Resonance
public import Tengoku

/-!
# Averaging the first homological equation

On a resonant periodic orbit, the first-order correction to a putative first integral is periodic.
Integrating its derivative over one period removes that term. A nonzero averaged perturbation then
forces the leading differential of the integral to annihilate the resonance vector.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

open MeasureTheory Set
open scoped Interval

/-- The derivative of a periodic scalar function has zero integral over a period.
@isnad1 id=eq.3h3v.s7.3041f7681d3f from=translated src=- shape=04af65b9 vocab=700a6062
-/
theorem intervalIntegral_derivative_eq_zero_of_endpoints_eq
    {correction correctionDerivative : ℝ → ℝ} {period : ℝ}
    (hderiv : ∀ time ∈ uIcc 0 period,
      HasDerivAt correction (correctionDerivative time) time)
    (hintegrable : IntervalIntegrable correctionDerivative volume 0 period)
    (hperiodic : correction period = correction 0) :
    ∫ time in 0..period, correctionDerivative time = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable, hperiodic, sub_self]

/-- If a first homological equation is a periodic total derivative plus a forcing term, then the
forcing has zero average over the period.
@isnad1 id=eq.5h4v.s7.54d5471ce88d from=translated src=- shape=3669b824 vocab=516a500c
-/
theorem intervalIntegral_forcing_eq_zero_of_homologicalEquation
    {correction correctionDerivative forcing : ℝ → ℝ} {period : ℝ}
    (hderiv : ∀ time ∈ uIcc 0 period,
      HasDerivAt correction (correctionDerivative time) time)
    (hcorrectionIntegrable : IntervalIntegrable correctionDerivative volume 0 period)
    (hforcingIntegrable : IntervalIntegrable forcing volume 0 period)
    (hperiodic : correction period = correction 0)
    (hequation : ∀ time ∈ uIcc 0 period,
      correctionDerivative time + forcing time = 0) :
    ∫ time in 0..period, forcing time = 0 := by
  have hderivativeIntegral : ∫ time in 0..period, correctionDerivative time = 0 :=
    intervalIntegral_derivative_eq_zero_of_endpoints_eq hderiv hcorrectionIntegrable hperiodic
  have hequationIntegral :
      ∫ time in 0..period, correctionDerivative time + forcing time = 0 := by
    rw [intervalIntegral.integral_congr fun time htime ↦ hequation time htime]
    simp
  rw [intervalIntegral.integral_add hcorrectionIntegrable hforcingIntegrable,
    hderivativeIntegral, zero_add] at hequationIntegral
  exact hequationIntegral

/-- Averaging a scalar first homological equation over a periodic orbit kills its correction
term.
@isnad1 id=eq.6h5v.s7.9a04d1f13eb8 from=translated src=- shape=092d8351 vocab=c22f6861
-/
theorem coefficient_eq_zero_of_averaged_homologicalEquation
    {correction correctionDerivative forcing : ℝ → ℝ} {coefficient period : ℝ}
    (hderiv : ∀ time ∈ uIcc 0 period,
      HasDerivAt correction (correctionDerivative time) time)
    (hcorrectionIntegrable : IntervalIntegrable correctionDerivative volume 0 period)
    (hforcingIntegrable : IntervalIntegrable forcing volume 0 period)
    (hperiodic : correction period = correction 0)
    (hforcing : ∫ time in 0..period, forcing time ≠ 0)
    (hequation : ∀ time ∈ uIcc 0 period,
      correctionDerivative time + coefficient * forcing time = 0) :
    coefficient = 0 := by
  have hderivativeIntegral : ∫ time in 0..period, correctionDerivative time = 0 :=
    intervalIntegral_derivative_eq_zero_of_endpoints_eq hderiv hcorrectionIntegrable hperiodic
  have hequationIntegral :
      ∫ time in 0..period,
          correctionDerivative time + coefficient * forcing time = 0 := by
    rw [intervalIntegral.integral_congr fun time htime ↦ hequation time htime]
    simp
  rw [intervalIntegral.integral_add hcorrectionIntegrable
      (hforcingIntegrable.const_mul coefficient),
    intervalIntegral.integral_const_mul, hderivativeIntegral, zero_add] at hequationIntegral
  exact (mul_eq_zero.mp hequationIntegral).resolve_right hforcing

/-- A nonzero averaged perturbation on a resonant orbit yields Poincaré's two-dimensional
linear-dependence obstruction.
@isnad1 id=not.8h7v.s8.718a3b08d249 from=translated src=- shape=25c5b82a vocab=190ffdba
-/
theorem averagedHomologicalEquation_obstruction
    {k frequency differential : ActionSpace}
    {correction correctionDerivative forcing : ℝ → ℝ} {period : ℝ}
    (hk : k ≠ 0) (hresonance : dot k frequency = 0)
    (hderiv : ∀ time ∈ uIcc 0 period,
      HasDerivAt correction (correctionDerivative time) time)
    (hcorrectionIntegrable : IntervalIntegrable correctionDerivative volume 0 period)
    (hforcingIntegrable : IntervalIntegrable forcing volume 0 period)
    (hperiodic : correction period = correction 0)
    (hforcing : ∫ time in 0..period, forcing time ≠ 0)
    (hequation : ∀ time ∈ uIcc 0 period,
      correctionDerivative time + dot k differential * forcing time = 0) :
    ¬LinearIndependent ℝ ![frequency, differential] := by
  have hdifferential : dot k differential = 0 :=
    coefficient_eq_zero_of_averaged_homologicalEquation hderiv hcorrectionIntegrable
      hforcingIntegrable hperiodic hforcing hequation
  exact not_linearIndependent_of_common_resonance hk hresonance hdifferential

end LeanPool.PoincareThreeBody
