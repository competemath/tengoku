/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Tengoku

/-!
# Circle argument-principle definitions and local residue

This module provides the normalized logarithmic-derivative integral around a
positively oriented complex circle, the associated multiplicity-weighted zero
count in its open disk, and the local factorization behind their relationship.
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace Causalean.Mathlib.Analysis.Complex.ArgumentPrinciple

/-- For [a complex-valued function](hyp:f), [a complex center](hyp:c), and [a real radius](hyp:R), [the normalized logarithmic-derivative circle integral](goal) is the integral of the function's logarithmic derivative around the positively oriented circle with that center and radius, divided by $2\pi i$.

This quantity is the winding count obtained by integrating the logarithmic derivative of a
complex-valued function around a positively oriented circle and scaling so that one enclosed
simple zero contributes one. -/
def normalizedLogDerivCircleIntegral (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * circleIntegral (logDeriv f) c R

open Classical in
/-- For [a complex-valued function](hyp:f), [a complex center](hyp:c), and [a real radius](hyp:R), [the zero-multiplicity count](goal) is the sum of the analytic multiplicities of all zeros of the function lying strictly inside the open disk with that center and radius, with the standard totalized finite sum used when the support is not finite.

This count adds the analytic multiplicity of every zero strictly inside a given open disk;
outside finite-support settings it uses the standard totalized finite sum. -/
def zeroMultiplicityCount (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℕ :=
  ∑ᶠ z : ℂ, if z ∈ ball c R then analyticOrderNatAt f z else 0

open Classical in
/-- For [a complex-valued function](hyp:f), [a complex center](hyp:c), and [a real radius](hyp:R), [the interior-zero set](goal) consists exactly of the complex numbers that are zeros of the function and lie strictly inside the open disk with that center and radius.

This set comprises exactly the zeros of a complex-valued function that lie strictly inside a
given open disk. -/
def interiorZeros (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : Set ℂ :=
  {z | z ∈ ball c R ∧ f z = 0}

/-- For [a positive radius `R`](hyp:hR) such that [the point `a` lies strictly
inside the open disk of radius `R` centered at `c`](hyp:ha), [the normalized
logarithmic-derivative integral around that circle of the monomial
`z ↦ (z - a)^n` equals `n`](goal). -/
theorem normalizedLogDerivCircleIntegral_centeredMonomial {c a : ℂ} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (ha : a ∈ ball c R) :
    normalizedLogDerivCircleIntegral (fun z ↦ (z - a) ^ n) c R = (n : ℂ) := by
  have hlogDeriv : logDeriv (fun z : ℂ ↦ (z - a) ^ n) =
      fun z ↦ (n : ℂ) * (z - a)⁻¹ := by
    funext z
    rw [logDeriv_fun_pow (by fun_prop)]
    simp [logDeriv_apply, div_eq_mul_inv]
  rw [normalizedLogDerivCircleIntegral, hlogDeriv,
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball ha]
  field_simp

end Causalean.Mathlib.Analysis.Complex.ArgumentPrinciple
