/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Distributions.InverseGamma.Basic
public import Tengoku

import Tengoku.Tauceti.TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of the inverse-gamma distribution

This file proves the natural moments, mean, variance, sharp moment thresholds, and exact
exponential-integrability domain of the inverse-gamma distribution.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {a r t : ℝ}

/-! ### Moments -/

/-- A natural power is integrable under a valid inverse-gamma law exactly below the shape. -/
@[simp]
theorem integrable_pow_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (inverseGammaMeasure a r) ↔ (n : ℝ) < a := by
  rw [inverseGammaMeasure_of_pos ha hr,
    integrable_map_measure (by fun_prop) measurable_inv.aemeasurable]
  simpa only [Function.comp_def, inv_pow] using
    TauCeti.Probability.integrable_inv_pow_gammaMeasure_iff ha hr n

/-- **Natural moments of a valid inverse-gamma law.**  The `n`th moment exists for `n < a` and
equals `r ^ n * Gamma (a - n) / Gamma a`. -/
@[simp]
theorem integral_pow_inverseGammaMeasure (hr : 0 < r) (n : ℕ)
    (hn : (n : ℝ) < a) :
    ∫ x, x ^ n ∂inverseGammaMeasure a r =
      r ^ n * Real.Gamma (a - n) / Real.Gamma a := by
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) hn
  rw [inverseGammaMeasure_of_pos ha hr,
    integral_map measurable_inv.aemeasurable (by fun_prop)]
  simpa only [inv_pow] using TauCeti.Probability.integral_inv_pow_gammaMeasure hr n hn

/-- The mean of an inverse-gamma law is `r / (a - 1)` when `1 < a`. -/
@[simp]
theorem integral_id_inverseGammaMeasure (hr : 0 < r) (ha : 1 < a) :
    ∫ x, x ∂inverseGammaMeasure a r = r / (a - 1) := by
  have h := integral_pow_inverseGammaMeasure hr 1 (by simpa using ha)
  have hgamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    simpa using Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  simp only [pow_one, Nat.cast_one] at h
  rw [h, hgamma]
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < a - 1)).ne']

/-- The second raw moment of an inverse-gamma law is
`r² / ((a - 1) * (a - 2))` when `2 < a`. -/
@[simp high]
theorem integral_sq_inverseGammaMeasure (hr : 0 < r) (ha : 2 < a) :
    ∫ x, x ^ 2 ∂inverseGammaMeasure a r = r ^ 2 / ((a - 1) * (a - 2)) := by
  have h := integral_pow_inverseGammaMeasure hr 2 (by simpa using ha)
  have hgamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    simpa using Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  have hshift : a - 2 + 1 = a - 1 := by ring
  have hgamma' : Real.Gamma (a - 1) = (a - 2) * Real.Gamma (a - 2) := by
    simpa [hshift] using Real.Gamma_add_one (by linarith : a - 2 ≠ 0)
  norm_num only [Nat.cast_ofNat] at h
  rw [h, hgamma, hgamma']
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < a - 2)).ne']

/-- The identity is integrable under a valid inverse-gamma law exactly above shape one. -/
@[simp]
theorem integrable_id_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) :
    Integrable id (inverseGammaMeasure a r) ↔ 1 < a := by
  simpa only [Function.id_def, pow_one, Nat.cast_one] using
    integrable_pow_inverseGammaMeasure_iff ha hr 1

/-- At and below shape one, the identity is not integrable under a valid inverse-gamma law. -/
theorem not_integrable_id_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (h : a ≤ 1) :
    ¬ Integrable id (inverseGammaMeasure a r) :=
  (integrable_id_inverseGammaMeasure_iff ha hr).not.mpr (not_lt.mpr h)

/-- At and below shape two, the square is not integrable under a valid inverse-gamma law. -/
theorem not_integrable_sq_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (h : a ≤ 2) :
    ¬ Integrable (fun x : ℝ ↦ x ^ 2) (inverseGammaMeasure a r) :=
  (integrable_pow_inverseGammaMeasure_iff ha hr 2).not.mpr (by simpa using h)

/-! ### Exponential moments -/

end Probability

end TauCeti
