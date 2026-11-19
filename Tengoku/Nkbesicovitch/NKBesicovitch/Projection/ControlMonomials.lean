/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
public import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The common monomial in the controlled inner and outer estimates

Both coefficient formulas reduce to the same positive monomial in the
input constant and the inverse separation radius.
-/

@[expose] public section

namespace NKBesicovitch.Projection

/-- The shared coefficient of the controlled inner-code and outer estimates.-/
noncomputable def controlCoefficient (m : ℕ) (β r C : ℝ) : ℝ :=
  (2 * C) ^ (1 / (β - 1)) * (r⁻¹) ^ ((m : ℝ) * ((β + 1) / (β - 1)))

/--
@isnad1 id=lt.2h4v.s5.b0c7ee6a1ef3 from=translated src=- shape=0d609fd4 vocab=c5ac1e9c
-/
theorem controlCoefficient_pos (m : ℕ) (β : ℝ) {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    0 < controlCoefficient m β r C := by
  unfold controlCoefficient
  positivity

/--
@isnad1 id=eq.2h4v.s7.30c159e78903 from=translated src=- shape=06998b09 vocab=08e68aec
-/
theorem inner_controlCoefficient_eq (m : ℕ) (β : ℝ) {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    (2 * r⁻¹ ^ m * C) ^ (1 / (β - 1)) / (r ^ m) ^ (β / (β - 1)) =
      controlCoefficient m β r C := by
  unfold controlCoefficient
  rw [show 2 * r⁻¹ ^ m * C = (2 * C) * r⁻¹ ^ m by ring,
    Real.mul_rpow (by positivity) (by positivity)]
  rw [div_eq_mul_inv, ← Real.inv_rpow (pow_nonneg hr.le _) _, ← inv_pow]
  simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hr.le)]
  rw [mul_assoc, ← Real.rpow_add (inv_pos.mpr hr)]
  congr 2
  ring

/--
@isnad1 id=eq.2h4v.s7.a274e68499fa from=translated src=- shape=2d6f7904 vocab=08e68aec
-/
theorem outer_controlCoefficient_eq (m : ℕ) (β : ℝ) {r C : ℝ} (hr : 0 < r) (hC : 0 < C) :
    ((2 * (r⁻¹ ^ m) ^ 2 * C) * (r⁻¹ ^ m) ^ (β - 1)) ^ (1 / (β - 1)) =
      controlCoefficient m β r C := by
  unfold controlCoefficient
  rw [show (2 * (r⁻¹ ^ m) ^ 2 * C) * (r⁻¹ ^ m) ^ (β - 1) =
      (2 * C) * ((r⁻¹ ^ m) ^ 2 * (r⁻¹ ^ m) ^ (β - 1)) by ring,
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast (r⁻¹ ^ m) 2,
    ← Real.rpow_add (pow_pos (inv_pos.mpr hr) m)]
  simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hr.le)]
  congr 2
  ring

end NKBesicovitch.Projection
