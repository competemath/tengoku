/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.Estimates
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlatePower
public import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ambient-dimension seed for the plate induction

Every thickened disk contains a ball of the same positive radius. Hölder
and the volume scaling of balls give deficit `n` at every exponent `p ≥ 1`.
In particular this starts the induction with zero-dimensional disks in
ambient dimension equal to the final codimension.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n k : ℕ} {δ p : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

/--
@isnad1 id=le.3h6v.s9.3f016d5f9ff1 from=translated src=- shape=42fad62e vocab=8dda756a
-/
theorem plateMaximal_rpow_le_ball_volume (hδ : 0 < δ) (hp : 1 ≤ p)
    (hf : Measurable f) (V : Grassmannian n k) :
    plateMaximal δ f V ^ p ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ))⁻¹ * ∫⁻ x, f x ^ p := by
  rw [← ENNReal.le_rpow_inv_iff (zero_lt_one.trans_le hp)]
  apply iSup_le
  intro a
  rw [ENNReal.le_rpow_inv_iff (zero_lt_one.trans_le hp)]
  apply (plateAverage_rpow_le hδ hp V.val a hf).trans
  have hvol : volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) ≤ volume (plate δ V.val a) := by
    rw [← volume.addHaar_ball_center a]
    exact measure_mono (ball_subset_thickening (by simp [unitDisk] : a ∈ unitDisk V.val a) δ)
  rw [div_eq_mul_inv, mul_comm]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hvol) (setLIntegral_le_lintegral _ _)

/--
@isnad1 id=le.3h6v.s9.e1f6215581e2 from=translated src=- shape=4fd14e26 vocab=c2a8e618
-/
theorem plateMaximal_le_ball_volume (hδ : 0 < δ) (hp : 1 ≤ p)
    (hf : Measurable f) (V : Grassmannian n k) :
    plateMaximal δ f V ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) ^ (-p⁻¹) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 := zero_lt_one.trans_le hp
  have h := ENNReal.rpow_le_rpow (plateMaximal_rpow_le_ball_volume hδ hp hf V)
    (inv_nonneg.mpr hp0.le)
  rw [ENNReal.rpow_rpow_inv hp0.ne', ENNReal.mul_rpow_of_nonneg _ _
    (inv_nonneg.mpr hp0.le), ← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, neg_one_mul] at h
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, enorm_eq_self, one_div] using h

end NKBesicovitch.Induction
