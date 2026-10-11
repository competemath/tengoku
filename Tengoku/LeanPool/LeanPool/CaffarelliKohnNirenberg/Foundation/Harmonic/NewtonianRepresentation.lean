/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Newtonian
public import Tengoku

/-!
# Newtonian Representation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Interval
open MeasureTheory MeasureTheory.Measure Set Filter

noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

/-! The Newtonian kernel representation obtained from the heat semigroup. -/

/-- The positive three-dimensional Newtonian kernel. -/
def newtonianKernel (z : Vec3) : ℝ :=
  1 / (4 * Real.pi * vec3EuclideanNorm z)

lemma newtonianKernel_locallyIntegrable :
    LocallyIntegrable newtonianKernel volume := by
  have hnorm : Continuous (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hmeas : AEStronglyMeasurable newtonianKernel volume := by
    exact (measurable_const.div (measurable_const.mul hnorm.measurable)).aestronglyMeasurable
  refine locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ)
    (C := (4 * Real.pi)⁻¹) (α := (1 : ℝ)) ?_ (by norm_num) ?_ hmeas
  · change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ)
    rw [Module.finrank_fin_fun]
    norm_num
  · filter_upwards [] with z
    by_cases hz : z = 0
    · subst z
      simp [newtonianKernel, vec3EuclideanNorm]
    · have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hrn : 0 < vec3EuclideanNorm z :=
        lt_of_lt_of_le hzn (CKN.space_norm_le_euclideanNorm z)
      have hinv : (vec3EuclideanNorm z)⁻¹ ≤ ‖z‖⁻¹ := by
        exact (inv_le_inv₀ hrn hzn).2 (CKN.space_norm_le_euclideanNorm z)
      rw [newtonianKernel, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [show 1 / (4 * Real.pi * vec3EuclideanNorm z) =
          (4 * Real.pi)⁻¹ * (vec3EuclideanNorm z)⁻¹ by field_simp]
      have hrpow : ‖z‖ ^ (-1 : ℝ) = ‖z‖⁻¹ := by
        rw [Real.rpow_neg (norm_nonneg z), Real.rpow_one]
      rw [hrpow]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)

end CKN.Foundation.Heat
