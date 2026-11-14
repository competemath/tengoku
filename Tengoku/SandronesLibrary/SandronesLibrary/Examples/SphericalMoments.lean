/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Examples.CoordinateIntegrals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 球体矩：均匀球体的重心与转动惯量

本 Entry 服务理论条目 `analysis.coordinate-integrals.mass-center`（质量、重心与转动惯量）
与 `analysis.multivariable.coordinate-integrals`（球坐标公式）。本文件继续
`CoordinateIntegrals.lean` 的球坐标例题：通过角变量的奇偶性证明均匀球体的三个一阶矩
（重心坐标）均为零，并直接算出绕 `z` 轴的转动惯量 `8πδR⁵/15`，最后把它改写成教材
常见的 `I = (2/5)MR²`（`M = 4πδR³/3` 为球体质量）。

所有计算都保留 Jacobian `ρ² sin φ`，以便与数学分析教材的逐步积分一一对照。

> **Entry**: examples.analysis.spherical-moments
-/

noncomputable section

namespace SandronesLibrary.Examples.SphericalMoments

open SandronesLibrary.Examples.CoordinateIntegrals

open Set MeasureTheory Real
open scoped Interval

lemma integral_Ioo_cos_neg_pi_pi :
    (∫ θ in Ioo (-π) π, cos θ) = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  rw [integral_cos]
  simp

lemma integral_Ioo_sin_neg_pi_pi :
    (∫ θ in Ioo (-π) π, sin θ) = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  rw [integral_sin]
  simp

lemma integral_Ioo_sin_sq_zero_pi :
    (∫ φ in Ioo (0 : ℝ) π, sin φ ^ 2) = π / 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le]
  rw [integral_sin_sq]
  simp

lemma integral_Ioo_sin_mul_cos_zero_pi :
    (∫ φ in Ioo (0 : ℝ) π, sin φ * cos φ) = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le]
  rw [integral_sin_mul_cos₁]
  simp

lemma integral_Ioo_sin_cube_zero_pi :
    (∫ φ in Ioo (0 : ℝ) π, sin φ ^ 3) = 4 / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le]
  rw [integral_sin_pow_three]
  norm_num

lemma integral_Ioo_pow_four_zero_radius {R : ℝ} (hR : 0 ≤ R) :
    (∫ ρ in Ioo (0 : ℝ) R, ρ ^ 4) = R ^ 5 / 5 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR]
  rw [integral_pow]
  norm_num

/-- 均匀球体的 `x` 方向一阶矩为零。-/
theorem uniform_ball_first_moment_x (δ : ℝ) {R : ℝ} :
    (∫ ρ in Ioo (0 : ℝ) R, ∫ θ in Ioo (-π) π,
      ∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * sin φ * cos θ) * (ρ ^ 2 * sin φ))) = 0 := by
  have hphi (ρ θ : ℝ) :
      (∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * sin φ * cos θ) * (ρ ^ 2 * sin φ))) =
          δ * ρ ^ 3 * cos θ * (π / 2) := by
    have heq : (∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * sin φ * cos θ) * (ρ ^ 2 * sin φ))) =
        ∫ φ in Ioo (0 : ℝ) π, (δ * ρ ^ 3 * cos θ) * sin φ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro φ _
      ring
    rw [heq]
    rw [integral_const_mul, integral_Ioo_sin_sq_zero_pi]
  simp_rw [hphi]
  have htheta (ρ : ℝ) :
      (∫ θ in Ioo (-π) π, δ * ρ ^ 3 * cos θ * (π / 2)) = 0 := by
    have heq : (∫ θ in Ioo (-π) π, δ * ρ ^ 3 * cos θ * (π / 2)) =
        ∫ θ in Ioo (-π) π, (δ * ρ ^ 3 * (π / 2)) * cos θ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      ring
    rw [heq]
    rw [integral_const_mul, integral_Ioo_cos_neg_pi_pi, mul_zero]
  simp_rw [htheta]
  simp

/-- 均匀球体的 `y` 方向一阶矩为零。-/
theorem uniform_ball_first_moment_y (δ : ℝ) {R : ℝ} :
    (∫ ρ in Ioo (0 : ℝ) R, ∫ θ in Ioo (-π) π,
      ∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * sin φ * sin θ) * (ρ ^ 2 * sin φ))) = 0 := by
  have hphi (ρ θ : ℝ) :
      (∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * sin φ * sin θ) * (ρ ^ 2 * sin φ))) =
          δ * ρ ^ 3 * sin θ * (π / 2) := by
    have heq : (∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * sin φ * sin θ) * (ρ ^ 2 * sin φ))) =
        ∫ φ in Ioo (0 : ℝ) π, (δ * ρ ^ 3 * sin θ) * sin φ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro φ _
      ring
    rw [heq]
    rw [integral_const_mul, integral_Ioo_sin_sq_zero_pi]
  simp_rw [hphi]
  have htheta (ρ : ℝ) :
      (∫ θ in Ioo (-π) π, δ * ρ ^ 3 * sin θ * (π / 2)) = 0 := by
    have heq : (∫ θ in Ioo (-π) π, δ * ρ ^ 3 * sin θ * (π / 2)) =
        ∫ θ in Ioo (-π) π, (δ * ρ ^ 3 * (π / 2)) * sin θ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      ring
    rw [heq]
    rw [integral_const_mul, integral_Ioo_sin_neg_pi_pi, mul_zero]
  simp_rw [htheta]
  simp

/-- 均匀球体的 `z` 方向一阶矩为零。-/
theorem uniform_ball_first_moment_z (δ : ℝ) {R : ℝ} :
    (∫ ρ in Ioo (0 : ℝ) R, ∫ _θ in Ioo (-π) π,
      ∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * cos φ) * (ρ ^ 2 * sin φ))) = 0 := by
  have hphi (ρ : ℝ) :
      (∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * cos φ) * (ρ ^ 2 * sin φ))) = 0 := by
    have heq : (∫ φ in Ioo (0 : ℝ) π,
        δ * ((ρ * cos φ) * (ρ ^ 2 * sin φ))) =
        ∫ φ in Ioo (0 : ℝ) π, (δ * ρ ^ 3) * (sin φ * cos φ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro φ _
      ring
    rw [heq]
    rw [integral_const_mul, integral_Ioo_sin_mul_cos_zero_pi, mul_zero]
  simp_rw [hphi]
  simp

/-- 均匀球体绕 `z` 轴的转动惯量为 `8πδR⁵/15`。-/
theorem uniform_ball_moment_of_inertia_z (δ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ ρ in Ioo (0 : ℝ) R, ∫ _θ in Ioo (-π) π,
      ∫ φ in Ioo (0 : ℝ) π, δ * (ρ ^ 4 * sin φ ^ 3)) =
        8 * π * δ * R ^ 5 / 15 := by
  have hphi (ρ : ℝ) :
      (∫ φ in Ioo (0 : ℝ) π, δ * (ρ ^ 4 * sin φ ^ 3)) =
        δ * ρ ^ 4 * (4 / 3) := by
    have heq : (∫ φ in Ioo (0 : ℝ) π, δ * (ρ ^ 4 * sin φ ^ 3)) =
        ∫ φ in Ioo (0 : ℝ) π, (δ * ρ ^ 4) * sin φ ^ 3 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro φ _
      ring
    rw [heq]
    rw [integral_const_mul, integral_Ioo_sin_cube_zero_pi]
  simp_rw [hphi]
  have htheta (ρ : ℝ) :
      (∫ _θ in Ioo (-π) π, δ * ρ ^ 4 * (4 / 3)) =
        8 * π * δ * ρ ^ 4 / 3 := by
    rw [setIntegral_const]
    simp [pi_pos.le]
    ring
  simp_rw [htheta]
  have heq : (∫ ρ in Ioo (0 : ℝ) R, 8 * π * δ * ρ ^ 4 / 3) =
      ∫ ρ in Ioo (0 : ℝ) R, (8 * π * δ / 3) * ρ ^ 4 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro ρ _
    ring
  rw [heq, integral_const_mul, integral_Ioo_pow_four_zero_radius hR]
  ring

/-- 把转动惯量改写为教材常见的 `I = (2/5)MR²`，其中
`M = 4πδR³/3`。-/
theorem uniform_ball_inertia_eq_two_fifths_mass (δ R : ℝ) :
    8 * π * δ * R ^ 5 / 15 =
      (2 / 5 : ℝ) * (4 * π * δ * R ^ 3 / 3) * R ^ 2 := by
  ring

end SandronesLibrary.Examples.SphericalMoments
