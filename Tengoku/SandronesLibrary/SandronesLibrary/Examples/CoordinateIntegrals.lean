/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.CoordinateIntegrals
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 坐标积分：球体体积与质量的球坐标计算

本 Entry 服务理论条目 `analysis.multivariable.coordinate-integrals`（极坐标与柱坐标的
坐标变换公式）。本文件把球坐标参数盒 `(ρ,θ,φ) ∈ (0,R)×(-π,π)×(0,π)` 上的 Jacobian
积分逐步算成教材数值：极角积分 `∫₀^π sin φ dφ = 2`、径向积分 `∫₀^R ρ² dρ = R³/3`，
合起来给出半径 `R` 的球体体积 `4πR³/3` 与常密度 `δ` 下的质量 `4πδR³/3`。

本文件不重建换元理论：所有结果都调用理论层的坐标公式与一维特殊函数积分接口，
给出可直接在教材中引用的数值。转动惯量与重心见 `SphericalMoments.lean`。

> **Entry**: examples.analysis.coordinate-integrals
-/

noncomputable section

namespace SandronesLibrary.Examples.CoordinateIntegrals

open Set MeasureTheory Real
open scoped Interval

/-- 极角积分 `∫₀^π sin φ dφ = 2`。开区间与有向区间的端点只差零测集。-/
theorem integral_Ioo_sin_zero_pi :
    (∫ φ in Ioo (0 : ℝ) π, sin φ) = 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le]
  rw [integral_sin]
  norm_num

/-- 径向积分 `∫₀ʳ ρ² dρ = R³/3`。-/
theorem integral_Ioo_sq_zero_radius {R : ℝ} (hR : 0 ≤ R) :
    (∫ ρ in Ioo (0 : ℝ) R, ρ ^ 2) = R ^ 3 / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR]
  rw [integral_pow]
  norm_num

/-- **球体体积的球坐标计算**：半径 `R` 的球体在标准球坐标参数盒中的 Jacobian
积分为 `4πR³/3`。这就是教材中球体体积计算的数值步骤。-/
theorem spherical_ball_jacobian_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ ρ in Ioo (0 : ℝ) R, ∫ _θ in Ioo (-π) π,
      ∫ φ in Ioo (0 : ℝ) π, ρ ^ 2 * sin φ) =
        4 * π * R ^ 3 / 3 := by
  have hphi (ρ : ℝ) :
      (∫ φ in Ioo (0 : ℝ) π, ρ ^ 2 * sin φ) = ρ ^ 2 * 2 := by
    rw [integral_const_mul, integral_Ioo_sin_zero_pi]
  simp_rw [hphi]
  have htheta (ρ : ℝ) :
      (∫ _θ in Ioo (-π) π, ρ ^ 2 * 2) = 4 * π * ρ ^ 2 := by
    rw [setIntegral_const]
    simp [pi_pos.le]
    ring
  simp_rw [htheta]
  rw [integral_const_mul, integral_Ioo_sq_zero_radius hR]
  ring

/-- **均匀球体的质量**：若密度为常数 `δ`，则半径 `R` 的球体质量积分为
`4πδR³/3`。-/
theorem uniform_ball_mass_jacobian_integral (δ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ ρ in Ioo (0 : ℝ) R, ∫ _θ in Ioo (-π) π,
      ∫ φ in Ioo (0 : ℝ) π, δ * (ρ ^ 2 * sin φ)) =
        4 * π * δ * R ^ 3 / 3 := by
  have hphi (ρ : ℝ) :
      (∫ φ in Ioo (0 : ℝ) π, δ * (ρ ^ 2 * sin φ)) =
        δ * (ρ ^ 2 * 2) := by
    rw [← mul_assoc, integral_const_mul, integral_const_mul,
      integral_Ioo_sin_zero_pi]
    ring
  simp_rw [hphi]
  have htheta (ρ : ℝ) :
      (∫ _θ in Ioo (-π) π, δ * (ρ ^ 2 * 2)) =
        4 * π * δ * ρ ^ 2 := by
    rw [setIntegral_const]
    simp [pi_pos.le]
    ring
  simp_rw [htheta]
  rw [integral_const_mul, integral_Ioo_sq_zero_radius hR]
  ring

end SandronesLibrary.Examples.CoordinateIntegrals
