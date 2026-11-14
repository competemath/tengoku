/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.GreenGaussStokes
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / Green 公式：直角三角形与单位圆盘

本 Entry 服务理论条目 `analysis.multivariable.green-gauss-stokes`（Green、Gauss 与 Stokes
公式）与 `analysis.multivariable.jordan-region`（Jordan 可测区域）。本文件给出两个标准
平面区域上的 Green 公式实例：第一象限的标准直角三角形与闭单位圆盘。两者都先写成理论层
的「双正常域」表示（竖直正常域 = 水平正常域），再调用 `green_binormal_domain`。

本文件还给出**定向反例**：把边界遍历方向反过来，边界积分整体变号，而右端的区域内积分
与定向无关，于是同一个右端不可能同时匹配两种定向——Green 公式的逆时针约定不是可以省略
的装饰（`standardRightTriangle_rev_ne_ccw`、`unitDisk_rev_ne_ccw_of_ne_zero`）。

> **Entry**: examples.analysis.green-regions
-/

noncomputable section

namespace SandronesLibrary.Examples.GreenRegions

open Set MeasureTheory
open SandronesLibrary.Analysis.Multivariable
open SandronesLibrary.Analysis.GreenGaussStokes

/-! ## 标准直角三角形 -/

/-- 第一象限中的标准直角三角形 `x ≥ 0`、`y ≥ 0`、`x+y ≤ 1`。-/
def standardRightTriangle : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}

lemma standardRightTriangle_eq_xNormal :
    standardRightTriangle = xNormalDomain 0 1 (fun _ ↦ 0) (fun x ↦ 1 - x) := by
  ext z
  simp only [standardRightTriangle, xNormalDomain, mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨⟨hx, by linarith⟩, hy, by linarith⟩
  · rintro ⟨⟨hx, _⟩, hy, hyu⟩
    exact ⟨hx, hy, by linarith⟩

lemma standardRightTriangle_eq_yNormal :
    standardRightTriangle = yNormalDomain 0 1 (fun _ ↦ 0) (fun y ↦ 1 - y) := by
  ext z
  simp only [standardRightTriangle, yNormalDomain, mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨⟨hy, by linarith⟩, hx, by linarith⟩
  · rintro ⟨⟨hy, _⟩, hx, hxu⟩
    exact ⟨hx, hy, by linarith⟩

/-- 标准直角三角形的逆时针边界积分。-/
def standardRightTriangleBoundaryIntegral (P Q : ℝ × ℝ → ℝ) : ℝ :=
  (∫ x in Icc (0 : ℝ) 1, P (x, 0) - P (x, 1 - x)) +
    ∫ y in Icc (0 : ℝ) 1, Q (1 - y, y) - Q (0, y)

/-- **标准直角三角形上的 Green 公式**。-/
theorem green_standardRightTriangle
    (P Q : ℝ × ℝ → ℝ)
    (hPy : IntegrableOn (fun z ↦ deriv (fun y ↦ P (z.1, y)) z.2)
      standardRightTriangle (volume.prod volume))
    (hQx : IntegrableOn (fun z ↦ deriv (fun x ↦ Q (x, z.2)) z.1)
      standardRightTriangle (volume.prod volume))
    (hPdiff : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc 0 (1 - x),
      DifferentiableAt ℝ (fun t ↦ P (x, t)) y)
    (hQdiff : ∀ y ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc 0 (1 - y),
      DifferentiableAt ℝ (fun t ↦ Q (t, y)) x)
    (hPint : ∀ x ∈ Icc (0 : ℝ) 1,
      IntervalIntegrable (deriv (fun y ↦ P (x, y))) volume 0 (1 - x))
    (hQint : ∀ y ∈ Icc (0 : ℝ) 1,
      IntervalIntegrable (deriv (fun x ↦ Q (x, y))) volume 0 (1 - y)) :
    standardRightTriangleBoundaryIntegral P Q =
      ∫ z in standardRightTriangle,
        (deriv (fun x ↦ Q (x, z.2)) z.1 -
          deriv (fun y ↦ P (z.1, y)) z.2) ∂(volume.prod volume) := by
  have hdomains : xNormalDomain 0 1 (fun _ ↦ 0) (fun x ↦ 1 - x) =
      yNormalDomain 0 1 (fun _ ↦ 0) (fun y ↦ 1 - y) :=
    standardRightTriangle_eq_xNormal.symm.trans standardRightTriangle_eq_yNormal
  have hPy' : IntegrableOn (fun z ↦ deriv (fun y ↦ P (z.1, y)) z.2)
      (xNormalDomain 0 1 (fun _ ↦ 0) (fun x ↦ 1 - x))
      (volume.prod volume) := by
    simpa [← standardRightTriangle_eq_xNormal] using hPy
  have hQx' : IntegrableOn (fun z ↦ deriv (fun x ↦ Q (x, z.2)) z.1)
      (yNormalDomain 0 1 (fun _ ↦ 0) (fun y ↦ 1 - y))
      (volume.prod volume) := by
    simpa [← standardRightTriangle_eq_yNormal] using hQx
  have h := green_binormal_domain P Q 0 1 0 1
    (fun _ ↦ 0) (fun x ↦ 1 - x) (fun _ ↦ 0) (fun y ↦ 1 - y)
    continuous_const (continuous_const.sub continuous_id)
    continuous_const (continuous_const.sub continuous_id)
    (fun x hx ↦ by linarith [hx.2]) (fun y hy ↦ by linarith [hy.2])
    hdomains hPy' hQx' hPdiff hQdiff hPint hQint
  simpa [standardRightTriangleBoundaryIntegral, normalDomainBoundaryIntegral,
    ← standardRightTriangle_eq_xNormal] using h

/-- 用 `(P,Q)=(0,x)` 得到三角形面积型边界积分 `1/2`。-/
theorem standardRightTriangleBoundaryIntegral_zero_fst :
    standardRightTriangleBoundaryIntegral (fun _ ↦ 0) (fun z ↦ z.1) = 1 / 2 := by
  have honeSub : (∫ y in Icc (0 : ℝ) 1, 1 - y) = 1 / 2 := by
    calc
      _ = ∫ y in (0 : ℝ)..1, 1 - y := by
        rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
      _ = _ := by
        rw [intervalIntegral.integral_sub]
        · norm_num [integral_id]
        · exact continuous_const.intervalIntegrable 0 1
        · exact continuous_id.intervalIntegrable 0 1
  rw [standardRightTriangleBoundaryIntegral]
  simp only [sub_self, MeasureTheory.integral_zero, zero_add, sub_zero]
  rw [honeSub]

/-! ## 闭单位圆盘 -/

/-- 闭单位圆盘 `x²+y²≤1`。-/
def unitDisk : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

/-- 单位圆盘的竖直正常域表示。-/
lemma unitDisk_eq_xNormal : unitDisk =
    xNormalDomain (-1) 1 (fun x ↦ -√(1 - x ^ 2)) (fun x ↦ √(1 - x ^ 2)) := by
  ext z
  simp only [unitDisk, xNormalDomain, mem_ofPred_eq, Set.mem_Icc]
  constructor
  · intro h
    have hxSq : z.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.2]
    have hxabs : |z.1| ≤ 1 := by simpa using Real.abs_le_sqrt hxSq
    have hyabs : |z.2| ≤ √(1 - z.1 ^ 2) := Real.abs_le_sqrt (by nlinarith)
    exact ⟨abs_le.mp hxabs, abs_le.mp hyabs⟩
  · rintro ⟨hx, hyl, hyu⟩
    have hxabs : |z.1| ≤ 1 := abs_le.mpr hx
    have hxSq : z.1 ^ 2 ≤ 1 := by
      simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg z.1) (by norm_num)).2 hxabs
    have hA : 0 ≤ 1 - z.1 ^ 2 := by linarith
    have hyabs : |z.2| ≤ √(1 - z.1 ^ 2) := abs_le.mpr ⟨hyl, hyu⟩
    have hySq : z.2 ^ 2 ≤ (√(1 - z.1 ^ 2)) ^ 2 := by
      simpa using (sq_le_sq₀ (abs_nonneg z.2) (Real.sqrt_nonneg _)).2 hyabs
    rw [Real.sq_sqrt hA] at hySq
    nlinarith

/-- 单位圆盘的水平正常域表示。-/
lemma unitDisk_eq_yNormal : unitDisk =
    yNormalDomain (-1) 1 (fun y ↦ -√(1 - y ^ 2)) (fun y ↦ √(1 - y ^ 2)) := by
  ext z
  simp only [unitDisk, yNormalDomain, mem_ofPred_eq, Set.mem_Icc]
  constructor
  · intro h
    have hySq : z.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.1]
    have hyabs : |z.2| ≤ 1 := by simpa using Real.abs_le_sqrt hySq
    have hxabs : |z.1| ≤ √(1 - z.2 ^ 2) := Real.abs_le_sqrt (by nlinarith)
    exact ⟨abs_le.mp hyabs, abs_le.mp hxabs⟩
  · rintro ⟨hy, hxl, hxu⟩
    have hyabs : |z.2| ≤ 1 := abs_le.mpr hy
    have hySq : z.2 ^ 2 ≤ 1 := by
      simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg z.2) (by norm_num)).2 hyabs
    have hB : 0 ≤ 1 - z.2 ^ 2 := by linarith
    have hxabs : |z.1| ≤ √(1 - z.2 ^ 2) := abs_le.mpr ⟨hxl, hxu⟩
    have hxSq : z.1 ^ 2 ≤ (√(1 - z.2 ^ 2)) ^ 2 := by
      simpa using (sq_le_sq₀ (abs_nonneg z.1) (Real.sqrt_nonneg _)).2 hxabs
    rw [Real.sq_sqrt hB] at hxSq
    nlinarith

/-- 单位圆盘的逆时针边界积分，以上下、左右半圆图像表示。-/
def unitDiskBoundaryIntegral (P Q : ℝ × ℝ → ℝ) : ℝ :=
  (∫ x in Icc (-1 : ℝ) 1,
      P (x, -√(1 - x ^ 2)) - P (x, √(1 - x ^ 2))) +
    ∫ y in Icc (-1 : ℝ) 1,
      Q (√(1 - y ^ 2), y) - Q (-√(1 - y ^ 2), y)

/-- **闭单位圆盘上的 Green 公式**。-/
theorem green_unitDisk
    (P Q : ℝ × ℝ → ℝ)
    (hPy : IntegrableOn (fun z ↦ deriv (fun y ↦ P (z.1, y)) z.2)
      unitDisk (volume.prod volume))
    (hQx : IntegrableOn (fun z ↦ deriv (fun x ↦ Q (x, z.2)) z.1)
      unitDisk (volume.prod volume))
    (hPdiff : ∀ x ∈ Icc (-1 : ℝ) 1,
      ∀ y ∈ Icc (-√(1 - x ^ 2)) (√(1 - x ^ 2)),
        DifferentiableAt ℝ (fun t ↦ P (x, t)) y)
    (hQdiff : ∀ y ∈ Icc (-1 : ℝ) 1,
      ∀ x ∈ Icc (-√(1 - y ^ 2)) (√(1 - y ^ 2)),
        DifferentiableAt ℝ (fun t ↦ Q (t, y)) x)
    (hPint : ∀ x ∈ Icc (-1 : ℝ) 1,
      IntervalIntegrable (deriv (fun y ↦ P (x, y))) volume
        (-√(1 - x ^ 2)) (√(1 - x ^ 2)))
    (hQint : ∀ y ∈ Icc (-1 : ℝ) 1,
      IntervalIntegrable (deriv (fun x ↦ Q (x, y))) volume
        (-√(1 - y ^ 2)) (√(1 - y ^ 2))) :
    unitDiskBoundaryIntegral P Q =
      ∫ z in unitDisk,
        (deriv (fun x ↦ Q (x, z.2)) z.1 -
          deriv (fun y ↦ P (z.1, y)) z.2) ∂(volume.prod volume) := by
  have hsqrt : Continuous (fun x : ℝ ↦ √(1 - x ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
  have hdomains :
      xNormalDomain (-1) 1 (fun x ↦ -√(1 - x ^ 2)) (fun x ↦ √(1 - x ^ 2)) =
        yNormalDomain (-1) 1 (fun y ↦ -√(1 - y ^ 2)) (fun y ↦ √(1 - y ^ 2)) :=
    unitDisk_eq_xNormal.symm.trans unitDisk_eq_yNormal
  have hPy' : IntegrableOn (fun z ↦ deriv (fun y ↦ P (z.1, y)) z.2)
      (xNormalDomain (-1) 1 (fun x ↦ -√(1 - x ^ 2)) (fun x ↦ √(1 - x ^ 2)))
      (volume.prod volume) := by
    simpa [← unitDisk_eq_xNormal] using hPy
  have hQx' : IntegrableOn (fun z ↦ deriv (fun x ↦ Q (x, z.2)) z.1)
      (yNormalDomain (-1) 1 (fun y ↦ -√(1 - y ^ 2)) (fun y ↦ √(1 - y ^ 2)))
      (volume.prod volume) := by
    simpa [← unitDisk_eq_yNormal] using hQx
  have h := green_binormal_domain P Q (-1) 1 (-1) 1
    (fun x ↦ -√(1 - x ^ 2)) (fun x ↦ √(1 - x ^ 2))
    (fun y ↦ -√(1 - y ^ 2)) (fun y ↦ √(1 - y ^ 2))
    hsqrt.neg hsqrt hsqrt.neg hsqrt
    (fun x _ ↦ by linarith [Real.sqrt_nonneg (1 - x ^ 2)])
    (fun y _ ↦ by linarith [Real.sqrt_nonneg (1 - y ^ 2)])
    hdomains hPy' hQx' hPdiff hQdiff hPint hQint
  simpa [unitDiskBoundaryIntegral, normalDomainBoundaryIntegral,
    ← unitDisk_eq_xNormal] using h

/-! ## 定向：反向遍历的反例

Green 公式的左端是**有向**边界积分。下面把两个区域的边界按相反方向再遍历一次，
证明所得积分恰好是原积分的相反数；于是只要原积分非零，两种定向给出不同的值，
而右端的区域内积分并不随定向改变——公式只能对其中一种定向成立。
-/

/-- 标准直角三角形的顺时针（反向）边界积分：三条边的参数化方向全部反过来。-/
def standardRightTriangleBoundaryIntegralRev (P Q : ℝ × ℝ → ℝ) : ℝ :=
  (∫ x in Icc (0 : ℝ) 1, P (x, 1 - x) - P (x, 0)) +
    ∫ y in Icc (0 : ℝ) 1, Q (0, y) - Q (1 - y, y)

/-- **反向遍历只改符号**：直角三角形的顺时针边界积分等于逆时针边界积分的相反数。-/
theorem standardRightTriangleBoundaryIntegralRev_eq_neg (P Q : ℝ × ℝ → ℝ) :
    standardRightTriangleBoundaryIntegralRev P Q =
      -standardRightTriangleBoundaryIntegral P Q := by
  have h1 : (∫ x in Icc (0 : ℝ) 1, P (x, 1 - x) - P (x, 0)) =
      -(∫ x in Icc (0 : ℝ) 1, P (x, 0) - P (x, 1 - x)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    ring
  have h2 : (∫ y in Icc (0 : ℝ) 1, Q (0, y) - Q (1 - y, y)) =
      -(∫ y in Icc (0 : ℝ) 1, Q (1 - y, y) - Q (0, y)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y _
    ring
  rw [standardRightTriangleBoundaryIntegralRev, standardRightTriangleBoundaryIntegral,
    h1, h2]
  ring

/-- **定向反例（直角三角形）**：取 `(P,Q)=(0,x)` 时逆时针边界积分为 `1/2`（三角形面积），
顺时针为 `-1/2`，两者不等。这反驳「边界积分与遍历方向无关」这一误认：Green 公式
`standardRightTriangleBoundaryIntegral P Q = ∬(∂Q/∂x-∂P/∂y)` 的右端不随定向改变，
因此反向定向后公式必然失败。-/
theorem standardRightTriangle_rev_ne_ccw :
    standardRightTriangleBoundaryIntegralRev (fun _ ↦ 0) (fun z ↦ z.1) ≠
      standardRightTriangleBoundaryIntegral (fun _ ↦ 0) (fun z ↦ z.1) := by
  rw [standardRightTriangleBoundaryIntegralRev_eq_neg,
    standardRightTriangleBoundaryIntegral_zero_fst]
  norm_num

/-- 闭单位圆盘的顺时针（反向）边界积分：上下两个半圆图像的参数化方向都反过来。-/
def unitDiskBoundaryIntegralRev (P Q : ℝ × ℝ → ℝ) : ℝ :=
  (∫ x in Icc (-1 : ℝ) 1, P (x, √(1 - x ^ 2)) - P (x, -√(1 - x ^ 2))) +
    ∫ y in Icc (-1 : ℝ) 1, Q (-√(1 - y ^ 2), y) - Q (√(1 - y ^ 2), y)

/-- **反向遍历只改符号**：单位圆盘的顺时针边界积分等于逆时针边界积分的相反数。-/
theorem unitDiskBoundaryIntegralRev_eq_neg (P Q : ℝ × ℝ → ℝ) :
    unitDiskBoundaryIntegralRev P Q = -unitDiskBoundaryIntegral P Q := by
  have h1 : (∫ x in Icc (-1 : ℝ) 1, P (x, √(1 - x ^ 2)) - P (x, -√(1 - x ^ 2))) =
      -(∫ x in Icc (-1 : ℝ) 1, P (x, -√(1 - x ^ 2)) - P (x, √(1 - x ^ 2))) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    ring
  have h2 : (∫ y in Icc (-1 : ℝ) 1, Q (-√(1 - y ^ 2), y) - Q (√(1 - y ^ 2), y)) =
      -(∫ y in Icc (-1 : ℝ) 1, Q (√(1 - y ^ 2), y) - Q (-√(1 - y ^ 2), y)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y _
    ring
  rw [unitDiskBoundaryIntegralRev, unitDiskBoundaryIntegral, h1, h2]
  ring

/-- **定向反例（单位圆盘）**：只要逆时针边界积分非零，顺时针值就与它不同。
取 `(P,Q)=(0,x)` 时逆时针值是圆盘面积 `π`（由 `green_unitDisk` 化为 `∬1`），
顺时针值是 `-π`——定向同样不可省略。-/
theorem unitDisk_rev_ne_ccw_of_ne_zero {P Q : ℝ × ℝ → ℝ}
    (h : unitDiskBoundaryIntegral P Q ≠ 0) :
    unitDiskBoundaryIntegralRev P Q ≠ unitDiskBoundaryIntegral P Q := by
  rw [unitDiskBoundaryIntegralRev_eq_neg]
  intro hc
  exact h (by linarith [hc])

end SandronesLibrary.Examples.GreenRegions
