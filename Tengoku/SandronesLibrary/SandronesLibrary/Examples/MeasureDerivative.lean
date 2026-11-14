/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.MeasureDerivativeRadonNikodym
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.MeasureDerivativeLebesgueDecomposition
import Tengoku.Seed.Probability.Distributions.Gaussian.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 测度导数（RA-F2）具体计算例

本文件为实分析 RA-F2（`real-analysis.measure-derivative.*`）补齐可计算的具体例子：常密度测度、
Gaussian 测度与标准 Lebesgue 测度的关系，以及 Dirac 测度相对 Lebesgue 测度的互奇异与
Lebesgue 分解。

> **Entry**: examples.real-analysis.measure-derivative
-/

noncomputable section

namespace SandronesLibrary.Examples.MeasureDerivative

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## 1. 常密度测度 `2 · volume` -/

/-- **常密度 `2` 的测度**：`twoVolume = volume.withDensity (fun _ ↦ 2)`。这是勒贝格测度的
最简非平凡密度扰动，用于把 RA-F2 的抽象分解落到可直接计算的数值结果上。-/
def twoVolume : Measure ℝ := volume.withDensity fun _ ↦ (2 : ℝ≥0∞)

/-- 常密度测度关于勒贝格测度绝对连续（RA-F2 `absolute-continuity` 的正例）。
@isnad1 id=absolute.0h0v.s2.b767add8ee95 from=translated src=- shape=fa180b53 vocab=237d25d1
-/
theorem twoVolume_absolutelyContinuous : twoVolume ≪ volume :=
  withDensity_absolutelyContinuous volume (fun _ ↦ (2 : ℝ≥0∞))

/-- **Radon–Nikodym 导数计算**：`d(twoVolume)/d(volume) = 2`（几乎处处）。
@isnad1 id=eventual.0h0v.s5.707f63ef7706 from=translated src=- shape=4119c1db vocab=56903742
-/
theorem twoVolume_rnDeriv :
    twoVolume.rnDeriv volume =ᵐ[volume] fun _ ↦ (2 : ℝ≥0∞) :=
  Measure.rnDeriv_withDensity volume measurable_const

/-- **可计算结论**：`twoVolume` 在单位区间 `[0,1]` 上的质量问题为 `2`。
这是教材“密度为 `2` 的测度在区间上的质量等于 `2 × 长度`”的显式计算。
@isnad1 id=eq.0h0v.s5.429b6c695373 from=translated src=- shape=f2f5b78d vocab=a26d2874
-/
theorem twoVolume_Icc_zero_one : twoVolume (Set.Icc (0 : ℝ) 1) = 2 := by
  rw [twoVolume, withDensity_apply _ measurableSet_Icc]
  rw [setLIntegral_const, Real.volume_Icc]
  norm_num

/-! ## 2. 标准正态测度与勒贝格测度 -/

/-- 标准正态测度关于勒贝格测度绝对连续（`variance = 1 ≠ 0` 时的 RA-F2 正例）。
@isnad1 id=absolute.0h0v.s4.c72666bac248 from=translated src=- shape=32ebfc65 vocab=062ae612
-/
theorem standardGaussian_absolutelyContinuous :
    gaussianReal 0 1 ≪ (volume : Measure ℝ) :=
  gaussianReal_absolutelyContinuous 0 (by norm_num)

/-- **Radon–Nikodym 导数计算**：`d(gaussianReal 0 1)/d(volume) = gaussianPDF 0 1`
（几乎处处）。这把“正态密度的积分是正态测度”写成测度导数语言。
@isnad1 id=eventual.0h0v.s5.67991ad3d97c from=translated src=- shape=ed45cfec vocab=06b261ec
-/
theorem gaussianReal_rnDeriv :
    (gaussianReal 0 1).rnDeriv volume =ᵐ[volume] gaussianPDF 0 1 :=
  rnDeriv_gaussianReal 0 1

/-! ## 3. Dirac 测度与 Lebesgue 测度互奇异、不绝对连续 -/

/-- `δ₀` 与勒贝格测度互奇异（RA-F2 `mutually-singular` 的正例）。
@isnad1 id=mutually.0h0v.s3.711f27ab4206 from=translated src=- shape=cd0f3c6e vocab=2f5c662e
-/
theorem dirac_zero_mutuallySingular_volume :
    (Measure.dirac (0 : ℝ)) ⟂ₘ (volume : Measure ℝ) :=
  mutuallySingular_dirac 0 volume

/-- **反例（不可省略的条件）**：`δ₀` 关于勒贝格测度**不**绝对连续。零测集 `{0}` 的
`volume` 测度为零，但 `δ₀` 测度为 `1`，正是否定 `absolute-continuity` 定义中
“`ν s = 0 → μ s = 0`”的具体见证。
@isnad1 id=not.0h0v.s4.5f9a9fac3fe1 from=translated src=- shape=151049cc vocab=55542ace
-/
theorem dirac_zero_not_absolutelyContinuous :
    ¬ ((Measure.dirac (0 : ℝ)) ≪ (volume : Measure ℝ)) := by
  intro h
  have hzero : (Measure.dirac (0 : ℝ)) ({0} : Set ℝ) = 0 := h Real.volume_singleton
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton 0)] at hzero
  norm_num at hzero

/-! ## 4. `δ₀` 相对勒贝格测度的 Lebesgue 分解 -/

/-- **奇异部分就是全测度**：`(δ₀).singularPart volume = δ₀`，因为 `δ₀` 与 `volume` 互奇异。
@isnad1 id=eq.0h0v.s4.af5cf9174e7d from=translated src=- shape=adc56cf8 vocab=abf4f611
-/
theorem dirac_zero_singularPart_eq_self :
    (Measure.dirac (0 : ℝ)).singularPart volume = Measure.dirac 0 :=
  Measure.singularPart_eq_self.mpr dirac_zero_mutuallySingular_volume

/-- **密度部分为零**：`d(δ₀)/d(volume) = 0`（几乎处处），因为两者互奇异。
@isnad1 id=eventual.0h0v.s5.56468e510bcd from=translated src=- shape=9a19564d vocab=c8ff840d
-/
theorem dirac_zero_rnDeriv_eq_zero :
    (Measure.dirac (0 : ℝ)).rnDeriv volume =ᵐ[volume] 0 :=
  Measure.MutuallySingular.rnDeriv_ae_eq_zero dirac_zero_mutuallySingular_volume

/-- **Lebesgue 分解的显式重写**：`δ₀ = δ₀ + volume.withDensity 0`。这是 RA-F2 主等式
`μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)` 在 `μ = δ₀`、`ν = volume` 上的
具体形态：奇异部分取全部质量，密度部分恒为零。
@isnad1 id=eq.0h0v.s6.a7970e567baf from=translated src=- shape=f7f51f0d vocab=7d0ccc0d
-/
theorem dirac_zero_lebesgueDecomposition :
    (Measure.dirac (0 : ℝ)) =
      (Measure.dirac (0 : ℝ)).singularPart volume +
        volume.withDensity ((Measure.dirac (0 : ℝ)).rnDeriv volume) :=
  Measure.haveLebesgueDecomposition_add _ _

end SandronesLibrary.Examples.MeasureDerivative
