/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.NormalDomain
import Tengoku.Seed.MeasureTheory.Function.Jacobian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 多重积分换元公式

本模块把 Mathlib 的有限维 Jacobian 定理封装成数学分析教材常用的接口。给定可测区域
`s` 和区域上可微、单射的坐标变换 `φ`，像区域上的积分可以拉回到 `s`，并乘以
Jacobian 行列式的绝对值。

Mathlib 的底层定理允许一般有限维实向量空间和 Banach 空间值函数；这里固定为
`Fin n → ℝ` 上的实值积分，与本库的多元 Riemann、Jordan 区域和正常区域接口对齐。
-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set MeasureTheory
open scoped ENNReal

/-- 映射 `φ` 沿区域 `s` 的 Jacobian 绝对值，即
`|det (Dφ|s)(x)|`。边界点使用区域内 Fréchet 导数 `fderivWithin`。

> **Entry**: analysis.multivariable.change-variables-/
def absJacobianWithin {n : ℕ} (φ : JordanEuc n → JordanEuc n)
    (s : Set (JordanEuc n)) (x : JordanEuc n) : ℝ :=
  |(fderivWithin ℝ φ s x).det|

/-- **多重积分换元公式**：若 `φ` 在可测区域 `s` 上可微且单射，则像区域上的积分
等于原区域上复合函数乘以 Jacobian 绝对值后的积分：

`∫_{φ(s)} g(y) dy = ∫_s g(φ(x)) |det Dφ(x)| dx`。

该等式对不可积函数仍按 Bochner 积分的底层约定成立；需要传递可积性时使用下一条
等价定理。
@isnad1 id=eq.3h4v.s8.3d915204ab54 from=translated src=- shape=2d8ec0d5 vocab=0ce5b6aa
-/
theorem integral_image_eq_integral_absJacobian_mul {n : ℕ}
    {s : Set (JordanEuc n)} {φ : JordanEuc n → JordanEuc n}
    (hs : MeasurableSet s) (hφ : DifferentiableOn ℝ φ s) (hinj : InjOn φ s)
    (g : JordanEuc n → ℝ) :
    (∫ y in φ '' s, g y) =
      ∫ x in s, absJacobianWithin φ s x * g (φ x) := by
  simpa [absJacobianWithin, smul_eq_mul] using
    (MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) hs (fun x hx ↦ (hφ x hx).hasFDerivWithinAt) hinj g)

/-- **换元后的可积性判据**：`g` 在像区域 `φ(s)` 上可积，当且仅当拉回并乘以
Jacobian 绝对值后的函数在原区域 `s` 上可积。
@isnad1 id=iff.3h4v.s8.37313413023a from=translated src=- shape=417693cd vocab=10e28673
-/
theorem integrableOn_image_iff_integrableOn_absJacobian_mul {n : ℕ}
    {s : Set (JordanEuc n)} {φ : JordanEuc n → JordanEuc n}
    (hs : MeasurableSet s) (hφ : DifferentiableOn ℝ φ s) (hinj : InjOn φ s)
    (g : JordanEuc n → ℝ) :
    IntegrableOn g (φ '' s) ↔
      IntegrableOn (fun x ↦ absJacobianWithin φ s x * g (φ x)) s := by
  simpa [absJacobianWithin, smul_eq_mul] using
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := volume) hs (fun x hx ↦ (hφ x hx).hasFDerivWithinAt) hinj g)

/-- **像区域体积公式**：像的体积等于原区域上 Jacobian 绝对值的非负积分：

`vol(φ(s)) = ∫_s |det Dφ(x)| dx`。

使用 `lintegral` 是为了允许区域具有无限体积，而不引入额外有限性假设。
@isnad1 id=eq.3h3v.s8.9d56565c5025 from=translated src=- shape=a6f25a80 vocab=c6cbe7d8
-/
theorem volume_image_eq_lintegral_absJacobian {n : ℕ}
    {s : Set (JordanEuc n)} {φ : JordanEuc n → JordanEuc n}
    (hs : MeasurableSet s) (hφ : DifferentiableOn ℝ φ s) (hinj : InjOn φ s) :
    volume (φ '' s) = ∫⁻ x in s, ENNReal.ofReal (absJacobianWithin φ s x) := by
  simpa [absJacobianWithin] using
    (MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      (μ := volume) hs (fun x hx ↦ (hφ x hx).hasFDerivWithinAt) hinj
      (fun _ : JordanEuc n ↦ (1 : ℝ≥0∞)))

end SandronesLibrary.Analysis.Multivariable
