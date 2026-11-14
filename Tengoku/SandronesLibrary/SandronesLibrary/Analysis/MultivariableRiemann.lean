/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.JordanRegion
import Tengoku.Seed.Analysis.BoxIntegral.Integrability
import Tengoku.Seed.Analysis.BoxIntegral.Partition.Measure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 闭盒上的多元 Riemann 积分

本模块用带标签盒分割的 Riemann 和定义多元 Riemann 积分，并证明闭盒上连续函数
Riemann 可积，其积分值等于 Lebesgue 盒积分。常函数的积分给出盒体积校准。
-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set MeasureTheory
open BoxIntegral

/-- 轴平行闭盒的端点数据载体；可积性由后续本库谓词表达。

> **Entry**: analysis.multivariable.riemann-box-/
abbrev RiemannBox (n : ℕ) := BoxIntegral.Box (Fin n)

/-- 多元函数在闭盒上的 Riemann 和趋于 `y`。-/
def HasRiemannBoxIntegral {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (I : RiemannBox n) (y : ℝ) : Prop :=
  BoxIntegral.HasIntegral I IntegrationParams.Riemann f BoxAdditiveMap.volume y

/-- 多元函数在闭盒上 Riemann 可积。-/
def RiemannIntegrableOnBox {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (I : RiemannBox n) : Prop :=
  BoxIntegral.Integrable I IntegrationParams.Riemann f BoxAdditiveMap.volume

/-- 闭盒上的多元 Riemann 积分值；不可积时按底层约定取零。-/
def riemannBoxIntegral {n : ℕ} (f : (Fin n → ℝ) → ℝ) (I : RiemannBox n) : ℝ :=
  BoxIntegral.integral I IntegrationParams.Riemann f BoxAdditiveMap.volume

/-- Riemann 积分值满足 `HasRiemannBoxIntegral`。-/
theorem HasRiemannBoxIntegral.integral_eq {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {I : RiemannBox n} {y : ℝ} (h : HasRiemannBoxIntegral f I y) :
    riemannBoxIntegral f I = y := by
  exact BoxIntegral.HasIntegral.integral_eq h

/-- 连续函数在闭盒上 Riemann 可积。-/
theorem continuousOn_riemannIntegrableOnBox {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {I : RiemannBox n} (hf : ContinuousOn f (Box.Icc I)) :
    RiemannIntegrableOnBox f I := by
  have hbox := MeasureTheory.ContinuousOn.hasBoxIntegral volume hf IntegrationParams.Riemann
  exact BoxIntegral.HasIntegral.integrable hbox

/-- 连续函数的多元 Riemann 积分值等于闭盒上的 Lebesgue 积分。-/
theorem riemannBoxIntegral_eq_setIntegral {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {I : RiemannBox n} (hf : ContinuousOn f (Box.Icc I)) :
    riemannBoxIntegral f I = ∫ x in (I : Set (Fin n → ℝ)), f x := by
  have hbox := MeasureTheory.ContinuousOn.hasBoxIntegral volume hf IntegrationParams.Riemann
  exact BoxIntegral.HasIntegral.integral_eq hbox

/-- 常函数 `1` 的多元 Riemann 积分等于各边长之积。-/
theorem riemannBoxIntegral_one {n : ℕ} (I : RiemannBox n) :
    riemannBoxIntegral (fun _ ↦ 1) I = ∏ i, (I.upper i - I.lower i) := by
  simp [riemannBoxIntegral, BoxIntegral.integral_const, BoxAdditiveMap.volume_apply]

end SandronesLibrary.Analysis.Multivariable
