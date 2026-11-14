/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.ParametrizedGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 第一型曲线积分与曲面积分

第一型积分对标量场按几何长度或面积加权。沿曲线时权重是速率 `‖γ'‖`；沿三维
参数曲面时权重是面积元 `‖σᵤ×σᵥ‖`。因此它们不依赖参数方向：保向曲线换参数和
一般单射曲面换参数都保持积分值。

> **Entry**: analysis.multivariable.first-kind-integrals
-/

noncomputable section

namespace SandronesLibrary.Analysis.Multivariable

open Set MeasureTheory
open scoped Interval

/-- 标量场 `f` 沿参数曲线 `γ` 的第一型曲线积分 `∫ f(γ(t))‖γ'(t)‖dt`。-/
def curveIntegralFirstKind {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (γ : ParametrizedCurve n) (a b : ℝ) : ℝ :=
  ∫ t in a..b, f (γ t) * curveSpeed γ t

/-- 标量场 `f` 沿三维参数曲面的第一型曲面积分
`∫∫ f(σ(u,v))‖σᵤ×σᵥ‖du dv`。-/
def surfaceIntegralFirstKind3 (f : (Fin 3 → ℝ) → ℝ)
    (σ : ParametrizedSurface 3) (s : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in s, f (σ p) * surfaceAreaElement3 σ p ∂(volume.prod volume)

/-- 常密度的第一型曲线积分等于常数乘弧长。-/
theorem curveIntegralFirstKind_const {n : ℕ} (c : ℝ)
    (γ : ParametrizedCurve n) (a b : ℝ) :
    curveIntegralFirstKind (fun _ ↦ c) γ a b = c * curveArcLength γ a b := by
  rw [curveIntegralFirstKind, curveArcLength,
    intervalIntegral.integral_const_mul]

/-- 第一型曲线积分在导数非负的保向可微换参数下不变。-/
theorem curveIntegralFirstKind_comp_of_deriv_nonneg {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (γ : ParametrizedCurve n) (φ : ℝ → ℝ) (c d : ℝ)
    (hγ : Differentiable ℝ γ) (hφ : Differentiable ℝ φ)
    (hφnonneg : ∀ t, 0 ≤ deriv φ t) :
    curveIntegralFirstKind f (γ ∘ φ) c d =
      curveIntegralFirstKind f γ (φ c) (φ d) := by
  rw [curveIntegralFirstKind, curveIntegralFirstKind]
  simp_rw [curveSpeed_comp_of_deriv_nonneg γ φ _ (hγ _) (hφ _) (hφnonneg _)]
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := c) (b := d) (f := φ) (f' := deriv φ)
    (g := fun x ↦ f (γ x) * curveSpeed γ x)
    hφ.continuous.continuousOn
    (fun t _ ↦ (hφ t).hasDerivAt)
    (fun t _ ↦ hφnonneg t)
  simpa only [Function.comp_apply, mul_assoc] using hsub

/-- 常密度的第一型曲面积分等于常数乘曲面面积。-/
theorem surfaceIntegralFirstKind3_const (c : ℝ)
    (σ : ParametrizedSurface 3) (s : Set (ℝ × ℝ)) :
    surfaceIntegralFirstKind3 (fun _ ↦ c) σ s = c * surfaceAreaOn3 σ s := by
  rw [surfaceIntegralFirstKind3, surfaceAreaOn3]
  rw [MeasureTheory.integral_const_mul]

/-- **第一型曲面积分的一般换参数不变性**。

若 `s` 可测、`φ` 全局可微且在 `s` 上单射，则复合参数化在 `s` 上的第一型积分，
等于原参数化在像域 `φ '' s` 上的第一型积分。Jacobian 因子由面积元变换公式给出，
再由二维积分换元公式吸收。-/
theorem surfaceIntegralFirstKind3_comp_reparam
    (f : (Fin 3 → ℝ) → ℝ)
    (σ : ParametrizedSurface 3) (φ : ℝ × ℝ → ℝ × ℝ)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s)
    (hφ : Differentiable ℝ φ) (hinj : InjOn φ s)
    (hσ : Differentiable ℝ σ) :
    surfaceIntegralFirstKind3 f (σ ∘ φ) s =
      surfaceIntegralFirstKind3 f σ (φ '' s) := by
  rw [surfaceIntegralFirstKind3, surfaceIntegralFirstKind3]
  have hchange := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) (f' := fun x ↦ fderiv ℝ φ x) hs
    (fun x _ ↦ (hφ x).hasFDerivAt.hasFDerivWithinAt) hinj
    (fun y ↦ f (σ y) * surfaceAreaElement3 σ y)
  rw [← Measure.volume_eq_prod]
  rw [hchange]
  apply setIntegral_congr_fun hs
  intro x hx
  change f (σ (φ x)) * surfaceAreaElement3 (σ ∘ φ) x =
    |(fderiv ℝ φ x).det| *
      (f (σ (φ x)) * surfaceAreaElement3 σ (φ x))
  rw [surfaceAreaElement3_comp_reparam σ φ x (hσ (φ x)) (hφ x)]
  rw [det_eq_jacobianDet2]
  ring

end SandronesLibrary.Analysis.Multivariable
