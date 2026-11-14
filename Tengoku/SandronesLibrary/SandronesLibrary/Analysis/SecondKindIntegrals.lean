/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.DifferentialForms
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.ParametrizedGeometry
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.MultivariableIntegration
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 第二型曲线积分与曲面积分

第二型积分积分的不是无向长度或面积，而是微分形式在**有序切向量**上的值。
对参数曲线 `γ` 和 1-形式 `ω`，定义

`∫ₐᵇ ω(γ(t))(γ'(t)) dt`；

对参数曲面 `σ` 和 2-形式 `ω`，定义

`∬ ω(σ(u,v))(∂ᵤσ, ∂ᵥσ) du dv`。

切向量的次序记录方向，所以第二型积分会在反向时改变符号。这与第一型积分中的
`‖γ'‖` 或面积 Jacobian 的绝对值形成根本区别。本模块先建立曲线与矩形参数曲面上
的定义、线性、保向换参数不变性，以及恰当 1-形式的积分基本定理。后续 Green、
Gauss 与 Stokes 公式将直接使用这些接口。

> **Entry**: analysis.multivariable.second-kind-integrals
-/

noncomputable section

namespace SandronesLibrary.Analysis.SecondKindIntegrals

open Set MeasureTheory
open scoped Interval
open SandronesLibrary.Analysis.DifferentialForms
open SandronesLibrary.Analysis.Multivariable

/-- 1-形式沿参数曲线的被积函数 `t ↦ ω(γ(t))(γ'(t))`。-/
def curveFormIntegrand {n : ℕ} (ω : DifferentialForm (Fin n → ℝ) 1)
    (γ : ParametrizedCurve n) (t : ℝ) : ℝ :=
  ω (γ t) (fun _ ↦ curveVelocity γ t)

/-- **第二型曲线积分**：1-形式沿有向参数曲线的积分。-/
def secondKindCurveIntegral {n : ℕ} (ω : DifferentialForm (Fin n → ℝ) 1)
    (γ : ParametrizedCurve n) (a b : ℝ) : ℝ :=
  ∫ t in a..b, curveFormIntegrand ω γ t

/-- 复合换参数后的 1-形式密度多出参数导数因子。

这里没有绝对值：若参数导数为负，密度随之变号，这正是有向积分的行为。-/
theorem curveFormIntegrand_comp {n : ℕ} (ω : DifferentialForm (Fin n → ℝ) 1)
    (γ : ParametrizedCurve n) (φ : ℝ → ℝ) (t : ℝ)
    (hγ : DifferentiableAt ℝ γ (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    curveFormIntegrand ω (γ ∘ φ) t =
      curveFormIntegrand ω γ (φ t) * deriv φ t := by
  rw [curveFormIntegrand, curveVelocity_comp γ φ t hγ hφ]
  have h := AlternatingMap.map_smul_univ
    (ω (γ (φ t))).toAlternatingMap (fun _ : Fin 1 ↦ deriv φ t)
      (fun _ : Fin 1 ↦ curveVelocity γ (φ t))
  simpa [curveFormIntegrand, Function.comp_apply, mul_comm] using h

/-- **保向换参数不变性**：若 `φ' ≥ 0`，则复合参数化不改变第二型曲线积分。

右侧端点自动变为 `φ(c)` 与 `φ(d)`。定理允许导数在个别点为零，因此也覆盖
不严格但从不反向的参数变化。-/
theorem secondKindCurveIntegral_comp_of_deriv_nonneg {n : ℕ}
    (ω : DifferentialForm (Fin n → ℝ) 1) (γ : ParametrizedCurve n)
    (φ : ℝ → ℝ) (c d : ℝ)
    (hγ : Differentiable ℝ γ) (hφ : Differentiable ℝ φ)
    (hφnonneg : ∀ t, 0 ≤ deriv φ t) :
    secondKindCurveIntegral ω (γ ∘ φ) c d =
      secondKindCurveIntegral ω γ (φ c) (φ d) := by
  rw [secondKindCurveIntegral, secondKindCurveIntegral]
  simp_rw [curveFormIntegrand_comp ω γ φ _ (hγ _) (hφ _)]
  exact intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := φ) (f' := deriv φ) (g := curveFormIntegrand ω γ) (a := c) (b := d)
    hφ.continuous.continuousOn
    (fun t _ ↦ (hφ t).hasDerivAt)
    (fun t _ ↦ hφnonneg t)

/-- 势函数外微分沿曲线的密度，就是复合函数 `f ∘ γ` 的一元导数。-/
theorem exactOneForm_curveFormIntegrand {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (γ : ParametrizedCurve n) (t : ℝ)
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : DifferentiableAt ℝ γ t) :
    curveFormIntegrand (exteriorDerivative (functionAsZeroForm f)) γ t =
      deriv (f ∘ γ) t := by
  rw [curveFormIntegrand, exteriorDerivative_zeroForm]
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt t hγ.hasDerivAt
  rw [hcomp.deriv]
  simp [curveVelocity]

/-- **第二型曲线积分基本定理**：恰当 1-形式的积分只取决于两个端点。

这是多元版本的 Newton–Leibniz 公式，也是“梯度场的曲线积分与路径无关”的核心。-/
theorem secondKindCurveIntegral_exact {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (γ : ParametrizedCurve n) (a b : ℝ)
    (hf : Differentiable ℝ f) (hγ : Differentiable ℝ γ)
    (hint : IntervalIntegrable (deriv (f ∘ γ)) volume a b) :
    secondKindCurveIntegral (exteriorDerivative (functionAsZeroForm f)) γ a b =
      f (γ b) - f (γ a) := by
  rw [secondKindCurveIntegral]
  simp_rw [exactOneForm_curveFormIntegrand f γ _ (hf _) (hγ _)]
  exact intervalIntegral.integral_deriv_eq_sub
    (fun t _ ↦ (hf (γ t)).comp t (hγ t)) hint

/-- 2-形式沿参数曲面的有向密度。

先放 `∂ᵤσ`、再放 `∂ᵥσ`；交换二者会因 2-形式的交替性改变符号。-/
def surfaceFormIntegrand {n : ℕ} (ω : DifferentialForm (Fin n → ℝ) 2)
    (σ : ParametrizedSurface n) (p : ℝ × ℝ) : ℝ :=
  ω (σ p) ![surfaceTangent₁ σ p, surfaceTangent₂ σ p]

/-- **第二型曲面积分**：在矩形参数域上积分拉回后的有向 2-形式系数。-/
def secondKindSurfaceIntegral {n : ℕ} (ω : DifferentialForm (Fin n → ℝ) 2)
    (σ : ParametrizedSurface n) (a b c d : ℝ) : ℝ :=
  rectangleIntegral (surfaceFormIntegrand ω σ) a b c d

/-- 在两个 1-形式密度都可积时，第二型曲线积分对形式可加。-/
theorem secondKindCurveIntegral_add {n : ℕ}
    (ω η : DifferentialForm (Fin n → ℝ) 1) (γ : ParametrizedCurve n) (a b : ℝ)
    (hω : IntervalIntegrable (curveFormIntegrand ω γ) volume a b)
    (hη : IntervalIntegrable (curveFormIntegrand η γ) volume a b) :
    secondKindCurveIntegral (ω + η) γ a b =
      secondKindCurveIntegral ω γ a b + secondKindCurveIntegral η γ a b := by
  rw [secondKindCurveIntegral, secondKindCurveIntegral, secondKindCurveIntegral]
  simp only [curveFormIntegrand, Pi.add_apply, ContinuousAlternatingMap.add_apply]
  exact intervalIntegral.integral_add hω hη

/-- 在两个有向面积密度都可积时，第二型曲面积分对形式可加。-/
theorem secondKindSurfaceIntegral_add {n : ℕ}
    (ω η : DifferentialForm (Fin n → ℝ) 2) (σ : ParametrizedSurface n)
    (a b c d : ℝ)
    (hω : IntegrableOn (surfaceFormIntegrand ω σ) (closedRectangle a b c d)
      (volume.prod volume))
    (hη : IntegrableOn (surfaceFormIntegrand η σ) (closedRectangle a b c d)
      (volume.prod volume)) :
    secondKindSurfaceIntegral (ω + η) σ a b c d =
      secondKindSurfaceIntegral ω σ a b c d +
        secondKindSurfaceIntegral η σ a b c d := by
  rw [secondKindSurfaceIntegral, secondKindSurfaceIntegral, secondKindSurfaceIntegral]
  simp only [surfaceFormIntegrand, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    rectangleIntegral]
  exact MeasureTheory.integral_add hω hη

/-! ## 坐标式、反向参数与闭曲线 -/

/-- 把连续协向量场看成 1-形式。

在有限维坐标中，教材常把它写成 `P₁ dx₁ + ⋯ + Pₙ dxₙ`；协向量场写法不依赖
具体基，随后需要时可再展开成各坐标分量。-/
def covectorFieldAsOneForm {n : ℕ}
    (A : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) :
    DifferentialForm (Fin n → ℝ) 1 :=
  fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (Fin n → ℝ) ℝ (0 : Fin 1) (A x)

/-- 协向量场版本恢复教材中的 `A(γ(t))(γ'(t))` 被积式。-/
theorem curveFormIntegrand_covectorField {n : ℕ}
    (A : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
    (γ : ParametrizedCurve n) (t : ℝ) :
    curveFormIntegrand (covectorFieldAsOneForm A) γ t =
      A (γ t) (curveVelocity γ t) := by
  simp [curveFormIntegrand, covectorFieldAsOneForm]

/-- 在区间 `[a,b]` 上反转曲线参数方向：新参数 `t` 对应旧参数 `a+b-t`。-/
def reverseCurve {n : ℕ} (γ : ParametrizedCurve n) (a b : ℝ) : ParametrizedCurve n :=
  γ ∘ fun t ↦ a + b - t

/-- **反向变号**：曲线参数方向反转后，第二型积分改变符号。

第一型弧长在同一操作下保持不变；这一正负号差异正是两类曲线积分的本质区别。-/
theorem secondKindCurveIntegral_reverse {n : ℕ}
    (ω : DifferentialForm (Fin n → ℝ) 1) (γ : ParametrizedCurve n)
    (a b : ℝ) (hγ : Differentiable ℝ γ) :
    secondKindCurveIntegral ω (reverseCurve γ a b) a b =
      -secondKindCurveIntegral ω γ a b := by
  rw [reverseCurve, secondKindCurveIntegral, secondKindCurveIntegral]
  let φ : ℝ → ℝ := fun t ↦ a + b - t
  change (∫ t in a..b, curveFormIntegrand ω (γ ∘ φ) t) = _
  have hφ : ∀ t, HasDerivAt φ (-1) t := fun t ↦
    (hasDerivAt_id t).const_sub (a + b)
  simp_rw [curveFormIntegrand_comp ω γ φ _ (hγ _) (hφ _).differentiableAt]
  have hdiff : Differentiable ℝ φ := fun t ↦ (hφ t).differentiableAt
  have hderiv : deriv φ = fun _ ↦ (-1 : ℝ) := by
    funext t
    exact (hφ t).deriv
  rw [hderiv]
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := φ) (f' := fun _ ↦ (-1 : ℝ))
    (g := curveFormIntegrand ω γ) (a := a) (b := b)
    hdiff.continuous.continuousOn
    (fun t _ ↦ hφ t)
    (fun _ _ ↦ by norm_num)
  calc
    _ = ∫ u in φ a..φ b, curveFormIntegrand ω γ u := by
      simpa only [Function.comp_apply] using hsub
    _ = _ := by
      simp only [φ]
      rw [show a + b - a = b by ring, show a + b - b = a by ring,
        intervalIntegral.integral_symm]

/-- **闭曲线上的恰当形式积分为零**。

若 `γ(a)=γ(b)`，端点差公式的右端为零。这是保守场沿闭路做功为零的微分形式版本。-/
theorem secondKindCurveIntegral_exact_closed {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (γ : ParametrizedCurve n) (a b : ℝ)
    (hf : Differentiable ℝ f) (hγ : Differentiable ℝ γ)
    (hint : IntervalIntegrable (deriv (f ∘ γ)) volume a b)
    (hclosed : γ b = γ a) :
    secondKindCurveIntegral (exteriorDerivative (functionAsZeroForm f)) γ a b = 0 := by
  rw [secondKindCurveIntegral_exact f γ a b hf hγ hint, hclosed, sub_self]

end SandronesLibrary.Analysis.SecondKindIntegrals
