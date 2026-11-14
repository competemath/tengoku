/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.GreenGaussStokes
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / Gauss 与 Stokes 公式：单位立方体与水平单位正方形

本 Entry 服务理论条目 `analysis.multivariable.green-gauss-stokes`（Green、Gauss 与 Stokes
公式）。本文件给出两个标准教材计算。Gauss 例题在单位立方体上取位置向量场，散度恒为 `3`；
Stokes 例题在水平单位正方形上取 1-形式 `x dy`，其拉回为 `u dv`，外微分密度恒为
`1`。两个证明分别调用理论层的 `gauss_box3` 和 `stokes_parametrized_rectangle`，
同时完成最终积分数值的计算。

本文件还给出**定向反例**：Gauss 公式的六面通量用的是外向法向，改成内向法向后整体变号
（`gauss_inward_ne_outward`）；Stokes 公式的曲面方向由切向量次序 `(∂ᵤσ,∂ᵥσ)` 决定，
交换两个切向量后同一 1-形式的边界环流变成 `-1`（`stokes_horizontalUnitSquareRev_xDy`）。
两处的定向约定都不是可以省略的装饰。

> **Entry**: examples.analysis.gauss-stokes
-/

noncomputable section

namespace SandronesLibrary.Examples.GaussStokes

open Set MeasureTheory Matrix
open scoped Interval Matrix
open SandronesLibrary.Analysis.Multivariable
open SandronesLibrary.Analysis.GreenGaussStokes

/-! ## Gauss 公式：单位立方体 -/

/-- 单位立方体的左下端点。-/
def unitCubeLower : Fin 3 → ℝ := fun _ ↦ 0

/-- 单位立方体的右上端点。-/
def unitCubeUpper : Fin 3 → ℝ := fun _ ↦ 1

/-- **Gauss 例题**：单位立方体上位置向量场 `F(x)=x` 的总外向通量等于 `3`。

位置向量场的 Fréchet 导数是恒等映射，故散度为 `1+1+1=3`。调用盒上的 Gauss
公式后，右端成为常数 `3` 在体积为 `1` 的单位立方体上的积分。
@isnad1 id=eq.0h0v.s4.09d958d71782 from=translated src=- shape=91a03b66 vocab=d965542c
-/
theorem gauss_unitCube_identity :
    boxBoundaryFlux3 (fun x : Fin 3 → ℝ ↦ x) unitCubeLower unitCubeUpper = 3 := by
  let F' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    fun _ ↦ ContinuousLinearMap.id ℝ (Fin 3 → ℝ)
  have hab : unitCubeLower ≤ unitCubeUpper := by
    intro i
    simp [unitCubeLower, unitCubeUpper]
  have hdiv : ∀ x, divergence3 F' x = 3 := by
    intro x
    simp [divergence3, F']
  have hint : IntegrableOn (divergence3 F') (Icc unitCubeLower unitCubeUpper) := by
    refine IntegrableOn.congr_fun
      (integrableOn_const (C := (3 : ℝ)) (measure_Icc_lt_top.ne)) ?_
      measurableSet_Icc
    intro x _
    exact (hdiv x).symm
  rw [gauss_box3 unitCubeLower unitCubeUpper hab (fun x ↦ x) F'
    continuous_id.continuousOn (fun x _ ↦ by unfold F'; fun_prop) hint]
  simp_rw [hdiv]
  rw [setIntegral_const]
  change (volume (Icc unitCubeLower unitCubeUpper)).toReal * 3 = 3
  rw [Real.volume_Icc_pi_toReal hab]
  simp [unitCubeLower, unitCubeUpper]

/-! ## Stokes 公式：水平单位正方形 -/

/-- `z=0` 平面内的水平单位正方形参数化 `σ(u,v)=(u,v,0)`。-/
def horizontalUnitSquare : ParametrizedSurface 3 :=
  affinePlane 0 ![1, 0, 0] ![0, 1, 0]

/-- 空间 1-形式 `x dy`：在点 `x` 处把切向量 `v` 映为 `x₀v₁`。-/
def xDyForm (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  x 0 • (ContinuousLinearMap.proj 1)

/-- **Stokes 例题**：水平单位正方形上 `x dy` 的边界环流等于 `1`。

参数化拉回后，`du` 系数为 `0`，`dv` 系数为 `u`，所以外微分密度为 `1`。
参数曲面 Stokes 公式把边界环流化为单位参数正方形上常数 `1` 的积分。
@isnad1 id=eq.0h0v.s5.8fde968ee97f from=translated src=- shape=74c11966 vocab=5a231c23
-/
theorem stokes_horizontalUnitSquare_xDy :
    rectangleBoundaryIntegral
      (surfacePullbackCoeff₁ xDyForm horizontalUnitSquare)
      (surfacePullbackCoeff₂ xDyForm horizontalUnitSquare) 0 0 1 1 = 1 := by
  have hP : surfacePullbackCoeff₁ xDyForm horizontalUnitSquare = fun _ ↦ 0 := by
    funext z
    simp [surfacePullbackCoeff₁, xDyForm, horizontalUnitSquare,
      surfaceTangent₁_affinePlane]
  have hQ : surfacePullbackCoeff₂ xDyForm horizontalUnitSquare = fun z ↦ z.1 := by
    funext z
    simp [surfacePullbackCoeff₂, xDyForm, horizontalUnitSquare, affinePlane,
      surfaceTangent₂_affinePlane]
  let P' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun _ ↦ 0
  let Q' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) :=
    fun _ ↦ ContinuousLinearMap.fst ℝ ℝ ℝ
  have hstokes := stokes_parametrized_rectangle xDyForm horizontalUnitSquare
    P' Q' 0 0 1 1
    (by rw [hP]; fun_prop)
    (by rw [hQ]; fun_prop)
    (by intro z hz; rw [hP]; unfold P'; fun_prop)
    (by intro z hz; rw [hQ]; unfold Q'; fun_prop)
    (by
      have heq : (fun z ↦ Q' z (1, 0) - P' z (0, 1)) = fun _ ↦ (1 : ℝ) := by
        funext z
        simp [P', Q']
      rw [heq]
      exact integrableOn_const ((isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne))
  rw [hstokes]
  simp [P', Q']

/-! ## 定向：外向法向与切向量次序的反例 -/

/-- 单位立方体的**内向**通量：与 `boxBoundaryFlux3` 同一组六个面，但每个面的法向取反。-/
def boxBoundaryFlux3Inward (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (a b : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3,
    ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i)

/-- **内向通量只改符号**：六个面逐面取反，总和取反。
@isnad1 id=eq.0h3v.s5.c9ba6c19c68c from=translated src=- shape=c5290468 vocab=2c6ead85
-/
theorem boxBoundaryFlux3Inward_eq_neg (F : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (a b : Fin 3 → ℝ) :
    boxBoundaryFlux3Inward F a b = -boxBoundaryFlux3 F a b := by
  rw [boxBoundaryFlux3Inward, boxBoundaryFlux3, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **定向反例（Gauss）**：单位立方体上位置向量场的外向通量为 `3`，内向通量为 `-3`，
两者不等。这反驳「通量与法向定向无关」这一误认：`gauss_box3` 的右端散度积分不随定向
改变，故内向约定下公式必然差一个符号。
@isnad1 id=ne.0h0v.s4.01d273742f34 from=translated src=- shape=cb7c17b2 vocab=f765347e
-/
theorem gauss_inward_ne_outward :
    boxBoundaryFlux3Inward (fun x : Fin 3 → ℝ ↦ x) unitCubeLower unitCubeUpper ≠
      boxBoundaryFlux3 (fun x : Fin 3 → ℝ ↦ x) unitCubeLower unitCubeUpper := by
  rw [boxBoundaryFlux3Inward_eq_neg, gauss_unitCube_identity]
  norm_num

/-- 把水平单位正方形的两个切向量次序交换，得到反向定向的参数化 `σ(u,v)=(v,u,0)`。-/
def horizontalUnitSquareRev : ParametrizedSurface 3 :=
  affinePlane 0 ![0, 1, 0] ![1, 0, 0]

/-- **定向反例（Stokes）**：在反向参数化 `σ(u,v)=(v,u,0)` 下，同一 1-形式 `x dy`
的拉回变成 `v du`，其外微分密度为 `-1`，于是边界环流为 `-1`，而原参数化下为 `1`。
这反驳「Stokes 公式的环流与曲面定向无关」这一误认：切向量次序 `(∂ᵤσ,∂ᵥσ)` 决定曲面
方向，交换次序恰好改变符号。
@isnad1 id=eq.0h0v.s5.b616e63de836 from=translated src=- shape=8b0249f0 vocab=e2a6138e
-/
theorem stokes_horizontalUnitSquareRev_xDy :
    rectangleBoundaryIntegral
      (surfacePullbackCoeff₁ xDyForm horizontalUnitSquareRev)
      (surfacePullbackCoeff₂ xDyForm horizontalUnitSquareRev) 0 0 1 1 = -1 := by
  have hP : surfacePullbackCoeff₁ xDyForm horizontalUnitSquareRev = fun z ↦ z.2 := by
    funext z
    simp [surfacePullbackCoeff₁, xDyForm, horizontalUnitSquareRev, affinePlane,
      surfaceTangent₁_affinePlane]
  have hQ : surfacePullbackCoeff₂ xDyForm horizontalUnitSquareRev = fun _ ↦ 0 := by
    funext z
    simp [surfacePullbackCoeff₂, xDyForm, horizontalUnitSquareRev, affinePlane,
      surfaceTangent₂_affinePlane]
  rw [hP, hQ, rectangleBoundaryIntegral]
  norm_num

end SandronesLibrary.Examples.GaussStokes
