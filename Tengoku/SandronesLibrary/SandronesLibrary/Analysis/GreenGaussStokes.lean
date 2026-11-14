/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.SecondKindIntegrals
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.NormalDomain
import Tengoku.Seed.MeasureTheory.Integral.DivergenceTheorem
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.LinearAlgebra.CrossProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Green、Gauss 与 Stokes 公式

本模块从二维矩形上的 Green 公式开始构建积分定理主线。Green 公式把区域内部的
旋度积分与逆时针边界上的第二型曲线积分联系起来：

`∮∂R P dx + Q dy = ∬R (∂Q/∂x - ∂P/∂y) dx dy`。

Mathlib 已证明矩形上的 Bochner 散度定理。令散度定理中的向量场为 `(Q,-P)`，其
散度正好是 `∂Q/∂x-∂P/∂y`，而外法向通量逐边展开后正好是逆时针的
`P dx+Q dy`。这给出 Green 公式，同时明确验证边界的四个符号。

在此基础上，本模块继续给出三维 Gauss 散度公式、经典 Stokes 公式、
`curl F · (σᵤ × σᵥ)` 坐标形式，以及 Green、Gauss、Stokes 三者的有限分片拼接接口。

> **Entry**: analysis.multivariable.green-gauss-stokes
-/

noncomputable section

namespace SandronesLibrary.Analysis.GreenGaussStokes

open Set Finset MeasureTheory
open scoped Interval Matrix
open SandronesLibrary.Analysis.Multivariable

/-- 逆时针遍历矩形边界时 `P dx + Q dy` 的四边积分之和。

四项依次对应下边、右边、上边、左边；上边和左边因逆时针方向与坐标正向相反而
带负号。-/
def rectangleBoundaryIntegral (P Q : ℝ × ℝ → ℝ) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  (∫ x in a₁..b₁, P (x, a₂)) +
    (∫ y in a₂..b₂, Q (b₁, y)) -
    (∫ x in a₁..b₁, P (x, b₂)) -
    (∫ y in a₂..b₂, Q (a₁, y))

/-- **矩形 Green 公式**：逆时针边界上的 `P dx+Q dy` 等于区域内旋度积分。

`P' z`、`Q' z` 是两个函数在 `z` 处的 Fréchet 导数；在标准坐标方向求值后，
`Q' z (1,0)` 是 `∂Q/∂x`，`P' z (0,1)` 是 `∂P/∂y`。-/
theorem green_rectangle
    (P Q : ℝ × ℝ → ℝ)
    (P' Q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (a₁ a₂ b₁ b₂ : ℝ)
    (hPcont : ContinuousOn P ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (hQcont : ContinuousOn Q ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (hPderiv : ∀ z ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
        Ioo (min a₂ b₂) (max a₂ b₂), HasFDerivAt P (P' z) z)
    (hQderiv : ∀ z ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
        Ioo (min a₂ b₂) (max a₂ b₂), HasFDerivAt Q (Q' z) z)
    (hint : IntegrableOn (fun z ↦ Q' z (1, 0) - P' z (0, 1))
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
    rectangleBoundaryIntegral P Q a₁ a₂ b₁ b₂ =
      ∫ x in a₁..b₁, ∫ y in a₂..b₂,
        Q' (x, y) (1, 0) - P' (x, y) (0, 1) := by
  have hdiv := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    Q (-P) Q' (-P') a₁ a₂ b₁ b₂
    hQcont hPcont.neg hQderiv
    (fun z hz ↦ (hPderiv z hz).neg)
    (by
      simpa only [Pi.neg_apply, neg_apply, sub_eq_add_neg]
        using hint)
  rw [rectangleBoundaryIntegral]
  calc
    _ = (((∫ x in a₁..b₁, (-P) (x, b₂)) -
          ∫ x in a₁..b₁, (-P) (x, a₂)) +
          ∫ y in a₂..b₂, Q (b₁, y)) -
          ∫ y in a₂..b₂, Q (a₁, y) := by
      simp only [Pi.neg_apply, intervalIntegral.integral_neg]
      abel
    _ = _ := hdiv.symm

/-! ## 矩形剖分与公共边抵消 -/

/-- 矩形沿竖线 `x=c` 分成两块时，两块公共边方向相反，边界积分相消。

右侧两块分别沿各自边界逆时针遍历，所以公共竖边在左块中向上、在右块中向下；
这两个积分在展开式中直接抵消。外边界的两条水平边则由区间积分的可加性重新拼合。-/
theorem rectangleBoundaryIntegral_split_vertical
    (P Q : ℝ × ℝ → ℝ) (a c b d e : ℝ)
    (hPac : IntervalIntegrable (fun x ↦ P (x, d)) volume a c)
    (hPcb : IntervalIntegrable (fun x ↦ P (x, d)) volume c b)
    (hPac' : IntervalIntegrable (fun x ↦ P (x, e)) volume a c)
    (hPcb' : IntervalIntegrable (fun x ↦ P (x, e)) volume c b) :
    rectangleBoundaryIntegral P Q a d b e =
      rectangleBoundaryIntegral P Q a d c e +
        rectangleBoundaryIntegral P Q c d b e := by
  rw [rectangleBoundaryIntegral, rectangleBoundaryIntegral,
    rectangleBoundaryIntegral,
    ← intervalIntegral.integral_add_adjacent_intervals hPac hPcb,
    ← intervalIntegral.integral_add_adjacent_intervals hPac' hPcb']
  ring

/-- 矩形沿横线 `y=c` 分成两块时，两块公共边方向相反，边界积分相消。

公共横边在下块中向左、在上块中向右；外边界的两条竖边由区间积分可加性拼合。-/
theorem rectangleBoundaryIntegral_split_horizontal
    (P Q : ℝ × ℝ → ℝ) (a b d c e : ℝ)
    (hQdc : IntervalIntegrable (fun y ↦ Q (b, y)) volume d c)
    (hQce : IntervalIntegrable (fun y ↦ Q (b, y)) volume c e)
    (hQdc' : IntervalIntegrable (fun y ↦ Q (a, y)) volume d c)
    (hQce' : IntervalIntegrable (fun y ↦ Q (a, y)) volume c e) :
    rectangleBoundaryIntegral P Q a d b e =
      rectangleBoundaryIntegral P Q a d b c +
        rectangleBoundaryIntegral P Q a c b e := by
  rw [rectangleBoundaryIntegral, rectangleBoundaryIntegral,
    rectangleBoundaryIntegral,
    ← intervalIntegral.integral_add_adjacent_intervals hQdc hQce,
    ← intervalIntegral.integral_add_adjacent_intervals hQdc' hQce']
  ring

/-! ## 曲边正常域上的 Green 公式 -/

/-- 同时为 `x` 型和 `y` 型的正常域，其逆时针边界积分。

第一项沿下边从左向右并沿上边从右向左，第二项沿右边从下向上并沿左边从上向下。
这种写法不要求把四段边界预先拼成一条分段参数曲线。-/
def normalDomainBoundaryIntegral
    (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (lower upper left right : ℝ → ℝ) : ℝ :=
  (∫ x in Icc a b, P (x, lower x) - P (x, upper x)) +
    ∫ y in Icc c d, Q (right y, y) - Q (left y, y)

/-- **双正常域 Green 公式**。

假设同一区域既可写成竖直正常域
`lower x ≤ y ≤ upper x`，也可写成水平正常域
`left y ≤ x ≤ right y`。分别对 `-∂P/∂y` 使用竖直截面、对 `∂Q/∂x` 使用水平截面，
再在每条一维截面上应用 Newton–Leibniz 公式，即得到曲边区域的 Green 公式。

这一版本已超出矩形：圆盘、椭圆以及许多由四条函数图像围成的区域都可直接套用。-/
theorem green_binormal_domain
    (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (lower upper left right : ℝ → ℝ)
    (hlower : Continuous lower) (hupper : Continuous upper)
    (hleft : Continuous left) (hright : Continuous right)
    (hlu : ∀ x ∈ Icc a b, lower x ≤ upper x)
    (hlr : ∀ y ∈ Icc c d, left y ≤ right y)
    (hdomains : xNormalDomain a b lower upper =
      yNormalDomain c d left right)
    (hPy : IntegrableOn (fun z ↦ deriv (fun y ↦ P (z.1, y)) z.2)
      (xNormalDomain a b lower upper) (volume.prod volume))
    (hQx : IntegrableOn (fun z ↦ deriv (fun x ↦ Q (x, z.2)) z.1)
      (yNormalDomain c d left right) (volume.prod volume))
    (hPdiff : ∀ x ∈ Icc a b, ∀ y ∈ Icc (lower x) (upper x),
      DifferentiableAt ℝ (fun t ↦ P (x, t)) y)
    (hQdiff : ∀ y ∈ Icc c d, ∀ x ∈ Icc (left y) (right y),
      DifferentiableAt ℝ (fun t ↦ Q (t, y)) x)
    (hPint : ∀ x ∈ Icc a b,
      IntervalIntegrable (deriv (fun y ↦ P (x, y))) volume (lower x) (upper x))
    (hQint : ∀ y ∈ Icc c d,
      IntervalIntegrable (deriv (fun x ↦ Q (x, y))) volume (left y) (right y)) :
    normalDomainBoundaryIntegral P Q a b c d lower upper left right =
      ∫ z in xNormalDomain a b lower upper,
        (deriv (fun x ↦ Q (x, z.2)) z.1 -
          deriv (fun y ↦ P (z.1, y)) z.2) ∂(volume.prod volume) := by
  have hPfiber : ∀ x ∈ Icc a b,
      (∫ y in Icc (lower x) (upper x), deriv (fun t ↦ P (x, t)) y) =
        P (x, upper x) - P (x, lower x) := by
    intro x hx
    calc
      _ = ∫ y in lower x..upper x, deriv (fun t ↦ P (x, t)) y := by
        rw [intervalIntegral.integral_of_le (hlu x hx), integral_Icc_eq_integral_Ioc]
      _ = _ := intervalIntegral.integral_deriv_eq_sub
        (fun y hy ↦ hPdiff x hx y (by
          simpa [uIcc_of_le (hlu x hx)] using hy)) (hPint x hx)
  have hQfiber : ∀ y ∈ Icc c d,
      (∫ x in Icc (left y) (right y), deriv (fun t ↦ Q (t, y)) x) =
        Q (right y, y) - Q (left y, y) := by
    intro y hy
    calc
      _ = ∫ x in left y..right y, deriv (fun t ↦ Q (t, y)) x := by
        rw [intervalIntegral.integral_of_le (hlr y hy), integral_Icc_eq_integral_Ioc]
      _ = _ := intervalIntegral.integral_deriv_eq_sub
        (fun x hx ↦ hQdiff y hy x (by
          simpa [uIcc_of_le (hlr y hy)] using hx)) (hQint y hy)
  have hPregion :
      (∫ z in xNormalDomain a b lower upper,
        deriv (fun y ↦ P (z.1, y)) z.2 ∂(volume.prod volume)) =
        ∫ x in Icc a b, P (x, upper x) - P (x, lower x) := by
    rw [integral_xNormalDomain_eq_iterated hlower hupper hPy]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact hPfiber x hx
  have hQregion :
      (∫ z in xNormalDomain a b lower upper,
        deriv (fun x ↦ Q (x, z.2)) z.1 ∂(volume.prod volume)) =
        ∫ y in Icc c d, Q (right y, y) - Q (left y, y) := by
    rw [hdomains]
    rw [integral_yNormalDomain_eq_iterated_of_measurable
      hleft.measurable hright.measurable hQx]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    exact hQfiber y hy
  have hQx' : IntegrableOn (fun z ↦ deriv (fun x ↦ Q (x, z.2)) z.1)
      (xNormalDomain a b lower upper) (volume.prod volume) := by
    rw [hdomains]
    exact hQx
  have hPboundary :
      (∫ x in Icc a b, P (x, lower x) - P (x, upper x)) =
        -(∫ x in Icc a b, P (x, upper x) - P (x, lower x)) := by
    rw [← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    simp
  rw [MeasureTheory.integral_sub hQx' hPy, hQregion, hPregion,
    normalDomainBoundaryIntegral, hPboundary]
  ring

/-! ## 有限分片区域的 Green 拼接定理 -/

/-- 有限 Green 分片的分析数据。

`cell i` 是第 `i` 个区域片。要求各片可测、片上旋度密度可积，并且不同片互不相交。
教材剖分中不同闭片可能共享边界；实际应用时可把公共零测边界只分配给其中一片，
或改用互不相交的半开片，而不改变区域积分。-/
structure GreenFiniteDecomposition {ι : Type*} (pieces : Finset ι)
    (cell : ι → Set (ℝ × ℝ)) (curlDensity : ℝ × ℝ → ℝ) : Prop where
  measurable : ∀ i ∈ pieces, MeasurableSet (cell i)
  pairwiseDisjoint : Set.Pairwise (↑pieces) (Function.onFun Disjoint cell)
  integrable : ∀ i ∈ pieces,
    IntegrableOn curlDensity (cell i) (volume.prod volume)

/-- **有限分片 Green 拼接定理**。

若每片的有向边界积分等于该片的旋度积分，而所有内部公共边成对反向抵消，
则剩余外边界积分等于整个有限并区域上的旋度积分。

定理把一般分片 Jordan 域证明分成两个独立任务：分析上对每个正常片使用局部 Green
公式；几何上证明公共边在两片中的方向相反。完成这两个任务后，整体结论由有限可加性
自动得到。-/
theorem green_finite_decomposition
    {ι : Type*} (pieces : Finset ι)
    (cell : ι → Set (ℝ × ℝ)) (curlDensity : ℝ × ℝ → ℝ)
    (localBoundary : ι → ℝ) (externalBoundary : ℝ)
    (hdecomp : GreenFiniteDecomposition pieces cell curlDensity)
    (hlocal : ∀ i ∈ pieces, localBoundary i =
      ∫ z in cell i, curlDensity z ∂(volume.prod volume))
    (hcancel : externalBoundary = ∑ i ∈ pieces, localBoundary i) :
    externalBoundary =
      ∫ z in ⋃ i ∈ pieces, cell i, curlDensity z ∂(volume.prod volume) := by
  classical
  rw [hcancel]
  calc
    ∑ i ∈ pieces, localBoundary i =
        ∑ i ∈ pieces, ∫ z in cell i, curlDensity z ∂(volume.prod volume) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hlocal i hi
    _ = _ := (MeasureTheory.integral_biUnion_finset pieces hdecomp.measurable
      hdecomp.pairwiseDisjoint hdecomp.integrable).symm

/-! ### 用有向边关联数自动验证公共边抵消 -/

/-- 按有向边出现次数计算边界积分；负系数表示反向遍历。

`incidence e = 1` 表示正向走一次边 `e`，`-1` 表示反向走一次，零表示该边不在边界中。
允许任意整数是为了兼容多重覆盖和更一般的有限边界链。-/
def orientedBoundaryValue {ε : Type*} (edges : Finset ε)
    (incidence : ε → ℤ) (edgeIntegral : ε → ℝ) : ℝ :=
  ∑ e ∈ edges, incidence e • edgeIntegral e

/-- 逐边相加局部边界出现次数，等价于相加各片的边界积分。-/
theorem orientedBoundaryValue_sum {ι ε : Type*}
    (pieces : Finset ι) (edges : Finset ε)
    (incidence : ι → ε → ℤ) (edgeIntegral : ε → ℝ) :
    orientedBoundaryValue edges (fun e ↦ ∑ i ∈ pieces, incidence i e) edgeIntegral =
      ∑ i ∈ pieces, orientedBoundaryValue edges (incidence i) edgeIntegral := by
  classical
  simp only [orientedBoundaryValue]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_smul]

/-- 同一组边以相反方向各出现一次时，总边界积分为零。-/
@[simp] theorem orientedBoundaryValue_add_neg {ε : Type*} (edges : Finset ε)
    (incidence : ε → ℤ) (edgeIntegral : ε → ℝ) :
    orientedBoundaryValue edges (fun e ↦ incidence e + -incidence e) edgeIntegral = 0 := by
  simp [orientedBoundaryValue]

/-- **按边关联数自动拼接 Green 公式**。

若外边界中每条有向边的系数等于它在所有局部边界中的系数之和，则内部公共边的
`+1` 与 `-1` 自动抵消，无需另行假设边界积分的实数等式。与
`green_finite_decomposition` 相比，本定理把“公共边抵消”从一个待手证的数值等式
提升为逐边的整数关联数核对。-/
theorem green_finite_decomposition_of_edge_incidence
    {ι ε : Type*} (pieces : Finset ι) (edges : Finset ε)
    (cell : ι → Set (ℝ × ℝ)) (curlDensity : ℝ × ℝ → ℝ)
    (localIncidence : ι → ε → ℤ) (externalIncidence : ε → ℤ)
    (edgeIntegral : ε → ℝ)
    (hdecomp : GreenFiniteDecomposition pieces cell curlDensity)
    (hlocal : ∀ i ∈ pieces,
      orientedBoundaryValue edges (localIncidence i) edgeIntegral =
        ∫ z in cell i, curlDensity z ∂(volume.prod volume))
    (hincidence : ∀ e ∈ edges,
      externalIncidence e = ∑ i ∈ pieces, localIncidence i e) :
    orientedBoundaryValue edges externalIncidence edgeIntegral =
      ∫ z in ⋃ i ∈ pieces, cell i, curlDensity z ∂(volume.prod volume) := by
  apply green_finite_decomposition pieces cell curlDensity
    (fun i ↦ orientedBoundaryValue edges (localIncidence i) edgeIntegral)
    (orientedBoundaryValue edges externalIncidence edgeIntegral) hdecomp hlocal
  calc
    orientedBoundaryValue edges externalIncidence edgeIntegral =
        orientedBoundaryValue edges (fun e ↦ ∑ i ∈ pieces, localIncidence i e)
          edgeIntegral := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hincidence e he]
    _ = _ := orientedBoundaryValue_sum pieces edges localIncidence edgeIntegral

/-! ## 三维 Gauss 散度公式 -/

/-- 三维向量场导数的散度：把导数分别作用于三个标准基向量，再取对应分量之和。-/
def divergence3
    (F' : (Fin (2 + 1) → ℝ) →
      (Fin (2 + 1) → ℝ) →L[ℝ] (Fin (2 + 1) → ℝ))
    (x : Fin (2 + 1) → ℝ) : ℝ :=
  ∑ i : Fin (2 + 1), F' x (Pi.single i 1) i

/-- 三维盒六个面的外向通量之和。

对每个坐标方向 `i`，先取上面 `xᵢ=bᵢ` 的正向通量，再减去下面 `xᵢ=aᵢ`
的通量；三个方向各有两个面，合计六面。-/
def boxBoundaryFlux3 (F : (Fin (2 + 1) → ℝ) → (Fin (2 + 1) → ℝ))
    (a b : Fin (2 + 1) → ℝ) : ℝ :=
  ∑ i : Fin (2 + 1),
    ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        F (i.insertNth (b i) y) i) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        F (i.insertNth (a i) y) i)

/-- **三维盒上的 Gauss 散度公式**：六面外向通量等于盒内散度的体积分。-/
theorem gauss_box3 (a b : Fin (2 + 1) → ℝ) (hab : a ≤ b)
    (F : (Fin (2 + 1) → ℝ) → (Fin (2 + 1) → ℝ))
    (F' : (Fin (2 + 1) → ℝ) →
      (Fin (2 + 1) → ℝ) →L[ℝ] (Fin (2 + 1) → ℝ))
    (hFcont : ContinuousOn F (Icc a b))
    (hFderiv : ∀ x ∈ Set.pi Set.univ (fun i ↦ Ioo (a i) (b i)),
      HasFDerivAt F (F' x) x)
    (hint : IntegrableOn (divergence3 F') (Icc a b)) :
    boxBoundaryFlux3 F a b = ∫ x in Icc a b, divergence3 F' x := by
  have h := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
    (n := 2) (a := a) (b := b) hab F F' ∅ Set.countable_empty hFcont
    (fun x hx ↦ hFderiv x hx.1)
    (by
      change IntegrableOn (divergence3 F') (Icc a b)
      exact hint)
  simpa only [boxBoundaryFlux3, divergence3] using h.symm

/-! ### 有限体元剖分上的 Gauss 拼接 -/

/-- 三维 Gauss 公式的有限体元剖分数据。

各体元在测度意义下互不相交；共享的二维面是零体积集，因此应用时可以把它只分配给
一个体元，而不改变散度的体积分。-/
structure GaussFiniteDecomposition {ι : Type*} (pieces : Finset ι)
    (cell : ι → Set (Fin 3 → ℝ)) (divDensity : (Fin 3 → ℝ) → ℝ) : Prop where
  measurable : ∀ i ∈ pieces, MeasurableSet (cell i)
  pairwiseDisjoint : Set.Pairwise (↑pieces) (Function.onFun Disjoint cell)
  integrable : ∀ i ∈ pieces, IntegrableOn divDensity (cell i) volume

/-- **有限体元 Gauss 拼接定理**。

每个体元上若“外向通量 = 散度体积分”，并且局部通量之和等于整体外边界通量，
则有限可加性给出整个剖分区域上的 Gauss 公式。-/
theorem gauss_finite_decomposition
    {ι : Type*} (pieces : Finset ι)
    (cell : ι → Set (Fin 3 → ℝ)) (divDensity : (Fin 3 → ℝ) → ℝ)
    (localFlux : ι → ℝ) (externalFlux : ℝ)
    (hdecomp : GaussFiniteDecomposition pieces cell divDensity)
    (hlocal : ∀ i ∈ pieces, localFlux i = ∫ x in cell i, divDensity x)
    (hcancel : externalFlux = ∑ i ∈ pieces, localFlux i) :
    externalFlux = ∫ x in ⋃ i ∈ pieces, cell i, divDensity x := by
  classical
  rw [hcancel]
  calc
    ∑ i ∈ pieces, localFlux i =
        ∑ i ∈ pieces, ∫ x in cell i, divDensity x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hlocal i hi
    _ = _ := (MeasureTheory.integral_biUnion_finset pieces hdecomp.measurable
      hdecomp.pairwiseDisjoint hdecomp.integrable).symm

/-- **按有向面关联数自动拼接 Gauss 公式**。

每个面选定参考方向；局部体元外法向与参考方向相同时记 `+1`，相反时记 `-1`。
内部公共面由两个相邻体元给出相反系数，故自动消失，剩下的恰是整体外边界。-/
theorem gauss_finite_decomposition_of_face_incidence
    {ι φ : Type*} (pieces : Finset ι) (faces : Finset φ)
    (cell : ι → Set (Fin 3 → ℝ)) (divDensity : (Fin 3 → ℝ) → ℝ)
    (localIncidence : ι → φ → ℤ) (externalIncidence : φ → ℤ)
    (faceFlux : φ → ℝ)
    (hdecomp : GaussFiniteDecomposition pieces cell divDensity)
    (hlocal : ∀ i ∈ pieces,
      orientedBoundaryValue faces (localIncidence i) faceFlux =
        ∫ x in cell i, divDensity x)
    (hincidence : ∀ f ∈ faces,
      externalIncidence f = ∑ i ∈ pieces, localIncidence i f) :
    orientedBoundaryValue faces externalIncidence faceFlux =
      ∫ x in ⋃ i ∈ pieces, cell i, divDensity x := by
  apply gauss_finite_decomposition pieces cell divDensity
    (fun i ↦ orientedBoundaryValue faces (localIncidence i) faceFlux)
    (orientedBoundaryValue faces externalIncidence faceFlux) hdecomp hlocal
  calc
    orientedBoundaryValue faces externalIncidence faceFlux =
        orientedBoundaryValue faces
          (fun f ↦ ∑ i ∈ pieces, localIncidence i f) faceFlux := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [hincidence f hf]
    _ = _ := orientedBoundaryValue_sum pieces faces localIncidence faceFlux

/-! ## 参数曲面上的经典 Stokes 公式 -/

/-- 空间协向量场沿参数曲面的第一个拉回系数 `A(σ(u,v))(∂ᵤσ)`。-/
def surfacePullbackCoeff₁
    (A : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ)
    (σ : ParametrizedSurface 3) (p : ℝ × ℝ) : ℝ :=
  A (σ p) (surfaceTangent₁ σ p)

/-- 空间协向量场沿参数曲面的第二个拉回系数 `A(σ(u,v))(∂ᵥσ)`。-/
def surfacePullbackCoeff₂
    (A : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ)
    (σ : ParametrizedSurface 3) (p : ℝ × ℝ) : ℝ :=
  A (σ p) (surfaceTangent₂ σ p)

/-- **矩形参数曲面上的 Stokes 公式**。

空间 1-形式沿曲面参数化拉回后写成 `P du + Q dv`。曲面边界上的有向积分等于
参数矩形边界上的拉回积分；Green 公式再把它化为
`∬(∂Q/∂u-∂P/∂v) du dv`。切向量次序 `(∂ᵤσ,∂ᵥσ)` 决定曲面方向，矩形边界
随之取相容的逆时针方向。-/
theorem stokes_parametrized_rectangle
    (A : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ)
    (σ : ParametrizedSurface 3)
    (P' Q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (a₁ a₂ b₁ b₂ : ℝ)
    (hPcont : ContinuousOn (surfacePullbackCoeff₁ A σ)
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (hQcont : ContinuousOn (surfacePullbackCoeff₂ A σ)
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (hPderiv : ∀ z ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
        Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt (surfacePullbackCoeff₁ A σ) (P' z) z)
    (hQderiv : ∀ z ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
        Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt (surfacePullbackCoeff₂ A σ) (Q' z) z)
    (hint : IntegrableOn (fun z ↦ Q' z (1, 0) - P' z (0, 1))
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]])) :
    rectangleBoundaryIntegral (surfacePullbackCoeff₁ A σ)
        (surfacePullbackCoeff₂ A σ) a₁ a₂ b₁ b₂ =
      ∫ u in a₁..b₁, ∫ v in a₂..b₂,
        Q' (u, v) (1, 0) - P' (u, v) (0, 1) := by
  exact green_rectangle
    (surfacePullbackCoeff₁ A σ) (surfacePullbackCoeff₂ A σ)
    P' Q' a₁ a₂ b₁ b₂ hPcont hQcont hPderiv hQderiv hint

/-! ### Stokes 公式的三维向量形式 -/

open Matrix

/-- 三阶 Jacobian 矩阵对应的旋度向量。

这里采用分析教材的 Jacobian 下标约定 `J i j = ∂ⱼFᵢ`，所以三个分量依次是
`∂₂F₃-∂₃F₂`、`∂₃F₁-∂₁F₃`、`∂₁F₂-∂₂F₁`（Lean 下标从零开始）。-/
def curlMatrix3 (J : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  ![J 2 1 - J 1 2, J 0 2 - J 2 0, J 1 0 - J 0 1]

/-- 旋度与有向面积向量的配对，等于 Jacobian 反对称部分在两条切向量上的值。

这是经典 Stokes 公式中坐标记号与微分形式记号之间的核心代数恒等式：
`curl F · (u × v) = DF(u) · v - DF(v) · u`。-/
theorem curlMatrix3_dot_cross (J : Matrix (Fin 3) (Fin 3) ℝ)
    (u v : Fin 3 → ℝ) :
    curlMatrix3 J ⬝ᵥ (u ⨯₃ v) =
      (J *ᵥ u) ⬝ᵥ v - (J *ᵥ v) ⬝ᵥ u := by
  simp only [curlMatrix3, cross_apply, mulVec, dotProduct, Fin.sum_univ_three]
  dsimp only [Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- 若拉回 1-形式的外微分密度已经写成 Jacobian 的反对称部分，
则它正是经典向量记号 `curl F · (σᵤ × σᵥ)`。-/
theorem pullback_curl_density_eq_dot_cross
    (J : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ)
    (Puv Quv : ℝ)
    (hP : Puv = (J *ᵥ v) ⬝ᵥ u)
    (hQ : Quv = (J *ᵥ u) ⬝ᵥ v) :
    Quv - Puv = curlMatrix3 J ⬝ᵥ (u ⨯₃ v) := by
  rw [hP, hQ, curlMatrix3_dot_cross]

/-- **矩形参数曲面上 Stokes 公式的经典三维坐标形式**。

假设拉回形式的二维旋度密度已经由链式法则整理成空间 Jacobian 的反对称部分，
前一个代数恒等式便把 Green 公式的被积函数改写为
`curl F · (∂ᵤσ × ∂ᵥσ)`。叉积的次序与参数曲面的既定方向一致。-/
theorem stokes_parametrized_rectangle_curl
    (A : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ)
    (σ : ParametrizedSurface 3)
    (P' Q' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ)
    (J : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (a₁ a₂ b₁ b₂ : ℝ)
    (hPcont : ContinuousOn (surfacePullbackCoeff₁ A σ)
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (hQcont : ContinuousOn (surfacePullbackCoeff₂ A σ)
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (hPderiv : ∀ z ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
        Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt (surfacePullbackCoeff₁ A σ) (P' z) z)
    (hQderiv : ∀ z ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ
        Ioo (min a₂ b₂) (max a₂ b₂),
      HasFDerivAt (surfacePullbackCoeff₂ A σ) (Q' z) z)
    (hint : IntegrableOn (fun z ↦ Q' z (1, 0) - P' z (0, 1))
      ([[a₁, b₁]] ×ˢ [[a₂, b₂]]))
    (hcurl : ∀ z, Q' z (1, 0) - P' z (0, 1) =
      curlMatrix3 (J z) ⬝ᵥ
        (surfaceTangent₁ σ z ⨯₃ surfaceTangent₂ σ z)) :
    rectangleBoundaryIntegral (surfacePullbackCoeff₁ A σ)
        (surfacePullbackCoeff₂ A σ) a₁ a₂ b₁ b₂ =
      ∫ u in a₁..b₁, ∫ v in a₂..b₂,
        curlMatrix3 (J (u, v)) ⬝ᵥ
          (surfaceTangent₁ σ (u, v) ⨯₃ surfaceTangent₂ σ (u, v)) := by
  rw [stokes_parametrized_rectangle A σ P' Q' a₁ a₂ b₁ b₂
    hPcont hQcont hPderiv hQderiv hint]
  apply intervalIntegral.integral_congr
  intro u _
  apply intervalIntegral.integral_congr
  intro v _
  exact hcurl (u, v)

/-! ### 有限曲面片上的 Stokes 拼接 -/

/-- **同一参数化下有限曲面片的 Stokes 拼接定理**。

每个参数片上先使用局部 Stokes 公式；同一条空间公共边在相邻曲面片的诱导方向相反，
因而其整数关联数相消。剩余边关联数描述整体曲面的有向边界，而右侧是所有参数片上
拉回外微分密度的积分。

这里假设各片来自同一个参数平面的互不相交子域，因此可复用二维有限分片的测度结构；
曲面片在三维空间中的公共边，则由有向边标签和关联数记录。多个互不相关坐标图的情形
还需要先把参数域做成带图标签的不交并。-/
theorem stokes_finite_patches_of_edge_incidence
    {ι ε : Type*} (patches : Finset ι) (edges : Finset ε)
    (parameterCell : ι → Set (ℝ × ℝ))
    (pulledBackExteriorDerivative : ℝ × ℝ → ℝ)
    (localIncidence : ι → ε → ℤ) (externalIncidence : ε → ℤ)
    (edgeIntegral : ε → ℝ)
    (hdecomp : GreenFiniteDecomposition patches parameterCell
      pulledBackExteriorDerivative)
    (hlocal : ∀ i ∈ patches,
      orientedBoundaryValue edges (localIncidence i) edgeIntegral =
        ∫ p in parameterCell i,
          pulledBackExteriorDerivative p ∂(volume.prod volume))
    (hincidence : ∀ e ∈ edges,
      externalIncidence e = ∑ i ∈ patches, localIncidence i e) :
    orientedBoundaryValue edges externalIncidence edgeIntegral =
      ∫ p in ⋃ i ∈ patches, parameterCell i,
        pulledBackExteriorDerivative p ∂(volume.prod volume) := by
  exact green_finite_decomposition_of_edge_incidence patches edges parameterCell
    pulledBackExteriorDerivative localIncidence externalIncidence edgeIntegral
    hdecomp hlocal hincidence

/-! ### 多坐标图曲面的 Stokes 拼接 -/

/-- 有限个参数曲面片上的拉回外微分积分之和。

每个曲面片保留自己的参数域和拉回密度；因此这里取有限和，而不把不同坐标图中的
参数点误当作同一个二维空间中的点。-/
def finiteAtlasSurfaceIntegral {ι : Type*} (patches : Finset ι)
    (parameterDomain : ι → Set (ℝ × ℝ))
    (pulledBackExteriorDerivative : ι → ℝ × ℝ → ℝ) : ℝ :=
  ∑ i ∈ patches, ∫ p in parameterDomain i,
    pulledBackExteriorDerivative i p ∂(volume.prod volume)

/-- **有限坐标图 Stokes 拼接定理**。

每片可使用不同参数域、参数化与拉回密度。局部 Stokes 公式给出每片边界积分；
不同图中的同一条空间公共边通过统一边标签识别。逐边关联数求和后，内部边的两个
相反诱导方向自动抵消，留下整体外边界。

本定理完成了从单一矩形参数片到有限图册曲面的代数拼接层。进一步处理光滑流形上的
一般 Stokes 定理，还需要图册细化、单位分解以及坐标无关的曲面积分结构。-/
theorem stokes_finite_atlas_of_edge_incidence
    {ι ε : Type*} (patches : Finset ι) (edges : Finset ε)
    (parameterDomain : ι → Set (ℝ × ℝ))
    (pulledBackExteriorDerivative : ι → ℝ × ℝ → ℝ)
    (localIncidence : ι → ε → ℤ) (externalIncidence : ε → ℤ)
    (edgeIntegral : ε → ℝ)
    (hlocal : ∀ i ∈ patches,
      orientedBoundaryValue edges (localIncidence i) edgeIntegral =
        ∫ p in parameterDomain i,
          pulledBackExteriorDerivative i p ∂(volume.prod volume))
    (hincidence : ∀ e ∈ edges,
      externalIncidence e = ∑ i ∈ patches, localIncidence i e) :
    orientedBoundaryValue edges externalIncidence edgeIntegral =
      finiteAtlasSurfaceIntegral patches parameterDomain
        pulledBackExteriorDerivative := by
  classical
  calc
    orientedBoundaryValue edges externalIncidence edgeIntegral =
        orientedBoundaryValue edges
          (fun e ↦ ∑ i ∈ patches, localIncidence i e) edgeIntegral := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hincidence e he]
    _ = ∑ i ∈ patches,
        orientedBoundaryValue edges (localIncidence i) edgeIntegral :=
      orientedBoundaryValue_sum patches edges localIncidence edgeIntegral
    _ = finiteAtlasSurfaceIntegral patches parameterDomain
        pulledBackExteriorDerivative := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hlocal i hi

/-- **闭曲面的 Stokes 推论**：无边界有限曲面上，外微分的曲面积分为零。

经典向量语言中，这给出闭曲面上旋度通量为零。证明只需观察整体外边界的每条边
关联数都为零，再应用有限坐标图 Stokes 拼接定理。-/
theorem stokes_closed_finite_atlas
    {ι ε : Type*} (patches : Finset ι) (edges : Finset ε)
    (parameterDomain : ι → Set (ℝ × ℝ))
    (pulledBackExteriorDerivative : ι → ℝ × ℝ → ℝ)
    (localIncidence : ι → ε → ℤ) (externalIncidence : ε → ℤ)
    (edgeIntegral : ε → ℝ)
    (hlocal : ∀ i ∈ patches,
      orientedBoundaryValue edges (localIncidence i) edgeIntegral =
        ∫ p in parameterDomain i,
          pulledBackExteriorDerivative i p ∂(volume.prod volume))
    (hincidence : ∀ e ∈ edges,
      externalIncidence e = ∑ i ∈ patches, localIncidence i e)
    (hclosed : ∀ e ∈ edges, externalIncidence e = 0) :
    finiteAtlasSurfaceIntegral patches parameterDomain
      pulledBackExteriorDerivative = 0 := by
  have hstokes := stokes_finite_atlas_of_edge_incidence patches edges
    parameterDomain pulledBackExteriorDerivative localIncidence externalIncidence
    edgeIntegral hlocal hincidence
  have hboundary : orientedBoundaryValue edges externalIncidence edgeIntegral = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [hclosed e he]
    simp
  rw [hboundary] at hstokes
  exact hstokes.symm

end SandronesLibrary.Analysis.GreenGaussStokes
