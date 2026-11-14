/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.TensorExterior
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.NormedAlternating
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Orientation
import Tengoku.Seed.Analysis.Calculus.DifferentialForm.Basic
import Tengoku.Seed.Analysis.Normed.Operator.Bilinear
import Tengoku.Seed.LinearAlgebra.Alternating.DomCoprod
import Tengoku.Seed.LinearAlgebra.TensorProduct.Associator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 欧氏空间上的微分形式

本模块把 mathlib 的连续交替映射与外微分核心包装成经典微分几何的教材接口。
在赋范实向量空间 `E` 上，`k` 次微分形式是在每一点 `x` 选取一个连续交替
`k` 重线性泛函的场：

`ω : E → E [⋀^Fin k]→L[ℝ] ℝ`。

第一批结果包括函数作为零次形式、沿光滑映射拉回、外微分的线性、零次形式的
外微分、恒等式 `d²=0`，以及外微分与拉回交换。这些是后续闭形式、恰当形式、
曲线曲面积分和一般 Stokes 定理的共同前置。

> **Entry**: analysis.multivariable.differential-forms
-/

noncomputable section

namespace SandronesLibrary.Analysis.DifferentialForms

open Set ContinuousAlternatingMap
open SandronesLibrary.Analysis.NormedAlternating
open scoped _root_.Topology

universe u v

/-! ## 定向与坐标变换 -/

/-- 微分形式积分所使用的环境空间定向，直接调用拓扑层的线性定向。-/
abbrev FormOrientation (E : Type u) [AddCommGroup E] [Module ℝ E] (n : ℕ) :=
  SandronesLibrary.Topology.Orientation.VectorOrientation E n

/-- 一个线性重参数化相对于环境定向是正向的。-/
abbrev IsPositiveLinearReparametrization
    {E : Type u} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (o : FormOrientation E n) (f : E ≃ₗ[ℝ] E) : Prop :=
  SandronesLibrary.Topology.Orientation.IsOrientationPreserving o f

/-- 正向线性重参数化的实用判据是雅可比行列式为正。-/
theorem isPositiveLinearReparametrization_iff_det_pos
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (o : FormOrientation E n)
    (f : E ≃ₗ[ℝ] E) (hdim : n = Module.finrank ℝ E) :
    IsPositiveLinearReparametrization o f ↔
      0 < LinearMap.det (f : E →ₗ[ℝ] E) := by
  exact SandronesLibrary.Topology.Orientation.isOrientationPreserving_iff_det_pos
    o f hdim

/-- 赋范空间 `E` 上的光滑性尚未打包的 `k` 次微分形式。-/
abbrev DifferentialForm (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :=
  E → E [⋀^Fin k]→L[ℝ] ℝ

/-- 微分形式在点和切向量组上的取值。-/
def formValue {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (ω : DifferentialForm E k) (x : E) (v : Fin k → E) : ℝ := ω x v

/-- 实函数看成零次微分形式。-/
def functionAsZeroForm {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) : DifferentialForm E 0 :=
  fun x ↦ constOfIsEmpty ℝ E (Fin 0) (f x)

/-- 沿映射 `f : E → F` 拉回 `F` 上的微分形式。-/
def formPullback {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (f : E → F) (ω : DifferentialForm F k) : DifferentialForm E k :=
  fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

/-- 微分形式的外微分。-/
def exteriorDerivative {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (ω : DifferentialForm E k) : DifferentialForm E (k + 1) := extDeriv ω

theorem exteriorDerivative_add {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {ω η : DifferentialForm E k} {x : E}
    (hω : DifferentiableAt ℝ ω x) (hη : DifferentiableAt ℝ η x) :
    exteriorDerivative (ω + η) x = exteriorDerivative ω x + exteriorDerivative η x := by
  exact extDeriv_add hω hη

theorem exteriorDerivative_smul {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (c : ℝ) (ω : DifferentialForm E k) (x : E) :
    exteriorDerivative (c • ω) x = c • exteriorDerivative ω x := by
  exact extDeriv_smul c ω

theorem exteriorDerivative_zeroForm {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) :
    exteriorDerivative (functionAsZeroForm f) x =
      .ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ f x) := by
  exact extDeriv_constOfIsEmpty f x

theorem exteriorDerivative_squared_zero {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {r : WithTop ℕ∞}
    (ω : DifferentialForm E k) (hω : ContDiff ℝ r ω)
    (hr : minSmoothness ℝ 2 ≤ r) :
    exteriorDerivative (exteriorDerivative ω) = 0 := by
  exact extDeriv_extDeriv hω hr

theorem exteriorDerivative_pullback {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {r : WithTop ℕ∞} (f : E → F) (ω : DifferentialForm F k) (x : E)
    (hω : DifferentiableAt ℝ ω (f x)) (hf : ContDiffAt ℝ r f x)
    (hr : minSmoothness ℝ 2 ≤ r) :
    exteriorDerivative (formPullback f ω) x =
      formPullback f (exteriorDerivative ω) x := by
  exact extDeriv_pullback hω hf hr

/-! ## 闭形式与恰当形式 -/

/-- 闭形式：外微分为零。-/
def IsClosedForm {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (ω : DifferentialForm E k) : Prop := exteriorDerivative ω = 0

/-- 恰当形式：它是一个充分光滑的低一次形式的外微分。光滑势形式作为 witness
保存在定义中，使“恰当必闭”能够直接应用 `d²=0`。-/
def IsExactForm {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (ω : DifferentialForm E (k + 1)) : Prop :=
  ∃ η : DifferentialForm E k, ContDiff ℝ ⊤ η ∧ exteriorDerivative η = ω

/-- 每个恰当形式都是闭形式，这是恒等式 `d²=0` 的直接推论。-/
theorem exactForm_isClosed {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {ω : DifferentialForm E (k + 1)} (hω : IsExactForm ω) : IsClosedForm ω := by
  obtain ⟨η, hηsmooth, rfl⟩ := hω
  exact exteriorDerivative_squared_zero η hηsmooth (by simp)

/-- 闭形式沿充分光滑映射拉回后仍然是闭形式。-/
theorem closedForm_pullback {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {r : WithTop ℕ∞} (f : E → F) (ω : DifferentialForm F k)
    (hωsmooth : ContDiff ℝ r ω) (hf : ContDiff ℝ r f)
    (hr : minSmoothness ℝ 2 ≤ r) (hωclosed : IsClosedForm ω) :
    IsClosedForm (formPullback f ω) := by
  rw [IsClosedForm] at hωclosed ⊢
  funext x
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    simp at hr
  rw [exteriorDerivative_pullback f ω x
    (hωsmooth.differentiable hr0 (f x)) hf.contDiffAt hr]
  simp only [formPullback]
  rw [congrFun hωclosed (f x)]
  ext v
  simp

/-- 外微分的教材交替和公式：依次删去第 `i` 个方向，把其余方向代入原形式，
再沿被删去的方向求导，并按 `(-1)^i` 求和。-/
theorem exteriorDerivative_apply {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {ω : DifferentialForm E k} {x : E} (hω : DifferentiableAt ℝ ω x)
    (v : Fin (k + 1) → E) :
    exteriorDerivative ω x v =
      ∑ i, (-1) ^ i.val • fderiv ℝ (ω · (i.removeNth v)) x (v i) := by
  exact extDeriv_apply hω v

/-! ## 楔积的代数基础

连续交替映射的楔积需要额外证明：有限个 shuffle 项组成的交替映射仍然连续。
在完成这个分析步骤以前，本节先把不会丢失信息的代数核心单独封装。具体而言，
`forgetFormContinuity` 只忘掉每个纤维映射的连续性证明，而
`alternatingWedge` 按教材中的 shuffle 公式构造两个交替映射的楔积。

mathlib 的 `AlternatingMap.domCoprod` 先让值落在 `ℝ ⊗[ℝ] ℝ`；随后用
`TensorProduct.lid` 做标量乘法，并用 `finSumFinEquiv` 把指标
`Fin k ⊕ Fin l` 重新编号为 `Fin (k+l)`。 -/

open scoped TensorProduct

/-- `k` 次代数微分形式：每一点取一个交替 `k` 重线性泛函，但暂不携带连续性。-/
abbrev AlgebraicDifferentialForm (E : Type u) [AddCommGroup E] [Module ℝ E] (k : ℕ) :=
  E → E [⋀^Fin k]→ₗ[ℝ] ℝ

/-- 忘掉连续微分形式每个纤维上的连续性证明，得到代数微分形式。-/
def forgetFormContinuity {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (ω : DifferentialForm E k) : AlgebraicDifferentialForm E k :=
  fun x ↦ (ω x).toAlternatingMap

/-- 两个交替多重线性泛函的楔积。其定义等价于对所有 `(k,l)`-shuffle
按置换符号求和，并把两个泛函值相乘。-/
def alternatingWedge {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→ₗ[ℝ] ℝ) (b : E [⋀^Fin l]→ₗ[ℝ] ℝ) :
    E [⋀^Fin (k + l)]→ₗ[ℝ] ℝ :=
  (TensorProduct.lid ℝ ℝ).toLinearMap.compAlternatingMap
    ((a.domCoprod b).domDomCongr finSumFinEquiv)

/-- 逐点取楔积，得到次数为 `k+l` 的代数微分形式。-/
def algebraicFormWedge {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (ω : AlgebraicDifferentialForm E k) (η : AlgebraicDifferentialForm E l) :
    AlgebraicDifferentialForm E (k + l) :=
  fun x ↦ alternatingWedge (ω x) (η x)

/-- 楔积对左变量可加。证明使用 `domCoprod'` 的张量积线性化接口。-/
theorem alternatingWedge_add_left {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (a₁ a₂ : E [⋀^Fin k]→ₗ[ℝ] ℝ) (b : E [⋀^Fin l]→ₗ[ℝ] ℝ) :
    alternatingWedge (a₁ + a₂) b = alternatingWedge a₁ b + alternatingWedge a₂ b := by
  have h : (a₁ + a₂).domCoprod b = a₁.domCoprod b + a₂.domCoprod b := by
    rw [← AlternatingMap.domCoprod'_apply, TensorProduct.add_tmul, map_add]
    rfl
  simp [alternatingWedge, h]

/-- 楔积对右变量可加。-/
theorem alternatingWedge_add_right {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→ₗ[ℝ] ℝ) (b₁ b₂ : E [⋀^Fin l]→ₗ[ℝ] ℝ) :
    alternatingWedge a (b₁ + b₂) = alternatingWedge a b₁ + alternatingWedge a b₂ := by
  have h : a.domCoprod (b₁ + b₂) = a.domCoprod b₁ + a.domCoprod b₂ := by
    rw [← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_add, map_add]
    rfl
  simp [alternatingWedge, h]

/-- 零交替映射从左侧作楔积仍为零。-/
theorem alternatingWedge_zero_left {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (b : E [⋀^Fin l]→ₗ[ℝ] ℝ) : alternatingWedge (0 : E [⋀^Fin k]→ₗ[ℝ] ℝ) b = 0 := by
  have h : (0 : E [⋀^Fin k]→ₗ[ℝ] ℝ).domCoprod b = 0 := by
    rw [← AlternatingMap.domCoprod'_apply, TensorProduct.zero_tmul, _root_.map_zero]
  simp [alternatingWedge, h]

/-- 零交替映射从右侧作楔积仍为零。-/
theorem alternatingWedge_zero_right {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→ₗ[ℝ] ℝ) : alternatingWedge a (0 : E [⋀^Fin l]→ₗ[ℝ] ℝ) = 0 := by
  have h : a.domCoprod (0 : E [⋀^Fin l]→ₗ[ℝ] ℝ) = 0 := by
    rw [← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_zero, _root_.map_zero]
  simp [alternatingWedge, h]

/-- 代数微分形式的楔积对左变量可加。-/
theorem algebraicFormWedge_add_left {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (ω₁ ω₂ : AlgebraicDifferentialForm E k) (η : AlgebraicDifferentialForm E l) :
    algebraicFormWedge (ω₁ + ω₂) η =
      algebraicFormWedge ω₁ η + algebraicFormWedge ω₂ η := by
  funext x
  exact alternatingWedge_add_left (ω₁ x) (ω₂ x) (η x)

/-- 代数微分形式的楔积对右变量可加。-/
theorem algebraicFormWedge_add_right {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (ω : AlgebraicDifferentialForm E k) (η₁ η₂ : AlgebraicDifferentialForm E l) :
    algebraicFormWedge ω (η₁ + η₂) =
      algebraicFormWedge ω η₁ + algebraicFormWedge ω η₂ := by
  funext x
  exact alternatingWedge_add_right (ω x) (η₁ x) (η₂ x)

/-- 零代数微分形式从左侧作楔积仍为零。-/
theorem algebraicFormWedge_zero_left {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (η : AlgebraicDifferentialForm E l) :
    algebraicFormWedge (0 : AlgebraicDifferentialForm E k) η = 0 := by
  funext x
  exact alternatingWedge_zero_left (η x)

/-- 零代数微分形式从右侧作楔积仍为零。-/
theorem algebraicFormWedge_zero_right {E : Type u} [AddCommGroup E] [Module ℝ E] {k l : ℕ}
    (ω : AlgebraicDifferentialForm E k) :
    algebraicFormWedge ω (0 : AlgebraicDifferentialForm E l) = 0 := by
  funext x
  exact alternatingWedge_zero_right (ω x)

/-! ## 连续楔积

代数楔积是有限个 shuffle 项的和。下面先逐项使用两个连续交替映射的算子范数界，
再用三角不等式对所有 shuffle 求和，从而得到 `mkContinuous` 所需的统一乘积界。 -/

/-- `(k,l)`-shuffle 商类的数目，作为楔积范数估计中的显式常数。-/
def shuffleCount (k l : ℕ) : ℝ :=
  Fintype.card (Equiv.Perm.ModSumCongr (Fin k) (Fin l))

/-- 每个带符号 shuffle 项都满足由两个因子算子范数给出的乘积界。置换符号只可能
为 `1` 或 `-1`，所以不改变范数；置换也不改变全部输入范数的乘积。-/
theorem alternatingWedge_summand_bound {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ)
    (σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l)) (w : Fin k ⊕ Fin l → E) :
    ‖(TensorProduct.lid ℝ ℝ)
        (AlternatingMap.domCoprod.summand a.toAlternatingMap b.toAlternatingMap σ w)‖ ≤
      (‖a‖ * ‖b‖) * ∏ i, ‖w i‖ := by
  induction σ using Quotient.inductionOn' with
  | h σ =>
      rw [AlternatingMap.domCoprod.summand_mk'']
      rw [_root_.smul_apply]
      rw [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply]
      have hmain :
          ‖(a.toMultilinearMap (fun i ↦ w (σ (Sum.inl i)))) •
              b.toMultilinearMap (fun i ↦ w (σ (Sum.inr i)))‖ ≤
            (‖a‖ * ‖b‖) * ∏ i, ‖w i‖ := by
        have ha := a.le_opNorm (fun i ↦ w (σ (Sum.inl i)))
        have hb := b.le_opNorm (fun i ↦ w (σ (Sum.inr i)))
        have hpσ : ∏ i, ‖w (σ i)‖ = ∏ i, ‖w i‖ :=
          Equiv.prod_comp σ (fun i ↦ ‖w i‖)
        have hsplit := Fintype.prod_sum_type (fun i : Fin k ⊕ Fin l ↦ ‖w (σ i)‖)
        have hprod :
            (∏ i, ‖w (σ (Sum.inl i))‖) * (∏ i, ‖w (σ (Sum.inr i))‖) =
              ∏ i, ‖w i‖ := hsplit.symm.trans hpσ
        calc
          ‖(a (fun i ↦ w (σ (Sum.inl i)))) •
              b (fun i ↦ w (σ (Sum.inr i)))‖ =
              ‖a (fun i ↦ w (σ (Sum.inl i)))‖ *
                ‖b (fun i ↦ w (σ (Sum.inr i)))‖ := norm_smul _ _
          _ ≤ (‖a‖ * ∏ i, ‖w (σ (Sum.inl i))‖) *
                (‖b‖ * ∏ i, ‖w (σ (Sum.inr i))‖) := by
              exact mul_le_mul ha hb (norm_nonneg _) (by positivity)
          _ = (‖a‖ * ‖b‖) *
                ((∏ i, ‖w (σ (Sum.inl i))‖) *
                  ∏ i, ‖w (σ (Sum.inr i))‖) := by ring
          _ = (‖a‖ * ‖b‖) * ∏ i, ‖w i‖ := by rw [hprod]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · simpa only [hs, one_smul, TensorProduct.lid_tmul] using hmain
      · rw [hs, Units.smul_def]
        change ‖(TensorProduct.lid ℝ ℝ) ((-1 : ℤ) • (_ ⊗ₜ[ℝ] _))‖ ≤ _
        simpa only [neg_one_zsmul, map_neg, TensorProduct.lid_tmul, norm_neg] using hmain

/-- 整个 shuffle 和的范数界。常数取 shuffle 的数目乘两个因子的算子范数。-/
theorem alternatingWedge_bound {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ)
    (v : Fin (k + l) → E) :
    ‖alternatingWedge a.toAlternatingMap b.toAlternatingMap v‖ ≤
      (shuffleCount k l * ‖a‖ * ‖b‖) * ∏ i, ‖v i‖ := by
  rw [alternatingWedge, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domDomCongr_apply, AlternatingMap.domCoprod_apply]
  calc
    ‖(TensorProduct.lid ℝ ℝ)
        ((∑ σ, AlternatingMap.domCoprod.summand a.toAlternatingMap
          b.toAlternatingMap σ) (v ∘ finSumFinEquiv))‖
        ≤ ∑ σ, ‖(TensorProduct.lid ℝ ℝ)
            (AlternatingMap.domCoprod.summand a.toAlternatingMap
              b.toAlternatingMap σ (v ∘ finSumFinEquiv))‖ := by
          rw [_root_.sum_apply, _root_.map_sum]
          exact norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l),
          (‖a‖ * ‖b‖) * ∏ i, ‖(v ∘ finSumFinEquiv) i‖ := by
          exact Finset.sum_le_sum fun σ _ ↦ alternatingWedge_summand_bound a b σ _
    _ = (shuffleCount k l * ‖a‖ * ‖b‖) * ∏ i, ‖v i‖ := by
          have hp := Fin.prod_univ_add (fun i : Fin (k + l) ↦ ‖v i‖)
          simp only [Function.comp_apply, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, shuffleCount]
          rw [Fintype.prod_sum_type]
          simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
          rw [hp]
          ring

/-- 两个连续交替映射的连续楔积。-/
def continuousAlternatingWedge {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ) :
    E [⋀^Fin (k + l)]→L[ℝ] ℝ :=
  (alternatingWedge a.toAlternatingMap b.toAlternatingMap).mkContinuous
    (shuffleCount k l * ‖a‖ * ‖b‖) (alternatingWedge_bound a b)

/-- 两个微分形式逐点作楔积。-/
def formWedge {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (ω : DifferentialForm E k) (η : DifferentialForm E l) : DifferentialForm E (k + l) :=
  fun x ↦ continuousAlternatingWedge (ω x) (η x)

/-- 连续楔积的取值就是底层代数楔积的取值。-/
theorem continuousAlternatingWedge_apply {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ) (v : Fin (k + l) → E) :
    continuousAlternatingWedge a b v =
      alternatingWedge a.toAlternatingMap b.toAlternatingMap v := by
  rfl

/-- 微分形式楔积的点态计算公式。-/
theorem formWedge_apply {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (ω : DifferentialForm E k) (η : DifferentialForm E l)
    (x : E) (v : Fin (k + l) → E) :
    formWedge ω η x v =
      alternatingWedge (ω x).toAlternatingMap (η x).toAlternatingMap v := by
  rfl

/-! ## 楔积的双线性 -/

/-- 连续楔积对左变量可加。-/
theorem continuousAlternatingWedge_add_left {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (a₁ a₂ : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ) :
    continuousAlternatingWedge (a₁ + a₂) b =
      continuousAlternatingWedge a₁ b + continuousAlternatingWedge a₂ b := by
  ext v
  exact DFunLike.congr_fun (alternatingWedge_add_left
    a₁.toAlternatingMap a₂.toAlternatingMap b.toAlternatingMap) v

/-- 连续楔积对右变量可加。-/
theorem continuousAlternatingWedge_add_right {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (b₁ b₂ : E [⋀^Fin l]→L[ℝ] ℝ) :
    continuousAlternatingWedge a (b₁ + b₂) =
      continuousAlternatingWedge a b₁ + continuousAlternatingWedge a b₂ := by
  ext v
  exact DFunLike.congr_fun (alternatingWedge_add_right
    a.toAlternatingMap b₁.toAlternatingMap b₂.toAlternatingMap) v

/-- 零连续交替映射从左侧作楔积仍为零。-/
theorem continuousAlternatingWedge_zero_left {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (b : E [⋀^Fin l]→L[ℝ] ℝ) :
    continuousAlternatingWedge (0 : E [⋀^Fin k]→L[ℝ] ℝ) b = 0 := by
  ext v
  exact DFunLike.congr_fun (alternatingWedge_zero_left b.toAlternatingMap) v

/-- 零连续交替映射从右侧作楔积仍为零。-/
theorem continuousAlternatingWedge_zero_right {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→L[ℝ] ℝ) :
    continuousAlternatingWedge a (0 : E [⋀^Fin l]→L[ℝ] ℝ) = 0 := by
  ext v
  exact DFunLike.congr_fun (alternatingWedge_zero_right a.toAlternatingMap) v

/-- 微分形式楔积对左变量可加。-/
theorem formWedge_add_left {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (ω₁ ω₂ : DifferentialForm E k) (η : DifferentialForm E l) :
    formWedge (ω₁ + ω₂) η = formWedge ω₁ η + formWedge ω₂ η := by
  funext x
  exact continuousAlternatingWedge_add_left (ω₁ x) (ω₂ x) (η x)

/-- 微分形式楔积对右变量可加。-/
theorem formWedge_add_right {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (ω : DifferentialForm E k) (η₁ η₂ : DifferentialForm E l) :
    formWedge ω (η₁ + η₂) = formWedge ω η₁ + formWedge ω η₂ := by
  funext x
  exact continuousAlternatingWedge_add_right (ω x) (η₁ x) (η₂ x)

/-- 零微分形式从左侧作楔积仍为零。-/
theorem formWedge_zero_left {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (η : DifferentialForm E l) :
    formWedge (0 : DifferentialForm E k) η = 0 := by
  funext x
  exact continuousAlternatingWedge_zero_left (η x)

/-- 零微分形式从右侧作楔积仍为零。-/
theorem formWedge_zero_right {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (ω : DifferentialForm E k) :
    formWedge ω (0 : DifferentialForm E l) = 0 := by
  funext x
  exact continuousAlternatingWedge_zero_right (ω x)

/-! ## 交替映射与形式的次数重编号 -/

/-- 沿有限指标等价重编号后，连续交替映射仍满足原算子范数给出的乘积界。-/
theorem alternatingReindex_bound {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {ι' : Type w} [Fintype ι] [Fintype ι']
    (σ : ι ≃ ι') (a : E [⋀^ι]→L[ℝ] ℝ) (x : ι' → E) :
    ‖a.toAlternatingMap.domDomCongr σ x‖ ≤ ‖a‖ * ∏ i, ‖x i‖ := by
  calc
    ‖a.toAlternatingMap.domDomCongr σ x‖ = ‖a (x ∘ σ)‖ := by
      rw [AlternatingMap.domDomCongr_apply]
      rfl
    _ ≤ ‖a‖ * ∏ i, ‖(x ∘ σ) i‖ := a.le_opNorm _
    _ = ‖a‖ * ∏ i, ‖x i‖ := by
      simp only [Function.comp_apply]
      exact congrArg (fun z : ℝ ↦ ‖a‖ * z) (Equiv.prod_comp σ (fun i ↦ ‖x i‖))

/-- 沿有限指标等价重编号连续交替映射。-/
def continuousAlternatingReindex {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {ι' : Type w} [Fintype ι] [Fintype ι']
    (σ : ι ≃ ι') (a : E [⋀^ι]→L[ℝ] ℝ) : E [⋀^ι']→L[ℝ] ℝ :=
  (a.toAlternatingMap.domDomCongr σ).mkContinuous ‖a‖ (alternatingReindex_bound σ a)

/-- 重编号后的连续交替映射按指标等价预合成输入。-/
theorem continuousAlternatingReindex_apply {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {ι' : Type w} [Fintype ι] [Fintype ι']
    (σ : ι ≃ ι') (a : E [⋀^ι]→L[ℝ] ℝ) (x : ι' → E) :
    continuousAlternatingReindex σ a x = a (x ∘ σ) := by
  rfl

/-- 用次数等式重编号微分形式。这用于统一结合方式不同但总次数相同的楔积。-/
def reindexForm {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (h : m = n) (ω : DifferentialForm E m) : DifferentialForm E n :=
  fun x ↦ continuousAlternatingReindex (finCongr h) (ω x)

/-- 次数重编号形式的点态计算公式。-/
theorem reindexForm_apply {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (h : m = n) (ω : DifferentialForm E m) (x : E) (v : Fin n → E) :
    reindexForm h ω x v = ω x (v ∘ finCongr h) := by
  rfl

/-! ## 楔积的连续双线性算子 -/

/-- 代数楔积与左侧实数数乘交换。-/
theorem alternatingWedge_smul_left {E : Type u} [AddCommGroup E] [Module ℝ E]
    {k l : ℕ} (c : ℝ) (a : E [⋀^Fin k]→ₗ[ℝ] ℝ) (b : E [⋀^Fin l]→ₗ[ℝ] ℝ) :
    alternatingWedge (c • a) b = c • alternatingWedge a b := by
  have h : (c • a).domCoprod b = c • a.domCoprod b := by
    rw [← AlternatingMap.domCoprod'_apply, ← TensorProduct.smul_tmul', map_smul]
    rfl
  simp [alternatingWedge, h]

/-- 代数楔积与右侧实数数乘交换。-/
theorem alternatingWedge_smul_right {E : Type u} [AddCommGroup E] [Module ℝ E]
    {k l : ℕ} (c : ℝ) (a : E [⋀^Fin k]→ₗ[ℝ] ℝ) (b : E [⋀^Fin l]→ₗ[ℝ] ℝ) :
    alternatingWedge a (c • b) = c • alternatingWedge a b := by
  have h : a.domCoprod (c • b) = c • a.domCoprod b := by
    rw [← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_smul, map_smul]
    rfl
  simp [alternatingWedge, h]

/-- 连续楔积与左侧实数数乘交换。-/
theorem continuousAlternatingWedge_smul_left {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (c : ℝ) (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ) :
    continuousAlternatingWedge (c • a) b = c • continuousAlternatingWedge a b := by
  ext v
  exact DFunLike.congr_fun
    (alternatingWedge_smul_left c a.toAlternatingMap b.toAlternatingMap) v

/-- 连续楔积与右侧实数数乘交换。-/
theorem continuousAlternatingWedge_smul_right {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (c : ℝ) (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ) :
    continuousAlternatingWedge a (c • b) = c • continuousAlternatingWedge a b := by
  ext v
  exact DFunLike.congr_fun
    (alternatingWedge_smul_right c a.toAlternatingMap b.toAlternatingMap) v

/-- 楔积作为两个连续交替映射空间之间的双线性映射。-/
def wedgeLinearMap {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (k l : ℕ) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ]
      (E [⋀^Fin l]→L[ℝ] ℝ) →ₗ[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] ℝ) :=
  LinearMap.mk₂ ℝ continuousAlternatingWedge
    continuousAlternatingWedge_add_left continuousAlternatingWedge_smul_left
    continuousAlternatingWedge_add_right continuousAlternatingWedge_smul_right

/-- 连续楔积的算子范数由 shuffle 数目乘两个因子范数控制。-/
theorem continuousAlternatingWedge_norm_le {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ) :
    ‖continuousAlternatingWedge a b‖ ≤ shuffleCount k l * ‖a‖ * ‖b‖ := by
  unfold continuousAlternatingWedge
  apply AlternatingMap.mkContinuous_norm_le
  unfold shuffleCount
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _)

/-- 楔积打包成连续双线性算子。这个接口使形式场的楔积可以直接使用
连续线性映射求值的 Fréchet 乘积法则。-/
def wedgeContinuousBilinear {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k l : ℕ) :
    (E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
      (E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin (k + l)]→L[ℝ] ℝ) :=
  (wedgeLinearMap k l).mkContinuous₂ (shuffleCount k l) <| by
    intro a b
    change ‖continuousAlternatingWedge a b‖ ≤ shuffleCount k l * ‖a‖ * ‖b‖
    exact continuousAlternatingWedge_norm_le a b

/-- 连续双线性算子的求值就是此前定义的连续楔积。-/
theorem wedgeContinuousBilinear_apply {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    (a : E [⋀^Fin k]→L[ℝ] ℝ) (b : E [⋀^Fin l]→L[ℝ] ℝ) :
    wedgeContinuousBilinear k l a b = continuousAlternatingWedge a b := by
  rfl

/-! ## 规范范数模型上的楔积求导

为避免 mathlib 的连续交替映射半范数实例与范数实例在高阶连续线性映射中发生
实例选择冲突，求导过程先进入 `NormalizedAlternatingSpace`，完成连续双线性
乘积的求导后再回到原形式空间。底层函数始终是同一个楔积。 -/

/-- 形式场进入规范交替映射空间后保持点可微性。-/
theorem normalizedAlternatingSpace_differentiableAt {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {ω : DifferentialForm E k} {x : E} (hω : DifferentiableAt ℝ ω x) :
    DifferentiableAt ℝ (fun y ↦ toNormalizedAlternatingSpace k (ω y)) x := by
  exact (toNormalizedAlternatingSpace k).differentiableAt.comp x hω

/-- 规范交替映射空间上的楔积双线性映射。-/
def normalizedWedgeLinearMap {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k l : ℕ) :
    NormalizedAlternatingSpace E k →ₗ[ℝ]
      NormalizedAlternatingSpace E l →ₗ[ℝ] NormalizedAlternatingSpace E (k + l) :=
  LinearMap.mk₂ ℝ continuousAlternatingWedge
    continuousAlternatingWedge_add_left continuousAlternatingWedge_smul_left
    continuousAlternatingWedge_add_right continuousAlternatingWedge_smul_right

/-- 规范交替映射空间上的连续双线性楔积。-/
def normalizedWedgeContinuousBilinear {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k l : ℕ) :
    NormalizedAlternatingSpace E k →L[ℝ]
      NormalizedAlternatingSpace E l →L[ℝ] NormalizedAlternatingSpace E (k + l) :=
  (normalizedWedgeLinearMap k l).mkContinuous₂ (shuffleCount k l) <| by
    intro a b
    change ‖continuousAlternatingWedge a b‖ ≤ shuffleCount k l * ‖a‖ * ‖b‖
    exact continuousAlternatingWedge_norm_le a b

/-- 两个点可微形式的楔积仍然点可微。证明在规范范数模型中应用连续双线性
映射的 Fréchet 乘积法则，再通过恒等连续线性桥返回原形式空间。-/
theorem differentiableAt_formWedge {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {k l : ℕ}
    {ω : DifferentialForm E k} {η : DifferentialForm E l} {x : E}
    (hω : DifferentiableAt ℝ ω x) (hη : DifferentiableAt ℝ η x) :
    DifferentiableAt ℝ (formWedge ω η) x := by
  have hωN := normalizedAlternatingSpace_differentiableAt (k := k) hω
  have hηN := normalizedAlternatingSpace_differentiableAt (k := l) hη
  have hc : DifferentiableAt ℝ
      (fun y ↦ normalizedWedgeContinuousBilinear k l
        (toNormalizedAlternatingSpace k (ω y))) x :=
    (normalizedWedgeContinuousBilinear k l).differentiableAt.comp x hωN
  have hprod : DifferentiableAt ℝ
      (fun y ↦ normalizedWedgeContinuousBilinear k l
        (toNormalizedAlternatingSpace k (ω y))
        (toNormalizedAlternatingSpace l (η y))) x :=
    hc.clm_apply hηN
  have hout := (fromNormalizedAlternatingSpace (k + l)).differentiableAt.comp x hprod
  exact hout

end SandronesLibrary.Analysis.DifferentialForms
