/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.BiasVariance
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.Density
import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Tengoku.Seed.Analysis.Calculus.Deriv.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fisher 信息与 Cramér–Rao 下界

设 `ν` 是样本空间 `𝓧` 上的支配测度，`p : ℝ → 𝓧 → ℝ` 是实值密度族，
`modelMeasure ν p θ = ν.withDensity (ofReal ∘ p θ)` 是参数 `θ` 下的模型测度。若
`∫ x, p θ x ∂ν = 1` 且 `p θ ≥ 0`，则每个纤维都是概率测度。

**得分函数** `s : ℝ → 𝓧 → ℝ` 是密度对数导数 `∂_θ log p_θ` 的正式承载。本条目不通过链式法则
从 `p` 构造 `s`，而是把 `s` 作为模型的一部分显式给出，并把正则条件写成
`IsRegularDominatedFamily` 的字段：

* 密度可测、非负、可积、总积分为一；
* `∫ x, (s θ x)^2 * p θ x ∂ν` 有限（Fisher 信息有限）；
* **微分与积分可交换**：`HasDerivAt (fun θ' => ∫ x, p θ' x ∂ν) (∫ x, s θ x * p θ x ∂ν) θ`。

最后一条是本条目的关键：Cramér–Rao 下界依赖它，而它是**实质假设**，不是技术细节。
本条目不把它替换成 Mathlib 的强定理（如 `hasDerivAt_integral_of_dominated_loc_of_deriv_le`），
也不默默引用；它逐字出现在结构字段与主定理的假设里。由它立即得到**得分函数均值为零**
（`score_integral_eq_zero`）：因为 `∫ p θ` 恒等于常数一，其导数必为零。

## Fisher 信息

`fisherInformation ν p s θ = ∫ x, (s θ x)^2 * p θ x ∂ν`，即得分函数平方的模型期望。它与
模型测度形式一致（`fisherInformation_eq_integral_modelMeasure`），也就是 `E_θ[s_θ²]`。

## Cramér–Rao 下界

对统计量 `T : 𝓧 → ℝ`，记其**均值函数** `densityMean ν p T θ = ∫ x, T x * p θ x ∂ν`。
若 `T` 与 `s θ` 在模型测度下二阶可积，且均值函数满足**微分与积分可交换**

`HasDerivAt (densityMean ν p T) (∫ x, T x * s θ x * p θ x ∂ν) θ`，

则

`(deriv (densityMean ν p T) θ)^2 ≤ fisherInformation ν p s θ * variance T (modelMeasure ν p θ)`。

结论左端就是 `g'(θ)²`（`g = E_θ[T]`），交换性假设正是把 `g'(θ)` 识别为
`∫ x, T x * s θ x * p θ x ∂ν` 的那一步；证明用柯西–施瓦茨
（`sq_integral_mul_le_integral_sq_mul_integral_sq`）与得分均值为零，并把
`∫ x, (T x - E_θ T)² ∂μ` 用 `statistics.estimator.bias-variance` 的
`squaredError_integral_eq_variance_add_bias_sq` 写成 `Var_θ(T)`（偏差项为零）。
`cramerRao_variance_ge` 把它改写成教材形式 `g'(θ)² / I(θ) ≤ Var_θ(T)`（要求 `I(θ) > 0`），
`cramerRao_variance_ge_inv_of_unbiased` 是无偏情形 `Var_θ(T) ≥ 1/I(θ)`。

## 未完成边界

本条目**不从 Mathlib 的支配收敛型微分定理推导交换性**，也不证明它在具体模型（如指数族、
正态族）中成立；把课程级正则条件（支撑集不随 `θ` 变、逐点可微、被可积控制函数支配）推出交换性
的工作登记为后续桥，而不是已完成的定理。本条目也不把 `statistics.model.density` 的
`ℝ≥0∞` 值 kernel 密度自动转成实值 `p`；实值密度族是本条目的显式输入。Mathlib 的 `deriv` 在
不可微点约定取 `0`，因此主定理的结论只在交换性假设 `hswap` 成立处有意义；本条目不用 `deriv`
的隐式约定去免费获得可微性。

> **Entry**: statistics.information.cramer-rao
-/

namespace SandronesLibrary.Statistics

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- 由支配测度 `ν` 与实值密度族 `p` 生成的**模型测度族**：
`modelMeasure ν p θ = ν.withDensity (ofReal ∘ p θ)`。

这是课程中"密度 `p_θ` 相对 `ν` 定义概率律"的正式承载，直接复用 Mathlib 的
`Measure.withDensity`，不另建概率密度结构。-/
noncomputable def modelMeasure (ν : Measure 𝓧) (p : ℝ → 𝓧 → ℝ) (θ : ℝ) : Measure 𝓧 :=
  ν.withDensity fun x => ENNReal.ofReal (p θ x)

/-- 模型测度在可测集上的取值就是密度的 Lebesgue 积分。-/
theorem modelMeasure_apply (ν : Measure 𝓧) (p : ℝ → 𝓧 → ℝ) (θ : ℝ) {s : Set 𝓧}
    (hs : MeasurableSet s) :
    modelMeasure ν p θ s = ∫⁻ x in s, ENNReal.ofReal (p θ x) ∂ν :=
  withDensity_apply _ hs

/-- **正则支配模型族**：Cramér–Rao 所需的全部正则条件，逐条显式列出。

`deriv_integral_swap` 就是"微分与积分可交换"：它断言总质量积分
`θ' ↦ ∫ x, p θ' x ∂ν` 在 `θ` 处可微，且导数等于 `∫ x, s θ x * p θ x ∂ν`。这不是技术细节，
而是把 `s` 与 `p` 的变化率锁在一起、并使得分函数均值为零的实质假设。-/
structure IsRegularDominatedFamily (ν : Measure 𝓧) (p : ℝ → 𝓧 → ℝ)
    (s : ℝ → 𝓧 → ℝ) : Prop where
  /-- 每个参数处的密度可测。-/
  aemeasurable_density : ∀ θ, AEMeasurable (p θ) ν
  /-- 每个参数处的密度几乎处处非负。-/
  nonneg_density : ∀ θ, 0 ≤ᵐ[ν] p θ
  /-- 每个参数处的密度可积（矩存在性的密度侧版本）。-/
  integrable_density : ∀ θ, Integrable (p θ) ν
  /-- 密度关于支配测度的总积分为一：`p θ` 确实是概率密度。-/
  density_integral_eq_one : ∀ θ, ∫ x, p θ x ∂ν = 1
  /-- Fisher 信息有限：得分函数平方的模型期望可积。-/
  score_sq_integrable : ∀ θ, Integrable (fun x => (s θ x) ^ 2 * p θ x) ν
  /-- **微分与积分可交换**（显式正则条件）。-/
  deriv_integral_swap : ∀ θ,
    HasDerivAt (fun θ' => ∫ x, p θ' x ∂ν) (∫ x, s θ x * p θ x ∂ν) θ

/-- 归一化密度给出的模型测度是概率测度。-/
theorem isProbabilityMeasure_modelMeasure {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    {s : ℝ → 𝓧 → ℝ} (h : IsRegularDominatedFamily ν p s) (θ : ℝ) :
    IsProbabilityMeasure (modelMeasure ν p θ) := by
  rw [isProbabilityMeasure_iff, modelMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (h.integrable_density θ)
      (h.nonneg_density θ), h.density_integral_eq_one θ, ENNReal.ofReal_one]

/-- **得分函数均值为零**：微分与积分可交换的直接推论。

`θ' ↦ ∫ x, p θ' x ∂ν` 恒等于常数一，其导数为零；由 `deriv_integral_swap` 与导数唯一性，
`∫ x, s θ x * p θ x ∂ν = 0`。这是 Cramér–Rao 证明中"协方差等于 `g'(θ)`"的一半。-/
theorem score_integral_eq_zero {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {s : ℝ → 𝓧 → ℝ}
    (h : IsRegularDominatedFamily ν p s) (θ : ℝ) :
    ∫ x, s θ x * p θ x ∂ν = 0 := by
  have h₁ : HasDerivAt (fun _ : ℝ => (1 : ℝ)) (∫ x, s θ x * p θ x ∂ν) θ :=
    (h.deriv_integral_swap θ).congr_of_eventuallyEq (by
      filter_upwards with θ'
      exact (h.density_integral_eq_one θ').symm)
  exact h₁.unique (hasDerivAt_const θ 1)

/-- 关于模型测度的积分等于密度加权积分。这是 `withDensity` 与 Bochner 积分之间的桥，
把"密度的期望"与"密度的加权积分"两种写法锁在一起。-/
theorem integral_modelMeasure {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {s : ℝ → 𝓧 → ℝ}
    (h : IsRegularDominatedFamily ν p s) (θ : ℝ) (F : 𝓧 → ℝ) :
    ∫ x, F x ∂(modelMeasure ν p θ) = ∫ x, F x * p θ x ∂ν := by
  rw [modelMeasure, integral_withDensity_eq_integral_toReal_smul₀
    ((h.aemeasurable_density θ).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [h.nonneg_density θ] with x hx
  rw [smul_eq_mul, ENNReal.toReal_ofReal hx, mul_comm]

/-- **Fisher 信息**：得分函数平方的模型期望，写成密度加权积分
`∫ x, (s θ x)^2 * p θ x ∂ν`。

`ν` 只作为支配测度出现，Fisher 信息的值不依赖 `ν` 的选择（密度按 RN 导数同步改变）；
本条目不证明这条不变量性质。-/
noncomputable def fisherInformation (ν : Measure 𝓧) (p : ℝ → 𝓧 → ℝ)
    (s : ℝ → 𝓧 → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, (s θ x) ^ 2 * p θ x ∂ν

/-- Fisher 信息的模型测度形式：它就是 `E_θ[s_θ²]`。-/
theorem fisherInformation_eq_integral_modelMeasure {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    {s : ℝ → 𝓧 → ℝ} (h : IsRegularDominatedFamily ν p s) (θ : ℝ) :
    fisherInformation ν p s θ = ∫ x, (s θ x) ^ 2 ∂(modelMeasure ν p θ) := by
  rw [fisherInformation, ← integral_modelMeasure h θ fun x => (s θ x) ^ 2]

/-- 统计量 `T` 的**均值函数** `g(θ) = E_θ[T]`，写成密度加权积分。-/
noncomputable def densityMean (ν : Measure 𝓧) (p : ℝ → 𝓧 → ℝ) (T : 𝓧 → ℝ)
    (θ : ℝ) : ℝ :=
  ∫ x, T x * p θ x ∂ν

/-- 均值函数的模型测度形式。-/
theorem densityMean_eq_integral_modelMeasure {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    {s : ℝ → 𝓧 → ℝ} (h : IsRegularDominatedFamily ν p s) (T : 𝓧 → ℝ) (θ : ℝ) :
    densityMean ν p T θ = ∫ x, T x ∂(modelMeasure ν p θ) := by
  rw [densityMean, ← integral_modelMeasure h θ T]

/-- Fisher 信息非负：它是得分函数平方的模型期望。-/
theorem fisherInformation_nonneg {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {s : ℝ → 𝓧 → ℝ}
    (h : IsRegularDominatedFamily ν p s) (θ : ℝ) :
    0 ≤ fisherInformation ν p s θ := by
  rw [fisherInformation_eq_integral_modelMeasure h θ]
  exact integral_nonneg fun x => sq_nonneg _

/-- **与 `statistics.model.density` 的桥**：支配 kernel 模型的联合可测 Radon--Nikodym 密度在
几乎处处有限的点上转成实值后，正好生成同一个模型测度。

右端的实值密度族 `fun θ x => (P.rnDeriv (Kernel.const ℝ ν) θ x).toReal` 就是本条目
`p` 在 kernel 模型上的标准取值；两个 `withDensity` 只在 `ν`-零测集上不同（`ℝ≥0∞` 密度可能
取无穷的点），由 `statisticalModel_density_ne_top_ae` 排除。-/
theorem modelMeasure_kernelDensity_eq (P : Kernel ℝ 𝓧) [IsMarkovKernel P] (ν : Measure 𝓧)
    [IsFiniteMeasure ν] [MeasurableSpace.CountableOrCountablyGenerated ℝ 𝓧]
    (hPν : ∀ θ, P θ ≪ ν) (θ : ℝ) :
    modelMeasure ν (fun θ x => (P.rnDeriv (Kernel.const ℝ ν) θ x).toReal) θ = P θ := by
  rw [modelMeasure, ← statisticalModel_withDensity_eq P ν θ (hPν θ)]
  refine withDensity_congr_ae ?_
  filter_upwards [statisticalModel_density_ne_top_ae P ν θ] with x hx
  exact ENNReal.ofReal_toReal hx

/-- **概率测度上的柯西–施瓦茨不等式（积分形式）**：
`(∫ f g)² ≤ (∫ f²)(∫ g²)`。

这是 Cramér–Rao 证明的纯分析核心，用 Mathlib 的 Hölder 不等式
`integral_mul_norm_le_Lp_mul_Lq`（`p = q = 2`）证明，不经过 `Lp` 商空间。-/
theorem sq_integral_mul_le_integral_sq_mul_integral_sq {μ : Measure 𝓧} {f g : 𝓧 → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
  have h22 : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) h22 hf' hg'
  have hA : 0 ≤ ∫ x, (f x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, (g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have habs : |∫ x, f x * g x ∂μ| ≤
      (∫ x, (f x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp [abs_mul, Real.norm_eq_abs]
      _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
            (∫ x, ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hholder
      _ = (∫ x, (f x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
            (∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
          simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hsq : (∫ x, f x * g x ∂μ) ^ 2 ≤
      ((∫ x, (f x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
        (∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
    sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
  calc (∫ x, f x * g x ∂μ) ^ 2
      ≤ ((∫ x, (f x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := hsq
    _ = (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA,
          Real.sq_sqrt hB]

/-- **Cramér–Rao 下界**：均值函数可微（且微分与积分可交换）的统计量 `T`，其均值函数的导数
平方不超过 Fisher 信息与方差之积。

左端 `deriv (densityMean ν p T) θ` 就是 `g'(θ)`（`g = E_θ[T]`）。`hswap` 是**显式**的
微分与积分可交换假设，它在证明中被 `HasDerivAt.deriv` 用来把 `g'(θ)` 识别为
`∫ x, T x * s θ x * p θ x ∂ν`，随后柯西–施瓦茨与得分均值为零给出结论。-/
theorem cramerRao_lower_bound {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {s : ℝ → 𝓧 → ℝ}
    (h : IsRegularDominatedFamily ν p s) (T : 𝓧 → ℝ) (θ : ℝ)
    (hT : MemLp T 2 (modelMeasure ν p θ))
    (hs : MemLp (s θ) 2 (modelMeasure ν p θ))
    (hswap : HasDerivAt (densityMean ν p T) (∫ x, T x * s θ x * p θ x ∂ν) θ) :
    (deriv (densityMean ν p T) θ) ^ 2 ≤
      fisherInformation ν p s θ * variance T (modelMeasure ν p θ) := by
  let μ := modelMeasure ν p θ
  have hμ : IsProbabilityMeasure μ := isProbabilityMeasure_modelMeasure h θ
  have hbridge : ∫ x, T x * s θ x ∂μ = ∫ x, T x * s θ x * p θ x ∂ν :=
    integral_modelMeasure h θ fun x => T x * s θ x
  have hswapμ : HasDerivAt (densityMean ν p T) (∫ x, T x * s θ x ∂μ) θ := by
    rw [hbridge]
    exact hswap
  rw [hswapμ.deriv]
  have hscore : ∫ x, s θ x ∂μ = 0 := by
    rw [integral_modelMeasure h θ fun x => s θ x]
    exact score_integral_eq_zero h θ
  have hf : MemLp (fun x => T x - ∫ y, T y ∂μ) 2 μ := hT.sub (memLp_const _)
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hf hs
  have hleft : ∫ x, (T x - ∫ y, T y ∂μ) * s θ x ∂μ = ∫ x, T x * s θ x ∂μ := by
    have hTs : Integrable (fun x => T x * s θ x) μ := hT.integrable_mul hs
    have hms : Integrable (fun x => (∫ y, T y ∂μ) * s θ x) μ :=
      (hs.integrable (by norm_num)).const_mul _
    simp_rw [sub_mul]
    rw [integral_sub hTs hms, integral_const_mul, hscore, mul_zero, sub_zero]
  rw [hleft] at hcs
  have hvar : ∫ x, (T x - ∫ y, T y ∂μ) ^ 2 ∂μ = variance T μ := by
    rw [squaredError_integral_eq_variance_add_bias_sq μ T hT (∫ y, T y ∂μ)]
    ring
  rw [hvar, ← fisherInformation_eq_integral_modelMeasure h θ] at hcs
  exact hcs.trans_eq (mul_comm (variance T (modelMeasure ν p θ)) (fisherInformation ν p s θ))

/-- **Cramér–Rao 下界的教材形式**：Fisher 信息为正时，
`g'(θ)² / I(θ) ≤ Var_θ(T)`。-/
theorem cramerRao_variance_ge {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {s : ℝ → 𝓧 → ℝ}
    (h : IsRegularDominatedFamily ν p s) (T : 𝓧 → ℝ) (θ : ℝ)
    (hT : MemLp T 2 (modelMeasure ν p θ))
    (hs : MemLp (s θ) 2 (modelMeasure ν p θ))
    (hswap : HasDerivAt (densityMean ν p T) (∫ x, T x * s θ x * p θ x ∂ν) θ)
    (hI : 0 < fisherInformation ν p s θ) :
    (deriv (densityMean ν p T) θ) ^ 2 / fisherInformation ν p s θ ≤
      variance T (modelMeasure ν p θ) := by
  rw [div_le_iff₀ hI]
  calc (deriv (densityMean ν p T) θ) ^ 2
      ≤ fisherInformation ν p s θ * variance T (modelMeasure ν p θ) :=
        cramerRao_lower_bound h T θ hT hs hswap
    _ = variance T (modelMeasure ν p θ) * fisherInformation ν p s θ := mul_comm _ _

/-- **无偏估计量的 Cramér–Rao 下界**：均值函数就是参数本身（`E_θ[T] = θ`，即 `T` 无偏估计
恒等参数）时，`Var_θ(T) ≥ 1 / I(θ)`。

这是主定理在 `g = id` 时的直接推论：`g'(θ) = 1`。-/
theorem cramerRao_variance_ge_inv_of_unbiased {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ}
    {s : ℝ → 𝓧 → ℝ} (h : IsRegularDominatedFamily ν p s) (T : 𝓧 → ℝ) (θ : ℝ)
    (hT : MemLp T 2 (modelMeasure ν p θ))
    (hs : MemLp (s θ) 2 (modelMeasure ν p θ))
    (hswap : HasDerivAt (densityMean ν p T) (∫ x, T x * s θ x * p θ x ∂ν) θ)
    (hunbiased : densityMean ν p T = fun θ' => θ')
    (hI : 0 < fisherInformation ν p s θ) :
    1 / fisherInformation ν p s θ ≤ variance T (modelMeasure ν p θ) := by
  have hd : deriv (densityMean ν p T) θ = 1 := by
    rw [hunbiased]
    simp
  have hmain := cramerRao_variance_ge h T θ hT hs hswap hI
  rwa [hd, one_pow] at hmain

end SandronesLibrary.Statistics
