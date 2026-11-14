/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.Model
import Tengoku.Seed.Probability.Decision.BayesEstimator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 统计量、估计量与风险

统计量是样本的可测函数。当它的值被解释为未知量的估计时，同一个可测函数就是确定性估计量。
更一般地，随机化估计量在观察到数据 `x` 后给出估计值的一个条件分布，因此正式承载是
`κ : Kernel 𝓧 𝓨` 与 `[IsMarkovKernel κ]`。后一个条件不可省略：普通 kernel 的纤维不一定具有总
质量一。

可测函数 `T : 𝓧 → 𝓨` 通过 `Kernel.deterministic T hT` 进入统一的随机化接口。与统计模型
`P : Kernel Θ 𝓧` 复合后，`(κ ∘ₖ P) θ` 是真实参数为 `θ` 时估计输出的分布；确定性情形正好是
数据分布的推前 `P.map T`。

损失函数取 `ℓ : Θ → 𝓨 → ℝ≥0∞`。扩展非负实数允许风险为无穷，不需要在定义阶段预设可积性；
联合可测性 `Measurable (Function.uncurry ℓ)` 保证每个固定参数的损失截面可测。逐参数风险直接写成

`∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)`，

不另造与 Mathlib 同义的定义。`avgRisk` 再关于先验平均，`bayesRisk` 是所有 Markov 估计量平均
风险的下确界。下确界不保证一定被某个估计量达到；`IsBayesEstimator` 只刻画达到时的性质。

本文件严格止于定义展开和确定性桥，不包含偏差—方差分解、MLE、Fisher 信息、充分性或一般最优
估计量存在性。

> **Entry**: statistics.estimator.definition
-/

namespace SandronesLibrary.Statistics

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

/-- 可测的确定性估计量经 Dirac kernel 构造后是合法的 Markov 估计量。
@isnad1 id=ismarkov.1h3v.s5.c03fbe687019 from=translated src=- shape=8a284326 vocab=c75b26d4
-/
theorem deterministicEstimator_isMarkov
    {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (T : 𝓧 → 𝓨) (hT : Measurable T) :
    IsMarkovKernel (Kernel.deterministic T hT) := by
  infer_instance

/-- 统计模型与随机化估计量复合后，所得输出分布族仍是 Markov kernel。
@isnad1 id=ismarkov.0h5v.s5.180f18d199eb from=translated src=- shape=af103cbc vocab=44c67a87
-/
theorem estimatorOutput_isMarkov
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    IsMarkovKernel (κ ∘ₖ P) := by
  infer_instance

/-- 确定性估计量的输出分布就是原数据分布沿该估计量的推前。
@isnad1 id=eq.1h5v.s6.97eaac986c12 from=translated src=- shape=7a390530 vocab=588fd18e
-/
theorem deterministicEstimator_outputDistribution
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (T : 𝓧 → 𝓨) (hT : Measurable T) :
    Kernel.deterministic T hT ∘ₖ P = P.map T := by
  exact Kernel.deterministic_comp_eq_map hT P

/-- 损失函数的联合可测性蕴含每个固定参数截面的可测性。
@isnad1 id=measurab.1h4v.s5.19900cd5756a from=translated src=- shape=1e8ee8dc vocab=131f853a
-/
theorem measurable_loss_section
    {Θ 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓨]
    {ℓ : Θ → 𝓨 → ℝ≥0∞} (hℓ : Measurable (Function.uncurry ℓ)) (θ : Θ) :
    Measurable (ℓ θ) := by
  fun_prop

/-- 平均风险展开为逐参数风险关于先验的积分。内层积分就是本库采用的逐参数风险表达式。
@isnad1 id=eq.0h7v.s6.ce4a525714ec from=translated src=- shape=43309474 vocab=e60dd66f
-/
theorem avgRisk_eq_lintegral_pointwiseRisk
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (π : Measure Θ) :
    avgRisk ℓ P κ π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ) ∂π := by
  rfl

/-- 确定性估计量通过推前分布使用与随机化估计量完全相同的平均风险接口。
@isnad1 id=eq.1h7v.s6.aa74394f1c94 from=translated src=- shape=a07d0584 vocab=618900df
-/
theorem avgRisk_deterministic
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (T : 𝓧 → 𝓨) (hT : Measurable T) (π : Measure Θ) :
    avgRisk ℓ P (Kernel.deterministic T hT) π =
      ∫⁻ θ, ∫⁻ y, ℓ θ y ∂((P.map T) θ) ∂π := by
  simp only [avgRisk, Kernel.deterministic_comp_eq_map hT P]

/-- Bayes 风险是每个合法随机化估计量的平均风险的下界。
@isnad1 id=le.0h7v.s6.94e9946791cd from=translated src=- shape=18bca94f vocab=50b38013
-/
theorem bayesRisk_le_estimator_avgRisk
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (π : Measure Θ) :
    bayesRisk ℓ P π ≤ avgRisk ℓ P κ π := by
  exact ProbabilityTheory.bayesRisk_le_avgRisk ℓ P κ π

/-- Bayes 估计量的定义展开：它恰好达到所有 Markov 估计量风险的下确界。
@isnad1 id=iff.0h7v.s6.27e8c61a4016 from=translated src=- shape=e2139377 vocab=2884a4b2
-/
theorem isBayesEstimator_iff
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (π : Measure Θ) :
    IsBayesEstimator ℓ P κ π ↔ avgRisk ℓ P κ π = bayesRisk ℓ P π := by
  rfl

end SandronesLibrary.Statistics
