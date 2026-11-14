/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.Density
import Tengoku.Seed.Probability.Kernel.CondDistrib

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 充分统计量与因子分解入口

统计模型 `P : Kernel Θ 𝓧` 在参数 `θ` 下给出样本分布 `P θ`，统计量
`S : 𝓧 → 𝓨` 只保留样本的某种摘要。`S` 充分的字面含义是：知道 `S` 以后，完整样本的条件分布
不再依赖未知参数。

当样本空间是标准 Borel 空间时，Mathlib 的 `condDistrib id S (P θ)` 给出完整样本 `id` 在给定
`S` 后的正规条件分布。`IsSufficientStatistic P S` 要求存在一个参数无关的 Markov kernel `Q`，
使它与每个参数下的条件分布在统计量分布 `(P θ).map S` 下几乎处处相等。a.e. 量词不能改成逐点
相等，因为零概率统计量值上的条件分布版本没有统计意义，也不由模型唯一决定。

`ReconstructsFromStatistic` 单独记录 Blackwell 重构：统计量的分布经参数无关 kernel 后处理后恢复
原模型。本文件证明充分性推出重构，但不声称无额外条件的反向命题。

对支配模型，`NeymanFisherFactorizes` 保存联合可测 `ℝ≥0∞` 密度的 a.e. 因子分解语义。本批只给
定义，不证明一般 Neyman--Fisher 定理。最后的有限离散原型在更强的纤维归一化假设下显式构造
参数无关重构概率，证明因子分解确有真实消费者。

> **Entry**: statistics.sufficiency.definition
-/

namespace SandronesLibrary.Statistics

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

/-- `S` 是模型 `P` 的充分统计量：给定 `S` 后完整样本的正规条件律可选择为与参数无关的同一
Markov kernel。

条件 kernel 只要求在各自统计量分布下几乎处处相等。这正是正规条件分布版本唯一性的层级。-/
def IsSufficientStatistic
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (S : 𝓧 → 𝓨) : Prop :=
  Measurable S ∧ ∃ Q : Kernel 𝓨 𝓧,
    IsMarkovKernel Q ∧
      ∀ θ, condDistrib id S (P θ) =ᵐ[(P θ).map S] Q

/-- Blackwell 重构性质：从统计量实验的输出分布出发，经一个参数无关 Markov kernel 可以恢复原
数据分布族。它与条件律定义分开承载，避免在缺少正则性时无条件宣称反向等价。-/
def ReconstructsFromStatistic
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    (P : Kernel Θ 𝓧) (S : 𝓧 → 𝓨) (hS : Measurable S) : Prop :=
  ∃ Q : Kernel 𝓨 𝓧,
    IsMarkovKernel Q ∧ Q ∘ₖ (Kernel.deterministic S hS ∘ₖ P) = P

/-- 共同的参数无关条件分布 kernel 能够从统计量分布重建每个原始样本分布。
@isnad1 id=reconstr.1h5v.s5.4fef077ec444 from=translated src=- shape=3460c172 vocab=ac38ca58
-/
theorem sufficientStatistic_reconstructs
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Kernel Θ 𝓧) [IsMarkovKernel P] (S : 𝓧 → 𝓨)
    (h : IsSufficientStatistic P S) :
    ReconstructsFromStatistic P S h.1 := by
  rcases h with ⟨hS, Q, hQ, hcond⟩
  refine ⟨Q, hQ, ?_⟩
  rw [Kernel.deterministic_comp_eq_map hS]
  ext θ : 1
  rw [Kernel.comp_apply, Kernel.map_apply P hS]
  calc
    Q ∘ₘ (P θ).map S = condDistrib id S (P θ) ∘ₘ (P θ).map S :=
      Measure.comp_congr (hcond θ).symm
    _ = (P θ).map id := condDistrib_comp_map hS.aemeasurable aemeasurable_id
    _ = P θ := Measure.map_id

/-- 支配模型的 Neyman--Fisher 因子分解谓词。

密度使用 kernel 的联合可测 RN 版本，等式只在支配测度 `ν` 下几乎处处成立。因子 `g` 对参数和
统计量值联合可测，`h` 只依赖完整样本。这个定义本身不宣称因子分解已经推出充分性。-/
def NeymanFisherFactorizes
    {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    [MeasurableSpace.CountableOrCountablyGenerated Θ 𝓧]
    (P : Kernel Θ 𝓧) (ν : Measure 𝓧) (S : 𝓧 → 𝓨) : Prop :=
  Measurable S ∧ ∃ (g : Θ → 𝓨 → ℝ≥0∞) (h : 𝓧 → ℝ≥0∞),
    Measurable (Function.uncurry g) ∧ Measurable h ∧
      ∀ θ, (fun x ↦ P.rnDeriv (Kernel.const Θ ν) θ x) =ᵐ[ν]
        (fun x ↦ g θ (S x) * h x)

section FinitePrototype

variable {Θ 𝓧 𝓨 : Type*} [Fintype 𝓧] [Fintype 𝓨] [DecidableEq 𝓨]

/-- 有限离散模型中统计量取值 `y` 的边缘质量。-/
def finiteStatisticMass (p : Θ → 𝓧 → ℝ≥0) (S : 𝓧 → 𝓨) (θ : Θ) (y : 𝓨) : ℝ≥0 :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ S x = y), p θ x

/-- 有限模型的归一化因子分解：`pθ(x)=gθ(Sx)h(x)`，并且 `h` 在每个统计量纤维上的和为一。

纤维归一化强于一般 Neyman--Fisher 因子分解；它专门用于透明地构造首个重构消费者。-/
def FiniteNormalizedFactorization (p : Θ → 𝓧 → ℝ≥0) (S : 𝓧 → 𝓨) : Prop :=
  ∃ (g : Θ → 𝓨 → ℝ≥0) (h : 𝓧 → ℝ≥0),
    (∀ θ x, p θ x = g θ (S x) * h x) ∧
      ∀ y, ∑ x ∈ Finset.univ.filter (fun x ↦ S x = y), h x = 1

/-- 有限模型的参数无关重构：每个统计量值 `y` 对应一个概率质量函数 `q y`，混合权重是统计量的
边缘分布，混合结果恢复原质量函数。-/
def FiniteReconstruction (p : Θ → 𝓧 → ℝ≥0) (S : 𝓧 → 𝓨) : Prop :=
  ∃ q : 𝓨 → 𝓧 → ℝ≥0,
    (∀ y, ∑ x, q y x = 1) ∧
      ∀ θ x, p θ x = ∑ y, finiteStatisticMass p S θ y * q y x

/-- 有限离散归一化因子分解显式给出参数无关的纤维重构概率。
@isnad1 id=finitere.1h5v.s5.db674cc457cc from=translated src=- shape=7ee1a84b vocab=457603eb
-/
theorem finite_normalizedFactorization_implies_reconstruction
    (p : Θ → 𝓧 → ℝ≥0) (S : 𝓧 → 𝓨)
    (hfac : FiniteNormalizedFactorization p S) :
    FiniteReconstruction p S := by
  rcases hfac with ⟨g, h, hp, hh⟩
  refine ⟨fun y x ↦ if S x = y then h x else 0, ?_, ?_⟩
  · intro y
    simpa [Finset.sum_filter] using hh y
  · intro θ x
    have hmass (y : 𝓨) : finiteStatisticMass p S θ y = g θ y := by
      unfold finiteStatisticMass
      calc
        ∑ z ∈ Finset.univ.filter (fun z ↦ S z = y), p θ z =
            ∑ z ∈ Finset.univ.filter (fun z ↦ S z = y), g θ (S z) * h z := by
              apply Finset.sum_congr rfl
              intro z _
              exact hp θ z
        _ = ∑ z ∈ Finset.univ.filter (fun z ↦ S z = y), g θ y * h z := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [Finset.mem_filter] at hz
              rw [hz.2]
        _ = g θ y * ∑ z ∈ Finset.univ.filter (fun z ↦ S z = y), h z := by
              rw [Finset.mul_sum]
        _ = g θ y := by rw [hh y, mul_one]
    rw [hp θ x]
    simp [hmass]

end FinitePrototype

end SandronesLibrary.Statistics
