/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.Model
import Tengoku.SandronesLibrary.SandronesLibrary.Statistics.Estimator
import Tengoku.Seed.Probability.Kernel.MeasurableIntegral
import Tengoku.Seed.Probability.Kernel.Integral
import Tengoku.Seed.MeasureTheory.Function.ConvergenceInMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 矩估计

设统计模型 `P : Kernel Θ 𝓧`（`[IsMarkovKernel P]`）与统计量 `T : 𝓧 → 𝓨`。参数 `θ` 下的
**总体矩**是 `T` 关于模型纤维 `P θ` 的 Bochner 积分

`momentMap P T θ = ∫ x, T x ∂(P θ)`。

**矩估计**把样本矩与总体矩配平：给定样本矩统计量 `S : 𝓧 → 𝓨`，可测映射 `θhat : 𝓧 → Θ`
是矩估计，当且仅当对每个观测 `x` 都有 `momentMap P T (θhat x) = S x`。这条等式就是矩方程，
不另建 `Moment`/`EmpiricalMeasure` 载体。

## 前提一：模型族可测性与矩存在性

`momentMap_measurable` 证明矩映射 `θ ↦ ∫ x, T x ∂(P θ)` 随参数可测。这正是 kernel 的
参数可测性经积分后的产物（Mathlib 的 `StronglyMeasurable.integral_kernel` 是正式承载），
它使"矩函数"成为参数空间上可测的对象，而不是逐参数孤立的数。可测性只需 `T` 强可测，
不需要 `T` 可积。

**矩存在性是另一条独立假设。** Bochner 积分对不可积函数返回 `0`，所以没有 `Integrable T (P θ)`
时 `momentMap P T θ` 只是退化值，不承载总体矩语义。本条目把逐参数可积性显式写进每个需要它的
定理（`momentMap_add`、`momentMap_const` 的常数情形等），不从 `IsMarkovKernel` 静默推出可积性。
`momentMap_const` 与 `momentMap_deterministic` 是两个消费者：前者说明概率模型下常数统计量的矩
就是该常数，后者说明确定性观测模型下总体矩退化为 `T (g θ)`。前者的证明直接用
`statistics.model.definition` 的 `statisticalModel_measure_univ`（模型总质量为一），后者的
`methodOfMomentsEstimator_isMarkov` 直接复用 `statistics.estimator.definition` 的
`deterministicEstimator_isMarkov`，因此两个前提条目都是真实消费者而不是装饰。

## 前提二：识别性与矩方程的适定性

仅有定义不足以谈一致性。本条目把一致性拆成三条**显式前提**：

* `MomentIdentifiable P T`：总体矩映射单射。它给出矩估计的唯一性
  （`methodOfMomentsEstimator_unique`），并在样本矩恰好等于真值时迫使估计等于真值
  （`methodOfMomentsEstimator_eq_of_sample_moment_eq`）。
* `MomentEquationWellPosedAt P T θ₀`：矩映射在 `θ₀` 处**局部可逆**，即其逆在 `θ₀` 连续
  （ε-δ 形式，用 `edist` 表述）。这是识别性的加强形式：单射只保证"矩相等 ⟹ 参数相等"，
  不保证"矩接近 ⟹ 参数接近"。教材通常由"参数空间紧 + 矩映射连续 + 单射"推出它，本条目
  不把这一步当作免费结论，而是作为显式假设；从紧性推出它的证明不在本条目内。
* 样本矩在真参数下依概率收敛到真值处的总体矩。这是大数定律一侧的输入，本条目同样只作假设。

`methodOfMomentsEstimator_tendstoInMeasure` 把这三条组装成相合性：矩估计序列依概率收敛到真值。
它不证明大数定律，也不构造经验测度；`S` 是外部给定的样本矩统计量（例如 `n` 份样本的均值），
其构造属于概率论极限定理一侧。

## 未完成边界

本条目不构造样本矩（无经验测度、无 `(1/n)∑ T(Xᵢ)`）、不证明大数定律、不从紧性推出矩方程的
适定性、不给出矩估计的渐近正态性或有效性，也不处理"矩条件个数多于参数维数"的一般 `k` 矩
联合系统——`T` 与 `S` 取值于任意实赋范空间 `𝓨`，因此 `𝓨 = ℝ^k` 的多元矩已可表达，但
"用哪 `k` 个矩、如何挑选"不在本条目内。

> **Entry**: statistics.method-of-moments
-/

namespace SandronesLibrary.Statistics

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

section Definition

variable {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]
  [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]

/-- 统计量 `T` 在参数 `θ` 下的**总体矩**：`T` 关于模型纤维 `P θ` 的 Bochner 积分。

当 `T` 不关于 `P θ` 可积时，Bochner 积分返回 `0`，此时该值不是总体矩；调用方必须显式给出
`Integrable T (P θ)`（矩存在性）。-/
noncomputable def momentMap (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) (θ : Θ) : 𝓨 :=
  ∫ x, T x ∂(P θ)

/-- **矩估计**：可测映射 `θhat` 在每个观测处让总体矩等于样本矩 `S`。

`S : 𝓧 → 𝓨` 是外部给定的样本矩统计量（共同观测空间约定与 `statistics.estimator.consistency`
一致）。等式是逐点成立的：矩方程 `momentMap P T (θhat x) = S x` 对每个 `x` 都要成立，因为
`momentMap` 是真正的函数而不是密度版本，不存在零测集上的版本差异。可测性分量保证 `θhat`
确实是估计量，可经 `Kernel.deterministic` 接入随机化估计量接口。-/
def IsMethodOfMomentsEstimator (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) (S : 𝓧 → 𝓨)
    (θhat : 𝓧 → Θ) : Prop :=
  Measurable θhat ∧ ∀ x, momentMap P T (θhat x) = S x

/-- 矩估计的定义展开。
@isnad1 id=iff.0h7v.s6.2dcaa29c8aa1 from=translated src=- shape=8fc501a7 vocab=93c8cf2e
-/
theorem isMethodOfMomentsEstimator_iff (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) (S : 𝓧 → 𝓨)
    (θhat : 𝓧 → Θ) :
    IsMethodOfMomentsEstimator P T S θhat ↔
      Measurable θhat ∧ ∀ x, momentMap P T (θhat x) = S x :=
  Iff.rfl

/-- **模型族可测性**：矩映射随参数可测。

这是 kernel 参数可测性经积分后的结论，只要求 `T` 强可测（不需要可积）。它是把"矩函数"
当作参数空间上可测对象的依据。
@isnad1 id=measurab.1h5v.s6.6a4ae6121c81 from=translated src=- shape=5e8453e6 vocab=cdf5c8cb
-/
theorem momentMap_measurable [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) (hT : StronglyMeasurable T) :
    Measurable (momentMap P T) := by
  change Measurable fun θ => ∫ x, T x ∂(P θ)
  exact hT.integral_kernel.measurable

/-- **矩存在性**下的加性：逐参数可积时，矩映射对统计量的加法线性。

可积性是真实假设：没有它 Bochner 积分可能退化为 `0`，右端的分解不成立。
@isnad1 id=eq.2h7v.s7.3189df317813 from=translated src=- shape=b1f51c50 vocab=2eefbe3d
-/
theorem momentMap_add (P : Kernel Θ 𝓧) (T T' : 𝓧 → 𝓨) (θ : Θ)
    (hT : Integrable T (P θ)) (hT' : Integrable T' (P θ)) :
    momentMap P (T + T') θ = momentMap P T θ + momentMap P T' θ := by
  simpa [momentMap] using integral_add hT hT'

/-- 概率模型下常数统计量的矩就是该常数。这是矩存在性最简的消费者：模型总质量为一是它成立
的唯一原因，证明直接引用 `statistics.model.definition` 的 `statisticalModel_measure_univ`。
@isnad1 id=eq.0h6v.s6.ddb28bcff65c from=translated src=- shape=39b072ed vocab=dc3b393e
-/
theorem momentMap_const (P : Kernel Θ 𝓧) [IsMarkovKernel P] [CompleteSpace 𝓨]
    (c : 𝓨) (θ : Θ) :
    momentMap P (fun _ => c) θ = c := by
  have h₁ : (P θ) Set.univ = 1 := statisticalModel_measure_univ P θ
  simp [momentMap, integral_const, measureReal_def, h₁]

/-- 确定性观测模型 `P = Kernel.deterministic g hg` 下，总体矩退化为 `T (g θ)`。

这把矩估计接到 `statistics.model.definition` 的确定性模型桥上：确定性参数族无需另设载体。
@isnad1 id=eq.2h6v.s6.2d7f9e712441 from=translated src=- shape=146dc991 vocab=a8c9fc94
-/
theorem momentMap_deterministic {g : Θ → 𝓧} (hg : Measurable g) (T : 𝓧 → 𝓨)
    [CompleteSpace 𝓨] (hT : StronglyMeasurable T) (θ : Θ) :
    momentMap (Kernel.deterministic g hg) T θ = T (g θ) := by
  simpa [momentMap] using Kernel.integral_deterministic' hg hT

/-- **矩识别性**：总体矩映射在参数空间上单射。

这是矩估计可识别性的正式载体：不同的参数必须给出不同的总体矩。-/
def MomentIdentifiable (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) : Prop :=
  Function.Injective (momentMap P T)

/-- 识别性的定义展开。
@isnad1 id=iff.0h5v.s6.5e5dd22cc669 from=translated src=- shape=2f29d7e4 vocab=e8fdd9cd
-/
theorem momentIdentifiable_iff (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) :
    MomentIdentifiable P T ↔ ∀ θ θ', momentMap P T θ = momentMap P T θ' → θ = θ' :=
  Iff.rfl

/-- 识别性给出矩估计的唯一性：同一个样本矩统计量至多对应一个矩估计。
@isnad1 id=eq.3h8v.s6.8718a56168cc from=translated src=- shape=e0a78224 vocab=995335e3
-/
theorem methodOfMomentsEstimator_unique (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) (S : 𝓧 → 𝓨)
    (h : MomentIdentifiable P T) {θhat θhat' : 𝓧 → Θ}
    (h1 : IsMethodOfMomentsEstimator P T S θhat)
    (h2 : IsMethodOfMomentsEstimator P T S θhat') :
    θhat = θhat' := by
  funext x
  exact h (by rw [h1.2 x, h2.2 x])

/-- 样本矩恰好等于真值处总体矩时，识别性迫使矩估计等于真值。这是矩估计"精确识别"的极限
情形，也是 `methodOfMomentsEstimator_unique` 的直接消费者。
@isnad1 id=eq.3h8v.s6.d39841a87877 from=translated src=- shape=403391b9 vocab=4b774cf9
-/
theorem methodOfMomentsEstimator_eq_const_of_sample_moment_eq (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨)
    (S : 𝓧 → 𝓨) (θhat : 𝓧 → Θ) (θ₀ : Θ) (h : MomentIdentifiable P T)
    (h1 : IsMethodOfMomentsEstimator P T S θhat)
    (hS : ∀ x, S x = momentMap P T θ₀) :
    θhat = fun _ => θ₀ := by
  funext x
  exact h (by rw [h1.2 x, hS x])

/-- 矩估计经 Dirac kernel 给出合法的确定性估计量，接入 `statistics.estimator.definition`
的随机化估计量接口。证明直接复用该条目的 `deterministicEstimator_isMarkov`，只使用定义中的
可测性分量；本引理不产生新的数学内容，职责是接口桥。
@isnad1 id=ismarkov.1h7v.s6.a13bdc99a0ec from=translated src=- shape=b12cd4ad vocab=829be57d
-/
theorem methodOfMomentsEstimator_isMarkov (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) (S : 𝓧 → 𝓨)
    (θhat : 𝓧 → Θ) (h : IsMethodOfMomentsEstimator P T S θhat) :
    IsMarkovKernel (Kernel.deterministic θhat h.1) :=
  deterministicEstimator_isMarkov θhat h.1

end Definition

section Consistency

variable {Θ 𝓧 𝓨 : Type*} [MeasurableSpace Θ] [PseudoMetricSpace Θ] [MeasurableSpace 𝓧]
  [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨]

/-- **矩方程在 `θ₀` 处的适定性**：矩映射的逆在 `θ₀` 连续，用 `edist` 的 ε-δ 形式表述。

这是识别性的加强形式，也是一致性证明真正使用的条件：单射只给出"矩相等 ⟹ 参数相等"，
不给出"矩接近 ⟹ 参数接近"。教材一般由"参数空间紧 + 矩映射连续 + 单射"推出它；本条目把
它作为显式假设，不从紧性推导。-/
def MomentEquationWellPosedAt (P : Kernel Θ 𝓧) (T : 𝓧 → 𝓨) (θ₀ : Θ) : Prop :=
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
    ∀ θ, edist (momentMap P T θ) (momentMap P T θ₀) < δ → edist θ θ₀ < ε

/-- **矩估计的相合性转移**：矩方程适定、样本矩依概率收敛到真值处总体矩、且每个阶段的
`θhat n` 都是该阶段样本矩的矩估计，则 `θhat n` 在真参数 `P θ₀` 下依概率收敛到 `θ₀`。

大数定律（`hS`）与矩方程适定性（`hwp`）都是显式前提：本定理只做"矩收敛 ⟹ 参数收敛"这一步
拓扑转移，不证明样本矩本身收敛。证明是测度单调性加夹逼：由 `hwp` 的逆连续性，事件
`{ε ≤ edist (θhat n x) θ₀}` 被事件 `{δ ≤ edist (S n x) (momentMap P T θ₀)}` 包含，后者的
概率按 `hS` 趋于零。
@isnad1 id=tendstoi.3h8v.s7.715f24138b5c from=translated src=- shape=ecb93e7c vocab=8d47ffc5
-/
theorem methodOfMomentsEstimator_tendstoInMeasure (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (T : 𝓧 → 𝓨) (S : ℕ → 𝓧 → 𝓨) (θhat : ℕ → 𝓧 → Θ) (θ₀ : Θ)
    (hwp : MomentEquationWellPosedAt P T θ₀)
    (hS : TendstoInMeasure (P θ₀) S atTop (fun _ => momentMap P T θ₀))
    (hθ : ∀ n, IsMethodOfMomentsEstimator P T (S n) (θhat n)) :
    TendstoInMeasure (P θ₀) θhat atTop (fun _ => θ₀) := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hwp ε hε
  have hle : ∀ n, (P θ₀) {x | ε ≤ edist (θhat n x) θ₀} ≤
      (P θ₀) {x | δ ≤ edist (S n x) (momentMap P T θ₀)} := by
    intro n
    refine measure_mono fun x hx => ?_
    have hxε : ¬ edist (θhat n x) θ₀ < ε := not_lt.mpr hx
    by_contra hcon
    exact hxε (hδ (θhat n x) (by rw [(hθ n).2 x]; exact not_le.mp hcon))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hS δ hδpos)
    (fun _ => bot_le) hle

end Consistency

end SandronesLibrary.Statistics
