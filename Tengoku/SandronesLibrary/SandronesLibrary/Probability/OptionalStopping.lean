/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Martingale
import Tengoku.Seed.Probability.Martingale.OptionalStopping

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 有界停时的可选停止定理

停时 `τ : Ω → ℕ∞` 是只凭截至当前时刻的信息就能判断是否已经停止的随机时刻。若 `X` 是离散时间
实值鞅，而停时 `τ ≤ σ` 且 `σ` 被同一个确定常数 `N` 一致控制，则

`𝔼[X_τ] = 𝔼[X_σ]`。

特别地，与常停时 `0` 比较可得 `𝔼[X_τ] = 𝔼[X_0]`。有界性同时排除了 `τ = ∞`，并保证停止值
由有限多个可积随机变量拼成，因此这里不需要额外的一致可积性条件。

本文件直接复用 Mathlib 的 `IsStoppingTime`、`stoppedValue` 与
`Submartingale.expected_stoppedValue_mono`。鞅既是下鞅，`-X` 也为鞅；对二者应用同一个次鞅不等式
给出两向不等式，从而得到等号。

> **Entry**: probability.martingale.optional-stopping-entry
-/

namespace SandronesLibrary.Probability

open MeasureTheory
open scoped ProbabilityTheory

/-- 停时的定义性展开：在时刻 `i` 已经停止的事件属于时刻 `i` 的信息。
@isnad1 id=iff.0h5v.s5.8d54b1d97df8 from=translated src=- shape=a66ea9f8 vocab=cf0ecc1b
-/
theorem stoppingTime_iff_measurableSet_le
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (𝓕 : Filtration ι m) (τ : Ω → WithTop ι) :
    IsStoppingTime 𝓕 τ ↔ ∀ i, MeasurableSet[𝓕 i] {ω | τ ω ≤ i} :=
  Iff.rfl

/-- 停止值是在随机时刻 `τ ω` 取过程值；若 `τ ω = ∞`，`untopA` 使用任意指标。
可选停止定理中的一致有界假设会排除这个无限分支。
@isnad1 id=eq.0h6v.s5.2af40a38d455 from=translated src=- shape=3e6a010c vocab=0fec33e9
-/
theorem stoppedValue_apply
    {Ω E ι : Type*} [Nonempty ι]
    (X : ι → Ω → E) (τ : Ω → WithTop ι) (ω : Ω) :
    stoppedValue X τ ω = X (τ ω).untopA ω :=
  rfl

/-- 有界可选停止定理：若 `τ ≤ σ ≤ N`，实值鞅在两个停时处的期望相等。
@isnad1 id=eq.5h8v.s7.c305da4d13fe from=translated src=- shape=47d13501 vocab=87c847c0
-/
theorem martingale_expected_stoppedValue_eq
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℕ m} [SigmaFiniteFiltration μ 𝓕]
    {X : ℕ → Ω → ℝ} (hX : Martingale X 𝓕 μ)
    {τ σ : Ω → ℕ∞} (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    (hτσ : τ ≤ σ) {N : ℕ} (hσN : ∀ ω, σ ω ≤ N) :
    μ[stoppedValue X τ] = μ[stoppedValue X σ] := by
  apply le_antisymm
  · exact hX.submartingale.expected_stoppedValue_mono hτ hσ hτσ hσN
  · have hneg := hX.neg.submartingale.expected_stoppedValue_mono hτ hσ hτσ hσN
    simpa only [Pi.neg_apply, stoppedValue, integral_neg, neg_le_neg_iff] using hneg

/-- 有界停时版本的公平游戏公式：停止时的期望等于初始期望。
@isnad1 id=eq.3h7v.s7.04c921eefaa7 from=translated src=- shape=f85ff3f3 vocab=87c847c0
-/
theorem martingale_expected_stoppedValue_eq_initial
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℕ m} [SigmaFiniteFiltration μ 𝓕]
    {X : ℕ → Ω → ℝ} (hX : Martingale X 𝓕 μ)
    {τ : Ω → ℕ∞} (hτ : IsStoppingTime 𝓕 τ)
    {N : ℕ} (hτN : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue X τ] = μ[X 0] := by
  symm
  simpa only [stoppedValue_const] using
    (martingale_expected_stoppedValue_eq hX (isStoppingTime_const 𝓕 0) hτ
      (fun _ ↦ bot_le) hτN)

end SandronesLibrary.Probability
