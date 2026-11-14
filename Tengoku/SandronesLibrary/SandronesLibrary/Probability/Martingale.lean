/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.ConditionalExpectation
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Filtration
import Tengoku.Seed.Probability.Martingale.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 鞅、上鞅与下鞅

给定过滤 `𝓕` 和测度 `μ`，过程 `X` 是鞅，是指它适应于当前信息，并且对任意 `i ≤ j`，
未来值 `X j` 在时刻 `i` 信息下的条件期望几乎处处等于当前值 `X i`。上鞅把等号换成
“条件期望不超过当前值”，下鞅则换成反向不等式。

本文件直接采用 Mathlib 的 `MeasureTheory.Martingale`、`Supermartingale` 和
`Submartingale`，不另造过程结构。Mathlib 的三个定义使用 `StronglyAdapted`，因为条件期望是
Bochner 积分意义下的强可测对象。普通 `Adapted` 与强适应性不能在一般值域中无条件混同。

还有一个容易忽略的接口差异：上鞅和下鞅的定义显式包含逐时刻可积性；鞅定义只写强适应性与
条件期望等式。在完备值域中，令 `i = j` 即可由该等式推出可积性，因此教材中的可积性条件没有
丢失，只是由定理恢复。

> **Entry**: probability.martingale.definition
-/

namespace SandronesLibrary.Probability

open MeasureTheory

/-- 鞅的定义性展开：强适应，并且未来值关于当前信息的条件期望等于当前值。-/
theorem martingale_iff_stronglyAdapted_conditionalExpectation
    {Ω E ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : ι → Ω → E) (𝓕 : Filtration ι m) (μ : Measure Ω) :
    Martingale X 𝓕 μ ↔
      StronglyAdapted 𝓕 X ∧
        ∀ i j, i ≤ j → μ[X j | 𝓕 i] =ᵐ[μ] X i :=
  Iff.rfl

/-- 上鞅的定义性展开；与鞅不同，逐时刻可积性是定义的显式组成部分。-/
theorem supermartingale_iff_stronglyAdapted_conditionalExpectation
    {Ω E ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LE E]
    (X : ι → Ω → E) (𝓕 : Filtration ι m) (μ : Measure Ω) :
    Supermartingale X 𝓕 μ ↔
      StronglyAdapted 𝓕 X ∧
        (∀ i j, i ≤ j → μ[X j | 𝓕 i] ≤ᵐ[μ] X i) ∧
          ∀ i, Integrable (X i) μ :=
  Iff.rfl

/-- 下鞅的定义性展开；当前值几乎处处不超过未来值的当前条件期望。-/
theorem submartingale_iff_stronglyAdapted_conditionalExpectation
    {Ω E ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LE E]
    (X : ι → Ω → E) (𝓕 : Filtration ι m) (μ : Measure Ω) :
    Submartingale X 𝓕 μ ↔
      StronglyAdapted 𝓕 X ∧
        (∀ i j, i ≤ j → X i ≤ᵐ[μ] μ[X j | 𝓕 i]) ∧
          ∀ i, Integrable (X i) μ :=
  Iff.rfl

/-- Banach 空间值鞅的每个时刻取值都可积。可积性由 `i = j` 时的鞅等式推出。-/
theorem martingale_integrable
    {Ω E ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : ι → Ω → E} {𝓕 : Filtration ι m} {μ : Measure Ω}
    (hX : Martingale X 𝓕 μ) (i : ι) :
    Integrable (X i) μ :=
  hX.integrable i

/-- 在偏序 Banach 空间中，鞅恰好是同时为上鞅和下鞅的过程。-/
theorem martingale_iff_supermartingale_and_submartingale
    {Ω E ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [PartialOrder E]
    {X : ι → Ω → E} {𝓕 : Filtration ι m} {μ : Measure Ω} :
    Martingale X 𝓕 μ ↔ Supermartingale X 𝓕 μ ∧ Submartingale X 𝓕 μ :=
  MeasureTheory.martingale_iff

/-- 沿过滤逐层观察同一函数所得的条件期望过程是鞅。

这是定义层的首个实际消费者：过滤的单调性给出塔式条件期望，从而把已有的过滤与条件期望
接口组装成一个鞅。`SigmaFiniteFiltration` 保证每层条件期望所需的 trim 测度均为 σ-有限。-/
theorem conditionalExpectation_process_isMartingale
    {Ω E ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : Ω → E) (𝓕 : Filtration ι m) (μ : Measure Ω)
    [SigmaFiniteFiltration μ 𝓕] :
    Martingale (fun i ↦ μ[Y | 𝓕 i]) 𝓕 μ :=
  martingale_condExp Y 𝓕 μ

end SandronesLibrary.Probability
