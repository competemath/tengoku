/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Variable
import Tengoku.Seed.Probability.Process.Adapted

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 过滤与适应过程

过滤 `𝓕 : Filtration ι m` 是一族随时间单调增加、且都不超过环境 σ-代数 `m` 的 σ-代数。
它把“截至时刻 `i` 已知的信息”形式化为 `𝓕 i`。过程 `X` 适应于 `𝓕`，是指每个 `X i`
都只依赖截至时刻 `i` 的信息，即 `X i` 关于 `𝓕 i` 可测。

本文件直接采用 Mathlib 的 `MeasureTheory.Filtration` 和 `MeasureTheory.Adapted`。时间指标只需
`Preorder`，不无理由收紧为线性序。Mathlib 4.33 中 `Adapted` 指普通可测性；旧版曾由该名字
表示的强可测概念现已改名为 `StronglyAdapted`。

> **Entry**: probability.filtration.definition
-/

namespace SandronesLibrary.Probability

open MeasureTheory

/-- 过滤所含的信息随时间单调增加。-/
theorem filtration_mono
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (𝓕 : Filtration ι m) {i j : ι} (hij : i ≤ j) :
    𝓕 i ≤ 𝓕 j :=
  𝓕.mono hij

/-- 过滤的每一层都是环境 σ-代数的子 σ-代数。-/
theorem filtration_le
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    (𝓕 : Filtration ι m) (i : ι) :
    𝓕 i ≤ m :=
  𝓕.le i

/-- 适应性的定义性展开：过程在每个时刻都关于当时的信息可测。-/
theorem adapted_iff_measurable
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (𝓕 : Filtration ι m) (X : (i : ι) → Ω → β i) :
    Adapted 𝓕 X ↔ ∀ i, Measurable[𝓕 i] (X i) :=
  Iff.rfl

/-- 适应过程的过去取值关于任一未来时刻的信息可测。-/
theorem adapted_measurable_later
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {𝓕 : Filtration ι m} {X : (i : ι) → Ω → β i}
    (hX : Adapted 𝓕 X) {i j : ι} (hij : i ≤ j) :
    Measurable[𝓕 j] (X i) := by
  exact (hX i).mono (filtration_mono 𝓕 hij) le_rfl

/-- 适应过程的每个时刻取值也关于环境 σ-代数可测。-/
theorem adapted_measurable
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {𝓕 : Filtration ι m} {X : (i : ι) → Ω → β i}
    (hX : Adapted 𝓕 X) (i : ι) :
    Measurable[m] (X i) := by
  exact (hX i).mono (filtration_le 𝓕 i) le_rfl

end SandronesLibrary.Probability
