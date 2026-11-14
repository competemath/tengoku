/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.SpectrumDefinition
import Tengoku.Seed.Analysis.Normed.Algebra.GelfandFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 复 Banach 代数的谱非空性、紧致性与谱半径

本文件把教材的谱半径定理挂靠到 Mathlib 的 Banach 代数谱 API。关键假设
`[Nontrivial A]` 表达教材中的“非零 Banach 代数”：零环的谱确实可以为空，因而不能省略。

Mathlib 已经给出了 Liouville 论证和 Gelfand 公式的分析核心；这里保留其原生 carrier，并将
非空、紧致、范数界、半径取到和幂范数极限组织成教材可直接使用的一组接口。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter Set
open scoped ENNReal NNReal Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A] [NormOneClass A] [Nontrivial A]

omit [NormOneClass A] in
/-- 非零复 Banach 代数中每个元素的谱非空。

Mathlib 的证明正是教材所用的 Liouville 路线：若谱为空，则预解映射在整个复平面上全纯，
并由无穷远处趋零推出恒为零，这与预解元可逆矛盾。

> **Entry**: functional-analysis.spectrum.nonempty-compact-/
theorem complexSpectrum_nonempty (a : A) :
    (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a

omit [NormOneClass A] [Nontrivial A] in
/-- 复 Banach 代数元素的谱是紧集。闭性来自可逆元集合的开放性，有界性来自 Neumann 级数：
`‖a‖ < ‖z‖` 时 `z·1-a` 可逆。-/
theorem complexSpectrum_isCompact (a : A) :
    IsCompact (spectrum ℂ a) :=
  spectrum.isCompact a

omit [Nontrivial A] in
/-- 每个谱值都落在以零为中心、半径 `‖a‖` 的闭球中。-/
theorem norm_spectrum_le (a : A) {z : ℂ} (hz : z ∈ spectrum ℂ a) :
    ‖z‖ ≤ ‖a‖ :=
  spectrum.norm_le_norm_of_mem hz

omit [Nontrivial A] in
/-- 谱半径不超过代数元素的范数。结果保留 Mathlib 的 `ℝ≥0∞` 谱半径 carrier。-/
theorem spectralRadius_le_nnnorm (a : A) :
    spectralRadius ℂ a ≤ (‖a‖₊ : ℝ≥0∞) :=
  spectrum.spectralRadius_le_nnnorm a

omit [NormOneClass A] in
/-- 非空紧谱上的范数取得最大值；这个最大值恰为谱半径。这里把“非空 + 紧致 + 上确界定义”
组合成教材中 `max_{z ∈ σ(a)} ‖z‖` 的可用见证。-/
theorem exists_spectrum_nnnorm_eq_spectralRadius (a : A) :
    ∃ z ∈ spectrum ℂ a, (‖z‖₊ : ℝ≥0∞) = spectralRadius ℂ a :=
  spectrum.exists_nnnorm_eq_spectralRadius a

omit [NormOneClass A] [Nontrivial A] in
/-- Gelfand 谱半径公式：幂范数的 `n` 次根在 `ℝ≥0∞` 中收敛到谱半径。

`n = 0` 没有被排除；表达式采用 Mathlib 的总函数幂约定。有限个首项不影响 `atTop` 极限。-/
theorem tendsto_nthRoot_nnnorm_pow_spectralRadius (a : A) :
    Tendsto (fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ))
      atTop (𝓝 (spectralRadius ℂ a)) :=
  spectrum.gelfand_formula a

end SandronesLibrary.FunctionalAnalysis
