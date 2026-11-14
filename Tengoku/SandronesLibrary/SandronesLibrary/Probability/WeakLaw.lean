/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Convergence
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.Inequalities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 弱大数律

设 `X 0, X 1, ...` 是独立同分布的实值随机变量，且 `X 0` 二次可积。本文件证明样本均值

`(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i`

依概率收敛到共同期望。证明保留教材中的 Chebyshev 方差路线：同分布传递二次可积性、期望与
方差；独立性使有限和方差可加；样本均值方差等于单项方差除以 `n`；Chebyshev 不等式再把任意
固定阈值的偏差概率压到常数乘 `1/n`。

这里直接使用 `iIndepFun` 和 `IdentDistrib` 承载 iid，不另造重复谓词。结论沿既有
`TendstoInMeasure` 接口陈述，因此与本库的概率收敛定义完全一致。`Finset.range n` 从 `0` 到
`n-1`；`n = 0` 时逆元和空和把首项定义为零，但 `atTop` 极限只使用最终满足 `1 ≤ n` 的尾部。

本证明没有调用强大数律反推。它也不声称只需一阶矩、非同分布序列、三角阵或 Banach 值版本。

> **Entry**: probability.law-large-numbers.weak
-/

namespace SandronesLibrary.Probability

open Filter MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory Topology ENNReal BigOperators

/-- 同分布把基准随机变量的二次可积性传递给序列的每一项。
@isnad1 id=memlp.2h4v.s7.bac5d5f2a5fe from=translated src=- shape=a457eaf7 vocab=69ff20c4
-/
theorem iid_memLp_of_memLp_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (i : ℕ) :
    MemLp (X i) 2 μ := by
  exact (hident i).memLp_iff.mpr hX

/-- iid 序列的前 `n` 项和仍然二次可积。
@isnad1 id=memlp.2h4v.s7.eadd154636bb from=translated src=- shape=7f9afe9e vocab=2cf5fce7
-/
theorem iid_sum_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    MemLp (fun ω ↦ ∑ i ∈ range n, X i ω) 2 μ := by
  convert! memLp_finsetSum' (range n)
    (fun i _ ↦ iid_memLp_of_memLp_zero X hX hident i) using 1
  ext ω
  simp

/-- 独立同分布序列的前 `n` 项和的方差是单项方差的 `n` 倍。
@isnad1 id=eq.3h4v.s7.c0413404710b from=translated src=- shape=cd064685 vocab=72fd1d1b
-/
theorem iid_sum_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    Var[fun ω ↦ ∑ i ∈ range n, X i ω; μ] = n * Var[X 0; μ] := by
  have heq : (fun ω ↦ ∑ i ∈ range n, X i ω) = ∑ i ∈ range n, X i := by
    ext ω
    simp
  rw [heq, IndepFun.variance_sum]
  · simp_rw [(hident _).variance_eq]
    simp
  · intro i hi
    exact iid_memLp_of_memLp_zero X hX hident i
  · intro i hi j hj hij
    exact hindep.indepFun hij

/-- iid 样本均值二次可积，因而可以应用 Chebyshev 不等式。
@isnad1 id=memlp.2h4v.s7.ebbcdbfb54a9 from=translated src=- shape=b22d2b61 vocab=9ab049a2
-/
theorem iid_sampleMean_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    MemLp (fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω) 2 μ := by
  exact (iid_sum_memLp X hX hident n).const_mul _

/-- 在概率空间上，iid 序列前 `n` 项和的期望是共同期望的 `n` 倍。
@isnad1 id=eq.2h4v.s7.e6a6670fcf7a from=translated src=- shape=1e8eafcc vocab=0696794c
-/
theorem iid_sum_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    ∫ ω, (∑ i ∈ range n, X i ω) ∂μ = n * ∫ ω, X 0 ω ∂μ := by
  rw [integral_finsetSum]
  · simp_rw [(hident _).integral_eq]
    simp
  · intro i hi
    exact (iid_memLp_of_memLp_zero X hX hident i).integrable (by norm_num)

/-- 对正样本量，iid 样本均值的期望等于每一项的共同期望。
@isnad1 id=eq.3h4v.s7.c58f20c8b624 from=translated src=- shape=738fe67d vocab=e6cb22c1
-/
theorem iid_sampleMean_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω ∂μ = ∫ ω, X 0 ω ∂μ := by
  rw [integral_const_mul, iid_sum_integral X hX hident]
  field_simp

/-- 对正样本量，iid 样本均值的方差等于单项方差除以样本量。
@isnad1 id=eq.4h4v.s7.47919a22d69d from=translated src=- shape=eb8e9b36 vocab=1380ce98
-/
theorem iid_sampleMean_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {n : ℕ} (hn : 0 < n) :
    Var[fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω; μ] = Var[X 0; μ] / n := by
  rw [variance_const_mul, iid_sum_variance X hX hindep hident]
  field_simp

/-- **弱大数律**：二次可积的 iid 实值随机变量的样本均值依概率收敛到共同期望。

证明在正样本量尾部应用 Chebyshev 不等式，并以
`Var[X 0; μ] / ε² * n⁻¹` 控制偏差事件的实测度。该上界趋于零。
@isnad1 id=tendstoi.3h3v.s7.30dd127a2c08 from=translated src=- shape=bba3eb43 vocab=13250ebf
-/
theorem weakLaw_of_iid_finiteVariance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX : MemLp (X 0) 2 μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ range n, X i ω)
      atTop (fun _ ↦ ∫ ω, X 0 ω ∂μ) := by
  rw [convergesInProbability_iff_measureReal_dist]
  intro ε hε
  let C : ℝ := Var[X 0; μ] / ε ^ 2
  have hC : 0 ≤ C := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper_tendsto : Tendsto (fun n : ℕ ↦ C * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_tendsto
  · filter_upwards with n
    exact measureReal_nonneg
  · filter_upwards [eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
    have hnpos : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    have hcheb := chebyshev_inequality (iid_sampleMean_memLp X hX hident n) hε
    rw [iid_sampleMean_integral X hX hident hnpos,
      iid_sampleMean_variance X hX hindep hident hnpos] at hcheb
    rw [Measure.real_def]
    have hreal := ENNReal.toReal_mono (by simp) hcheb
    rw [ENNReal.toReal_ofReal
      (div_nonneg (div_nonneg (variance_nonneg _ _) (Nat.cast_nonneg _)) (sq_nonneg _))] at hreal
    simpa [Real.dist_eq, C, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hreal

end SandronesLibrary.Probability
