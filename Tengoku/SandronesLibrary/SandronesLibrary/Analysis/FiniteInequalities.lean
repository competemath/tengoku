/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Analysis.MeanInequalities
import Tengoku.Seed.Analysis.Real.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 有限实数族的经典不等式

本模块补齐在测度论 `Lᵖ` 之前就应掌握的有限维基础：Young 不等式、Hölder 不等式、
Cauchy–Schwarz 不等式和 Minkowski 不等式。索引集合是任意类型 `ι`，求和范围由
`Finset ι` 指定，因此既覆盖长度为 `n` 的实向量，也覆盖任意有限标号族。

这里的实幂 `x ^ p` 在 `p : ℝ` 时是实数幂；绝对值保证底数非负。共轭指数条件由
`Real.HolderConjugate p q` 表达，它封装 `p,q>1` 与 `1/p+1/q=1`。
-/

namespace SandronesLibrary.Analysis.FiniteInequalities

open Finset

variable {ι : Type*}

/-- **Young 不等式**：若 `p,q` 共轭，则
`ab ≤ |a|ᵖ/p + |b|ᑫ/q`。

> **Entry**: analysis.inequalities.young
@isnad1 id=le.1h4v.s6.016c2a14f436 from=translated src=- shape=1ab21e32 vocab=164f695a
-/
theorem young (a b : ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ |a| ^ p / p + |b| ^ q / q := by
  exact Real.young_inequality a b hpq

/-- **有限和 Hölder 不等式**：乘积绝对值之和不超过两个共轭幂范数之积。

> **Entry**: analysis.inequalities.holder-finite
@isnad1 id=le.1h6v.s7.f2231e9ddb5b from=translated src=- shape=16086264 vocab=d0472ec9
-/
theorem holder (s : Finset ι) (f g : ι → ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, |f i * g i| ≤
      (∑ i ∈ s, |f i| ^ p) ^ (1 / p) * (∑ i ∈ s, |g i| ^ q) ^ (1 / q) := by
  simpa [abs_mul] using
    (Real.inner_le_Lp_mul_Lq s (fun i => |f i|) (fun i => |g i|) hpq)

/-- **Cauchy–Schwarz 不等式（平方形式）**：有限实数族的内积平方不超过两边平方和
之积。平方形式不需要引入平方根，也不会丢失内积可能为负的信息。

> **Entry**: analysis.inequalities.cauchy-schwarz
@isnad1 id=le.0h4v.s6.2e77ef96ecfd from=translated src=- shape=0578f47e vocab=7e23ce03
-/
theorem cauchy_schwarz_sq (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤
      (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  exact Finset.sum_mul_sq_le_sq_mul_sq s f g

/-- **有限和 Minkowski 不等式**：当 `1 ≤ p` 时，有限实数族的 `ℓᵖ` 大小满足
三角不等式。

> **Entry**: analysis.inequalities.minkowski-finite
@isnad1 id=le.1h5v.s7.970f813e1ec5 from=translated src=- shape=1a5067e8 vocab=6981d80e
-/
theorem minkowski (s : Finset ι) (f g : ι → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, |f i + g i| ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, |f i| ^ p) ^ (1 / p) +
        (∑ i ∈ s, |g i| ^ p) ^ (1 / p) := by
  exact Real.Lp_add_le s f g hp

end SandronesLibrary.Analysis.FiniteInequalities
