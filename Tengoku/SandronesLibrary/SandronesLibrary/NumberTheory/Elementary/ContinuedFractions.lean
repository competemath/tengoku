/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.NumberTheory.DiophantineApproximation.ContinuedFractions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 连分数与有理逼近

本文件从初等数论教材的角度介绍实数的简单连分数，提供以下接口：

* 实数的简单连分数及其渐近分数；
* 按分母大小比较的最佳有理逼近，以及有限候选集中的最佳逼近；
* Legendre 判别准则：误差足够小的有理数一定是某个渐近分数。

这里直接复用 Mathlib 的渐近分数与 Legendre 判别准则接口，因为它们与本节采用的教材语义一致。
不过，Mathlib 目前尚未提供教材中常见的“每个连分数渐近分数都是最佳逼近”定理。因此下文会明确
区分“误差足够小则为渐近分数”和“渐近分数具有最佳性”这两个方向，不会把尚缺的后一个方向写成
已经证明的结论。

## 本文件条目

* `number-theory.elementary.continued-fraction-convergent`
* `number-theory.elementary.continued-fraction-recursion`
* `number-theory.elementary.best-rational-approximation`
* `number-theory.elementary.finite-best-approximation`
* `number-theory.elementary.legendre-criterion`
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- 实数 `ξ` 的简单连分数的第 `n` 个渐近分数。

渐近分数是一个有理数：把连分数在第 `n` 层截断后求值，就得到这个有理逼近。本定义采用
Mathlib 的 `Real.convergent` 作为正式承载，但对本课程公开的仍是取值于 `ℚ` 的初等接口，而不是
广义连分数的内部表示。

> **Entry**: number-theory.elementary.continued-fraction-convergent-/
noncomputable def continuedFractionConvergent (ξ : ℝ) (n : ℕ) : ℚ :=
  Real.convergent ξ n

/-- 第零个渐近分数就是 `ξ` 的整数部分 `⌊ξ⌋`。这是连分数递归展开的起点。
@isnad1 id=eq.0h1v.s4.9c006c7ead20 from=translated src=- shape=c81d1e4e vocab=8286103b
-/
@[simp]
theorem continuedFractionConvergent_zero (ξ : ℝ) :
    continuedFractionConvergent ξ 0 = (⌊ξ⌋ : ℤ) := by
  exact Real.convergent_zero ξ

/-- 连分数的递归步骤：先从 `ξ` 中去掉整数部分，再对剩余的小数部分取倒数并继续展开。

因此，第 `n + 1` 个渐近分数等于整数部分，加上“倒数后所得实数的第 `n` 个渐近分数”的倒数。
这个公式把连分数算法的一步直接翻译成了有理数等式。

> **Entry**: number-theory.elementary.continued-fraction-recursion
@isnad1 id=eq.0h2v.s5.223f66f03765 from=translated src=- shape=c7185958 vocab=32d5eb8b
-/
@[simp]
theorem continuedFractionConvergent_succ (ξ : ℝ) (n : ℕ) :
    continuedFractionConvergent ξ (n + 1) =
      (⌊ξ⌋ : ℤ) + (continuedFractionConvergent (Int.fract ξ)⁻¹ n)⁻¹ := by
  exact Real.convergent_succ ξ n

/-- 用有理数 `q` 逼近实数 `ξ` 时的绝对误差，即 `|ξ - q|`。-/
def rationalApproximationError (ξ : ℝ) (q : ℚ) : ℝ :=
  |ξ - (q : ℝ)|

/-- 若所有分母不超过 `q.den` 的有理数都不能比 `q` 更接近 `ξ`，就称 `q` 是 `ξ` 的最佳有理逼近。

这里用 `≤` 比较误差，因此允许两个候选者并列最佳。这个定义只谈“分母预算内谁的误差最小”，
并不预先假定 `q` 来自连分数。这样处理是为了诚实地区分最佳逼近的教材定义与当前已经形式化的
连分数定理；Mathlib 尚未给出“每个渐近分数都满足此定义”的一般结论。

> **Entry**: number-theory.elementary.best-rational-approximation-/
def IsBestRationalApproximation (ξ : ℝ) (q : ℚ) : Prop :=
  ∀ r : ℚ, r.den ≤ q.den →
    rationalApproximationError ξ q ≤ rationalApproximationError ξ r

/-- 若被逼近的实数本来就是有理数 `q`，那么用 `q` 自身逼近时误差为零，所以它自动是最佳逼近。
@isnad1 id=isbestra.0h1v.s3.2c9322502995 from=translated src=- shape=c811f807 vocab=4d28dc91
-/
theorem exact_rational_isBestApproximation (q : ℚ) :
    IsBestRationalApproximation (q : ℝ) q := by
  intro r _
  simp [rationalApproximationError]

/-- `q` 属于有限候选集 `s`，并且它的逼近误差不大于 `s` 中任何候选者的误差。-/
def IsBestApproximationIn (ξ : ℝ) (s : Finset ℚ) (q : ℚ) : Prop :=
  q ∈ s ∧ ∀ r ∈ s, rationalApproximationError ξ q ≤ rationalApproximationError ξ r

/-- 每个非空的有限有理候选集都存在误差最小的元素，也就是该候选集中的最佳逼近。

这里的结论只是有限集合取最小值，并没有声称所得有理数是按所有分母受限候选比较的全局最佳逼近。

> **Entry**: number-theory.elementary.finite-best-approximation
@isnad1 id=ex.1h2v.s4.527c8c6aac9f from=translated src=- shape=1354c80a vocab=6c478ea8
-/
theorem exists_bestApproximationIn (ξ : ℝ) {s : Finset ℚ} (hs : s.Nonempty) :
    ∃ q, IsBestApproximationIn ξ s q := by
  obtain ⟨q, hqs, hq⟩ := s.exists_min_image (rationalApproximationError ξ) hs
  exact ⟨q, hqs, hq⟩

/-- Legendre 判别准则使用的定量条件：逼近误差严格小于 `1 / (2 * 分母²)`。-/
def IsLegendreApproximation (ξ : ℝ) (q : ℚ) : Prop :=
  rationalApproximationError ξ q < 1 / (2 * (q.den : ℝ) ^ 2)

/-- **Legendre 判别准则。** 若有理数 `q` 对 `ξ` 的逼近满足教材中的阈值
`|ξ - q| < 1 / (2 q.den²)`，那么 `q` 一定会出现在 `ξ` 的连分数渐近分数序列中。

这是一个充分条件：它从“小误差”推出“是渐近分数”。它不是反方向的陈述，也没有证明每个渐近
分数都是最佳有理逼近。

> **Entry**: number-theory.elementary.legendre-criterion
@isnad1 id=ex.1h2v.s4.a3dd288bdb93 from=translated src=- shape=fbccddcd vocab=dc8691f9
-/
theorem legendreApproximation_is_convergent {ξ : ℝ} {q : ℚ}
    (hq : IsLegendreApproximation ξ q) :
    ∃ n, q = continuedFractionConvergent ξ n := by
  exact Real.exists_rat_eq_convergent hq

end SandronesLibrary.NumberTheory.Elementary
