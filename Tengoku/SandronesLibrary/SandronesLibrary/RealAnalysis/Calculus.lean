/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / Calculus —— 微积分基本定理（数学分析第二学期 R5）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **real-analysis.calculus.ftc**（微积分基本定理：∫f' = f(b) - f(a)）✅。
* **real-analysis.calculus.ftc-differentiate**（变上限积分可导，导数 = 被积函数）✅。

> **语言说明**：实分析阶段（§Phase5）mathlib 的 `IntervalIntegral`/`HasDerivAt` 等
> **教材结构可直接出现在签名**。一元积分学用测度积分承载。
-/

namespace SandronesLibrary

namespace RealAnalysis.Calculus

open MeasureTheory
open scoped Interval Topology

/-- **微积分基本定理（第二形式，FTC-2）**：f 在 [a,b] 上可导且 f' 可积，则
  ∫ₐᵇ f'(x) dx = f(b) - f(a)。 
> **Entry**: real-analysis.calculus.ftc-/
theorem ftc_2 {a b : ℝ} {f : ℝ → ℝ} {f' : ℝ → ℝ}
    (hderiv : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- **微积分基本定理（第一形式，FTC-1）**：f 在 [a,b] 上可积且在 b 连续，
  则变上限积分 u ↦ ∫ₐᵘ f 在 b 可导，导数 = f(b)。 
> **Entry**: real-analysis.calculus.ftc-differentiate-/
theorem ftc_1_right {a b : ℝ} {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasStrictDerivAt (fun u : ℝ => ∫ x in a..u, f x) (f b) b := by
  exact intervalIntegral.integral_hasStrictDerivAt_right hf hmeas hb

end RealAnalysis.Calculus

end SandronesLibrary
