/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Probability.ConditionalExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 条件期望的塔式性质

若 `m₁ ≤ m₂ ≤ m₀`，先按较丰富的信息 `m₂` 取条件期望，再按较粗的信息 `m₁` 取条件期望，
与直接按 `m₁` 取条件期望相同。这就是条件期望的塔式性质；等式自然成立于几乎处处意义下。

> **Entry**: probability.conditional-expectation.tower
-/

namespace SandronesLibrary.Probability

open MeasureTheory
open scoped ProbabilityTheory

/-- 塔式性质：`m₁ ≤ m₂` 时，`E[E[X|m₂]|m₁] = E[X|m₁]` a.e.
@isnad1 id=eventual.2h7v.s6.d85b3c19b927 from=translated src=- shape=692cb280 vocab=e248ee67
-/
theorem conditionalExpectation_tower
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m₁ m₂ m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀} {X : Ω → E}
    (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    [SigmaFinite (@Measure.trim Ω m₂ m₀ μ hm₂)] :
    μ[μ[X | m₂] | m₁] =ᵐ[μ] μ[X | m₁] :=
  condExp_condExp_of_le hm₁₂ hm₂

end SandronesLibrary.Probability
