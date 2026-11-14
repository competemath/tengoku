/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Holomorphic
import Tengoku.Seed.Analysis.Complex.Liouville

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Liouville 定理

本文件以教材全纯接口陈述 Liouville 定理：有界整函数必为常值函数。
-/

namespace SandronesLibrary.ComplexAnalysis

/-- **Liouville 定理**：若复函数在整个复平面上全纯且范数全局有界，则它等于某个常数。

> **Entry**: complex-analysis.liouville
@isnad1 id=ex.2h1v.s5.d95e8da9f4fe from=translated src=- shape=fd2c1b7e vocab=1a497a70
-/
theorem liouville {f : ℂ → ℂ}
    (hf : HolomorphicOnTextbook f Set.univ)
    (hbounded : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C) :
    ∃ b : ℂ, ∀ z : ℂ, f z = b := by
  have hd : Differentiable ℂ f := by
    intro z
    exact complexDifferentiableAtTextbook_iff_differentiableAt.mp (hf z (Set.mem_univ z))
  obtain ⟨C, hC⟩ := hbounded
  apply hd.exists_const_forall_eq_of_bounded
  rw [isBounded_iff_forall_norm_le]
  exact ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩

/-- Liouville 定理的两点形式：有界整函数在任意两点取相同值。
@isnad1 id=eq.2h3v.s5.e848f5e45fd6 from=translated src=- shape=6f6a0b92 vocab=1a497a70
-/
theorem liouville_eq {f : ℂ → ℂ}
    (hf : HolomorphicOnTextbook f Set.univ)
    (hbounded : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C) (z w : ℂ) :
    f z = f w := by
  obtain ⟨b, hb⟩ := liouville hf hbounded
  rw [hb z, hb w]

end SandronesLibrary.ComplexAnalysis
