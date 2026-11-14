/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.AdjointOperator
import Tengoku.Seed.Analysis.InnerProductSpace.l2Space

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hilbert 基与 Parseval 恒等式

无限维 Hilbert 空间中的“正交规范基”不仅要求向量两两正交且范数为一，还要求其线性张成稠密。
Mathlib 的 `HilbertBasis ι ℝ E` 直接把空间等距识别为 `ℓ²(ι, ℝ)`，并同时承载正交规范性、完备性、
Fourier 展开和 Parseval 恒等式。本文件只公开这些教材刻画，不另造基结构。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {ι E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Hilbert 基是一族正交规范向量。

> **Entry**: functional-analysis.hilbert.orthonormal-basis
@isnad1 id=orthonor.0h3v.s5.f3348030b633 from=translated src=- shape=3c0c5a51 vocab=a05019f9
-/
theorem hilbertBasis_orthonormal (b : HilbertBasis ι ℝ E) : Orthonormal ℝ b := by
  exact b.orthonormal

/-- Hilbert 基的线性张成在整个空间中稠密；这是无限维“基”的完备性条件。
@isnad1 id=eq.0h3v.s7.4e342947a2cb from=translated src=- shape=df467159 vocab=038d0491
-/
theorem hilbertBasis_dense_span (b : HilbertBasis ι ℝ E) :
    (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤ := by
  exact b.dense_span

/-- 每个向量都是其 Hilbert 基 Fourier 系数所给级数的和。
@isnad1 id=hassum.0h4v.s7.9c56db38a3fb from=translated src=- shape=883cb6a8 vocab=a1f02967
-/
theorem hilbertBasis_hasSum_fourier (b : HilbertBasis ι ℝ E) (x : E) :
    HasSum (fun i ↦ inner ℝ (b i) x • b i) x := by
  simpa only [HilbertBasis.repr_apply_apply] using b.hasSum_repr x

/-- Parseval 恒等式的内积形式：同一向量的 Fourier 系数乘积之和等于其自内积。
@isnad1 id=eq.0h4v.s6.68130e2a750b from=translated src=- shape=bb406c3f vocab=b094a77e
-/
theorem hilbertBasis_parseval (b : HilbertBasis ι ℝ E) (x : E) :
    ∑' i, inner ℝ x (b i) * inner ℝ (b i) x = inner ℝ x x := by
  exact b.tsum_inner_mul_inner x x

end SandronesLibrary.FunctionalAnalysis
