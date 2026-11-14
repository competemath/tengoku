/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.AnnihilatorClosure
import Tengoku.Seed.Analysis.Normed.Module.DoubleDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 典范双对偶嵌入与自反性

向量 `x` 通过求值送到双对偶：它把每个连续线性泛函 `f` 送到 `f x`。Mathlib 已将
这张图打包为 `NormedSpace.inclusionInDoubleDual`，并将其等距版本打包为
`NormedSpace.inclusionInDoubleDualLi`。本文件直接展开这些承载，并以典范嵌入的满射性表达
Banach 空间的自反性，不另建平行结构。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 典范双对偶嵌入就是求值映射。

> **Entry**: functional-analysis.bidual.reflexive
@isnad1 id=eq.0h3v.s12.f2c8aa0179b4 from=translated src=- shape=82f3d928 vocab=e76370af
-/
theorem bidual_evaluation (x : E) (f : StrongDual ℝ E) :
    NormedSpace.inclusionInDoubleDual ℝ E x f = f x := by
  exact NormedSpace.dual_def ℝ E x f

/-- 典范双对偶嵌入保持范数。
@isnad1 id=eq.0h2v.s12.2651370d7c63 from=translated src=- shape=8f4d00b6 vocab=9c633349
-/
theorem norm_bidual_evaluation (x : E) :
    ‖NormedSpace.inclusionInDoubleDual ℝ E x‖ = ‖x‖ := by
  exact (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map x

/-- 连续对偶能够分离点，因此典范双对偶映射是单射。
@isnad1 id=injectiv.0h1v.s12.c8f9170d4731 from=translated src=- shape=a2835d3f vocab=1692673a
-/
theorem bidual_evaluation_injective :
    Function.Injective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  exact (NormedSpace.inclusionInDoubleDualLi ℝ).injective

/-- 自反性的教材展开：典范嵌入满射，当且仅当每个双对偶元都是在某个向量上求值。
@isnad1 id=iff.0h1v.s12.787c36a99609 from=translated src=- shape=df62483e vocab=524661dd
-/
theorem reflexive_iff_every_bidual_is_evaluation :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) ↔
      ∀ Φ : StrongDual ℝ (StrongDual ℝ E), ∃ x : E, ∀ f : StrongDual ℝ E, Φ f = f x := by
  constructor
  · intro h Φ
    obtain ⟨x, rfl⟩ := h Φ
    exact ⟨x, fun f ↦ bidual_evaluation x f⟩
  · intro h Φ
    obtain ⟨x, hx⟩ := h Φ
    refine ⟨x, ContinuousLinearMap.ext ?_⟩
    intro f
    exact (bidual_evaluation x f).trans (hx f).symm

/-- 在自反空间中，每个双对偶元由唯一向量表示。
@isnad1 id=existsun.1h2v.s12.570adf20b6f0 from=translated src=- shape=5c1865c3 vocab=b140fe34
-/
theorem existsUnique_bidual_evaluation
    (hE : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (Φ : StrongDual ℝ (StrongDual ℝ E)) :
    ∃! x : E, ∀ f : StrongDual ℝ E, Φ f = f x := by
  obtain ⟨x, hx⟩ := (reflexive_iff_every_bidual_is_evaluation (E := E)).mp hE Φ
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply bidual_evaluation_injective (E := E)
  apply ContinuousLinearMap.ext
  intro f
  rw [bidual_evaluation, bidual_evaluation, ← hx f, ← hy f]

end SandronesLibrary.FunctionalAnalysis
