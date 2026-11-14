/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.RieszRepresentation
import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hilbert 空间上有界算子的伴随

本文件直接以 Mathlib 的 `ContinuousLinearMap.adjoint` 承载伴随算子。对
`A : E →L[ℝ] F`，其伴随是反向的连续线性映射 `A† : F →L[ℝ] E`，由内积转移公式唯一刻画。
这里不另造伴随结构，只公开教材所需的刻画、范数、对合与复合性质。
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace
open scoped InnerProduct

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BanachSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [BanachSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [BanachSpace G]

/-- 伴随算子的教材刻画：`B` 是 `A` 的伴随，当且仅当它把 `A` 从内积左边移到右边。

> **Entry**: functional-analysis.hilbert.adjoint-/
theorem eq_adjoint_iff_inner_transfer (A : E →L[ℝ] F) (B : F →L[ℝ] E) :
    B = A† ↔ ∀ x y, inner ℝ (A x) y = inner ℝ x (B y) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  constructor <;> intro h x y
  · simpa [real_inner_comm] using (h y x).symm
  · simpa [real_inner_comm] using (h y x).symm

/-- Mathlib 的正式伴随满足内积转移公式。
@isnad1 id=eq.0h5v.s11.fa2573ecf65c from=translated src=- shape=9c055578 vocab=e9cb67aa
-/
theorem adjoint_inner_transfer (A : E →L[ℝ] F) (x : E) (y : F) :
    inner ℝ (A x) y = inner ℝ x ((A†) y) := by
  exact (ContinuousLinearMap.adjoint_inner_right A x y).symm

/-- 取两次伴随回到原算子。
@isnad1 id=eq.0h3v.s12.723509feaef8 from=translated src=- shape=d5991c5e vocab=11983c79
-/
theorem adjoint_involutive (A : E →L[ℝ] F) : A†† = A := by
  exact ContinuousLinearMap.adjoint_adjoint A

/-- 伴随保持算子范数。
@isnad1 id=eq.0h3v.s11.f21f8e1b1633 from=translated src=- shape=ba512061 vocab=fcd140fd
-/
theorem norm_adjoint_eq (A : E →L[ℝ] F) : ‖A†‖ = ‖A‖ := by
  exact (ContinuousLinearMap.adjoint : (E →L[ℝ] F) ≃ₗᵢ⋆[ℝ] F →L[ℝ] E).norm_map A

/-- 复合的伴随按相反次序复合。
@isnad1 id=eq.0h5v.s13.da5055d2cfdb from=translated src=- shape=7046fd05 vocab=3bd3d333
-/
theorem adjoint_comp_reverse (A : F →L[ℝ] G) (B : E →L[ℝ] F) :
    (A ∘L B)† = B† ∘L A† := by
  exact ContinuousLinearMap.adjoint_comp A B

end SandronesLibrary.FunctionalAnalysis
