/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.OrthonormalBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hilbert 空间之间的酉算子

本文件把酉算子直接承载为 `LinearIsometryEquiv`：它同时记录线性、等距与双射。对于实 Hilbert
空间，这也是正交算子的无限维形式；其逆连续线性映射等于伴随。本文件不另造 `UnitaryOperator`。
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace
open scoped InnerProduct

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- 酉算子保持内积。

> **Entry**: functional-analysis.hilbert.unitary
@isnad1 id=eq.0h5v.s8.5c207c996365 from=translated src=- shape=bdd79b59 vocab=daf69966
-/
theorem unitary_inner_map_map (u : E ≃ₗᵢ[ℝ] F) (x y : E) :
    inner ℝ (u x) (u y) = inner ℝ x y := by
  exact u.inner_map_map x y

/-- 酉算子保持范数。
@isnad1 id=eq.0h4v.s8.3f131ba7e486 from=translated src=- shape=00f8b0dc vocab=a2498c69
-/
theorem unitary_norm_map (u : E ≃ₗᵢ[ℝ] F) (x : E) : ‖u x‖ = ‖x‖ := by
  exact u.norm_map x

/-- 酉算子的伴随就是其逆算子。
@isnad1 id=eq.0h3v.s11.bcc8201099f5 from=translated src=- shape=39beeff1 vocab=7befab1e
-/
theorem unitary_adjoint_eq_inverse [BanachSpace E] [BanachSpace F] (u : E ≃ₗᵢ[ℝ] F) :
    ContinuousLinearMap.adjoint (u : E →L[ℝ] F) = (u.symm : F →L[ℝ] E) := by
  exact u.adjoint_eq_symm

/-- 两个酉算子的复合仍由酉等距等价承载。
@isnad1 id=eq.0h6v.s9.b7f6036f6a26 from=translated src=- shape=8d95aa49 vocab=55d1a493
-/
theorem unitary_trans_apply (u : E ≃ₗᵢ[ℝ] F) (v : F ≃ₗᵢ[ℝ] G) (x : E) :
    (u.trans v) x = v (u x) := by
  rfl

end SandronesLibrary.FunctionalAnalysis
