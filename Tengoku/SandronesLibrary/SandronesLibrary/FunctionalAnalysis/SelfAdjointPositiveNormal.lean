/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.AdjointOperator
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.UnitaryOperator
import Tengoku.Seed.Analysis.InnerProductSpace.Positive
import Tengoku.Seed.Algebra.Star.Unitary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 有界自伴、正、正规与酉算子的关系

教材（Bühler–Salamon《Functional Analysis》第 5 章）在 Hilbert 空间上同时使用四类有界算子，
并用它们之间的蕴含关系组织后续的紧自伴谱理论。本文件不另造平行的算子类结构，而是把四类
概念直接承载为 Mathlib 的成熟接口，并补齐教材所需的相互关系和展开刻画。

设 `𝕜` 是 `RCLike`（`ℝ` 或 `ℂ`），`E` 是完备内积空间。本文研究 `E →L[𝕜] E` 上的算子。

- **自伴算子**：教材定义 `T = T*`，其中 `T*` 是伴随。Lean 正式承载是 Mathlib 的
  `IsSelfAdjoint T`（即 `star T = T`）。在 `E →L[𝕜] E` 上 `star T = T.adjoint`
  （`star_eq_adjoint`），因此 `IsSelfAdjoint T ↔ T.adjoint = T`，并且经
  `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric` 等价于内积对称性
  `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`。本库不重定义自伴。
- **正算子**：教材定义 `T = T*` 且 `∀ x, ⟪T x, x⟫ ≥ 0`。Lean 正式承载是 Mathlib 的
  `ContinuousLinearMap.IsPositive T`，其定义即“对称 + 二次型实部非负”
  （`isPositive_def'`／`isPositive_iff'`）。正算子是自伴算子的子类。
- **正规算子**：教材定义 `T T* = T* T`。Lean 正式承载是 Mathlib 的 `IsStarNormal T`，
  对 `E →L[𝕜] E` 展开为 `T.adjoint * T = T * T.adjoint`，并有等价的范数刻画
  `∀ x, ‖T x‖ = ‖T† x‖`（`isStarNormal_iff_norm_eq_adjoint`）。
- **酉算子**：教材定义等距满射；代数刻画是 `U* U = U U* = 1`。Lean 正式承载是
  Mathlib 的 `unitary (E →L[𝕜] E)` 子群（元素即满足 `U* U = U U* = 1` 的算子），
  它与线性等距等价 `E ≃ₗᵢ[𝕜] E` 通过 `Unitary.linearIsometryEquiv` 同构
  （`Unitary.inner_map_map`、`Unitary.norm_map` 给出等距性）。

本模块证明的“关系”链是：

`正算子 ⟹ 自伴算子 ⟹ 正规算子`，`酉算子 ⟹ 正规算子`，`酉算子 ⟹ 伴随 = 逆`，
以及“幂等算子：自伴 ⟺ 正规”。自伴、正规与酉三类算子都另有各自的范数／内积展开刻画。

**边界**：本模块只处理**有界**算子，使用 `CompleteSpace E`（Hilbert 空间意义下的完备性）；
不涉及无界算子（F7）、连续函数演算（F6.8）或谱测度（F6.9）。这里的 `IsPositive` 是
赋范空间算子上的二次型非负性，不是 `CStarAlgebra` 的正元素偏序；两者在 `E →L[𝕜] E` 上
一致，但本模块只使用前者。
-/

namespace SandronesLibrary.FunctionalAnalysis

open ContinuousLinearMap
open scoped InnerProduct ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-! ## 自伴算子 -/

/-- 自伴算子的内积刻画：`T` 自伴（即伴随等于自身，`T† = T`）当且仅当它可把内积中的 `T`
从一侧移到另一侧。

这是教材“`⟪T x, y⟫ = ⟪x, T y⟫`” 陈述对全部向量的精确量词展开；教材的 `T = T*` 即
`IsSelfAdjoint T`（在 `E →L[𝕜] E` 上 `star T = T†`）。

> **Entry**: functional-analysis.operator.selfadjoint-positive-normal-/
theorem isSelfAdjoint_iff_inner_symm (T : E →L[𝕜] E) :
    IsSelfAdjoint T ↔ ∀ x y : E, inner 𝕜 (T x) y = inner 𝕜 x (T y) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  exact ⟨fun h x y => h x y, fun h x y => h x y⟩

/-! ## 正算子 -/

/-- 正算子的等价刻画：正算子是自伴算子，且其二次型取非负值。

反向把“自伴 + 二次型非负”组装为正算子，正是教材对正算子的定义。-/
theorem isPositive_iff_selfAdjoint_inner_nonneg (T : E →L[𝕜] E) :
    T.IsPositive ↔ IsSelfAdjoint T ∧ ∀ x : E, 0 ≤ inner 𝕜 (T x) x :=
  isPositive_iff' T

/-- 正算子是自伴算子。-/
theorem positive_isSelfAdjoint {T : E →L[𝕜] E} (hT : T.IsPositive) : IsSelfAdjoint T :=
  hT.isSelfAdjoint

/-! ## 正规算子 -/

/-- 正规算子的交换刻画：`T` 正规当且仅当它与自己的伴随相乘可交换。-/
theorem isStarNormal_iff_adjoint_commute (T : E →L[𝕜] E) :
    IsStarNormal T ↔ T.adjoint * T = T * T.adjoint := by
  rw [isStarNormal_iff]
  constructor
  · intro h
    have hh : star T * T = T * star T := h.eq
    rwa [star_eq_adjoint] at hh
  · intro h
    have hh : star T * T = T * star T := by rwa [← star_eq_adjoint] at h
    exact hh

/-- 正规算子的范数刻画：`T` 正规当且仅当 `T` 与 `T†` 在每个向量上范数相同。-/
theorem isStarNormal_iff_norm_adjoint (T : E →L[𝕜] E) :
    IsStarNormal T ↔ ∀ x : E, ‖T x‖ = ‖T.adjoint x‖ :=
  isStarNormal_iff_norm_eq_adjoint

/-- 正规算子的核与伴随的核相同。-/
theorem isStarNormal_ker_adjoint {T : E →L[𝕜] E} (hT : IsStarNormal T) :
    T.adjoint.ker = T.ker :=
  hT.ker_adjoint_eq_ker

/-- 正规算子的值域与核正交（值域的正交补等于核）。-/
theorem isStarNormal_range_orthogonal_ker {T : E →L[𝕜] E} (hT : IsStarNormal T) :
    T.rangeᗮ = T.ker :=
  hT.orthogonal_range

/-- 自伴算子是正规算子。-/
theorem selfAdjoint_isStarNormal {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) : IsStarNormal T :=
  hT.isStarNormal

/-- 正算子是正规算子（经“正 ⟹ 自伴 ⟹ 正规”的关系链）。-/
theorem positive_isStarNormal {T : E →L[𝕜] E} (hT : T.IsPositive) : IsStarNormal T :=
  hT.isSelfAdjoint.isStarNormal

/-- 幂等算子：自伴当且仅当正规。

这是教材中正交投影与一般幂等算子区别的精确表述：在幂等性之外，
“自伴”与“正规”互相推出。-/
theorem idempotent_selfAdjoint_iff_isStarNormal {T : E →L[𝕜] E}
    (hT : IsIdempotentElem T) : IsSelfAdjoint T ↔ IsStarNormal T :=
  ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal hT

/-! ## 酉算子 -/

/-- 酉算子是正规算子。

酉算子满足 `U* U = U U* = 1`，因此 `U` 与 `U*` 交换；这是教材“酉 ⟹ 正规”的精确形式。-/
theorem unitary_isStarNormal {U : E →L[𝕜] E} (hU : U ∈ unitary (E →L[𝕜] E)) :
    IsStarNormal U :=
  isStarNormal_of_mem_unitary hU

/-- 酉算子的伴随等于它的逆（在 `unitary` 子群中）。-/
theorem unitary_adjoint_eq_inv (U : unitary (E →L[𝕜] E)) :
    (U : E →L[𝕜] E).adjoint = (U⁻¹ : unitary (E →L[𝕜] E)) := by
  rw [← star_eq_adjoint (U : E →L[𝕜] E)]
  exact congrArg (fun V : unitary (E →L[𝕜] E) => (V : E →L[𝕜] E)) (Unitary.star_eq_inv U)

/-- 自伴的酉算子是幂等的对合：`U * U = 1`。

这给出教材中“同时自伴且酉”的算子的精确含义。-/
theorem isSelfAdjoint_unitary_mul_self {U : E →L[𝕜] E}
    (hU : U ∈ unitary (E →L[𝕜] E)) (hU' : IsSelfAdjoint U) : U * U = 1 := by
  have h : U * star U = 1 := Unitary.mul_star_self_of_mem hU
  rwa [hU'.star_eq] at h

/-- 线性等距等价是酉算子：`E ≃ₗᵢ[𝕜] E` 的承载算子属于 `unitary (E →L[𝕜] E)`。

这把 F3.5 的 `LinearIsometryEquiv` 承载与本章的 `unitary` 子群显式连接起来，
说明两个接口描述的是同一类算子。-/
theorem linearIsometryEquiv_mem_unitary (e : E ≃ₗᵢ[𝕜] E) :
    (e : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := by
  have h := (Unitary.linearIsometryEquiv.symm e : unitary (E →L[𝕜] E)).property
  simpa using h

end SandronesLibrary.FunctionalAnalysis
