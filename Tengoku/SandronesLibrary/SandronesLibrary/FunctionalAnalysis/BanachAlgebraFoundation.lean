/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Analysis.Normed.Algebra.Unitization
import Tengoku.Seed.Analysis.Normed.Ring.Units
import Tengoku.Seed.Analysis.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 复 Banach 代数基础

Mathlib 不使用另一个 `BanachAlgebra` carrier：复 Banach 代数由 `NormedRing`、
`NormedAlgebra ℂ`、`CompleteSpace`（通常再带 `NormOneClass`）共同表达。本文件只提供课程命名的
几何级数、单位化与有界算子代数桥，不复制这些结构。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A] [NormOneClass A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A] in
/-- Banach 代数乘法的次乘性由 `NormedRing` 直接承载。

> **Entry**: functional-analysis.banach-algebra.foundation-/
theorem banachAlgebra_norm_mul_le (a b : A) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
  norm_mul_le a b

omit [NormedAlgebra ℂ A] [NormOneClass A] in
/-- 范数小于一的元素的 Neumann 级数收敛到 `1-a` 的环论逆元。-/
theorem banachAlgebra_hasSum_geometric_inverse (a : A) (ha : ‖a‖ < 1) :
    HasSum (fun n : ℕ ↦ a ^ n) (Ring.inverse (1 - a)) :=
  hasSum_geom_series_inverse a ha

omit [NormedAlgebra ℂ A] [NormOneClass A] in
/-- Neumann 级数判据：若 `‖a‖<1`，则 `1-a` 可逆。-/
theorem banachAlgebra_one_sub_isUnit (a : A) (ha : ‖a‖ < 1) :
    IsUnit (1 - a) :=
  isUnit_one_sub_of_norm_lt_one ha

section Unitization

variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace ℂ B]
  [SMulCommClass ℂ B B] [IsScalarTower ℂ B B]
  [CompleteSpace B] [RegularNormedAlgebra ℂ B]

omit [NormedSpace ℂ B] [SMulCommClass ℂ B B] [IsScalarTower ℂ B B]
  [RegularNormedAlgebra ℂ B] in
/-- Mathlib 的单位化 `Unitization ℂ B` 仍是完备的复赋范代数。-/
theorem complexUnitization_complete : CompleteSpace (Unitization ℂ B) :=
  inferInstance

omit [CompleteSpace B] in
/-- 非幺 Banach 代数到其单位化的典范嵌入是等距映射。-/
theorem complexUnitization_inclusion_isometry :
    Isometry ((↑) : B → Unitization ℂ B) :=
  Unitization.isometry_inr

omit [CompleteSpace B] in
@[simp]
theorem norm_complexUnitization_inclusion (b : B) :
    ‖(b : Unitization ℂ B)‖ = ‖b‖ :=
  Unitization.norm_inr b

end Unitization

section OperatorAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

omit [Nontrivial E] in
/-- 有界算子代数中的 Neumann 级数。这个实例桥是后续算子谱与预解集的基础。-/
theorem operator_hasSum_geometric_inverse (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    HasSum (fun n : ℕ ↦ T ^ n) (Ring.inverse (1 - T)) :=
  hasSum_geom_series_inverse T hT

omit [Nontrivial E] in
/-- 范数小于一的有界算子 `T` 使 `I-T` 在有界算子代数中可逆。-/
theorem operator_one_sub_isUnit (T : E →L[ℂ] E) (hT : ‖T‖ < 1) :
    IsUnit (1 - T) :=
  isUnit_one_sub_of_norm_lt_one hT

end OperatorAlgebra

end SandronesLibrary.FunctionalAnalysis
