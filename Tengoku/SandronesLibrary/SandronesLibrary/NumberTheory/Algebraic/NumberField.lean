/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.NumberTheory.NumberField.Basic
import Tengoku.Seed.FieldTheory.PrimitiveElement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 数域与有限扩张

本文件给出 N2.1 的教材接口：数域是特征零且作为 `ℚ`-向量空间有限维的域。以下公开内容
全部以 Mathlib 的 `NumberField` 类作为正式承载，因为它的定义与教材中「`ℚ` 的有限扩张」
完全一致；本文件不再复制一份同构的定义，只补上教材常用的展开、刻画和上层使用方法。

* `numberField_iff` 把 `NumberField` 展开成「特征零 + 有限维」这一教材定义；
* `numberField_finiteDimensional`、`numberField_isAlgebraic` 给出有限维与代数性两条基本性质；
* `numberField_of_module_finite`、`numberField_of_subfield` 说明数域对有限扩张和子域封闭；
* `numberField_exists_primitive_element` 是有限可分扩张的单生成元定理在数域上的形式。

Mathlib 的 `NumberField` 就是本课程数域概念的语义一致正式承载；本文件没有桥，也没有
私有后端定义。

## 本文件条目

* `number-theory.algebraic.number-field`
-/

namespace SandronesLibrary.NumberTheory.Algebraic

/-- **数域的刻画。** 一个特征零的域是数域，当且仅当它作为 `ℚ`-向量空间有限维。

这就是教材「数域是 `ℚ` 的有限扩张」的 Lean 展开：左端 `NumberField K` 是 Mathlib 的正式
承载，右端把它的两个组成条件写成对读者可见的命题。`CharZero` 由假设给出，`Algebra ℚ K`
是特征零域上唯一的 `ℚ`-代数结构。

> **Entry**: number-theory.algebraic.number-field-/
theorem numberField_iff (K : Type*) [Field K] [CharZero K] :
    NumberField K ↔ FiniteDimensional ℚ K :=
  ⟨fun h => h.to_finiteDimensional, fun h => @NumberField.of_module_finite ℚ K _ _ _ _ h⟩

/-- **数域是有限维 `ℚ`-向量空间。** 这是数域定义的一半，也是「每个数域都是有限次扩张」
的直接形式。

> **Entry**: number-theory.algebraic.number-field-/
theorem numberField_finiteDimensional (K : Type*) [Field K] [NumberField K] :
    FiniteDimensional ℚ K :=
  inferInstance

/-- **数域中每个元素都是 `ℚ` 上的代数元。** 有限维蕴含代数性，因此数域中任意元素都满足一个
非零有理系数多项式方程；这是后面代数整数与极小多项式讨论的入口。

> **Entry**: number-theory.algebraic.number-field-/
theorem numberField_isAlgebraic (K : Type*) [Field K] [NumberField K] :
    Algebra.IsAlgebraic ℚ K :=
  NumberField.isAlgebraic K

/-- **数域的有限扩张仍是数域。** 若 `L` 是数域 `K` 上的有限扩张，则 `L` 也是数域：由塔性质，
`L` 在 `ℚ` 上有限维，且特征零。教材里「数域的任何有限扩张还是数域」即此。

> **Entry**: number-theory.algebraic.number-field-/
theorem numberField_of_module_finite (K L : Type*) [Field K] [Field L] [NumberField K]
    [Algebra K L] [Module.Finite K L] : NumberField L :=
  NumberField.of_module_finite K L

/-- **数域的子域仍是数域。** 子域继承特征零；又因为 `E ⊆ K` 且 `K` 在 `ℚ` 上有限维，
`E` 也在 `ℚ` 上有限维。

> **Entry**: number-theory.algebraic.number-field-/
theorem numberField_of_subfield (K : Type*) [Field K] [NumberField K] (E : Subfield K) :
    NumberField E :=
  NumberField.of_subfield E

/-- **单生成元定理（primitive element theorem）。** 数域 `K` 是 `ℚ` 的单扩张：存在 `α : K`
使得 `ℚ(α) = K`。这里用 `IntermediateField.adjoin ℚ {α} = ⊤` 表示「由 `α` 生成的中间域是
整个 `K`」。

这正是教材「有限可分扩张都是单扩张」在数域上的形式：特征零自动给出可分性。有限性假设由
`NumberField` 提供。

> **Entry**: number-theory.algebraic.number-field-/
theorem numberField_exists_primitive_element (K : Type*) [Field K] [NumberField K] :
    ∃ α : K, IntermediateField.adjoin ℚ ({α} : Set K) = ⊤ :=
  Field.exists_primitive_element ℚ K

end SandronesLibrary.NumberTheory.Algebraic
