/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.NumberTheory.Pell

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pell 方程

本文件用初等数论中熟悉的整数坐标 `(x, y)` 来陈述正 Pell 方程
`x² - d y² = 1`。公开接口只要求读者理解整数平方和二元不定方程；Mathlib 中二次环与单位元的
打包表示仅在证明内部使用。

Mathlib 已经证明正 Pell 方程解的存在性与分类。但它明确没有完成这些解与 `√d` 的连分数之间的
联系，也没有处理负 Pell 方程 `x² - d y² = -1`。因此，本文件只陈述已经获得 Lean 证明的正方程
结果，不把这两个后续方向写成已完成内容。

## 本文件条目

* `number-theory.elementary.pell-equation`
* `number-theory.elementary.pell-composition`
* `number-theory.elementary.pell-positive-existence`
* `number-theory.elementary.pell-fundamental-solution`
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- 若存在整数 `z` 使 `z² = d`，就称整数 `d` 是整数平方数。

这里把教材中的存在量词直接写成定义，以便后面的“`d` 不是平方数”具有明确的整数坐标含义。

> **Entry**: number-theory.elementary.pell-positive-existence-/
def IsIntegerSquare (d : ℤ) : Prop :=
  ∃ z : ℤ, z ^ 2 = d

/-- 上述整数坐标定义与 Mathlib 的乘法谓词 `IsSquare` 等价。

这条桥说明后续存在性定理可以安全复用 Mathlib：在整数上，“某数等于一个整数的平方”与
“某数可写成某元素自乘”表达的是同一个概念。
@isnad1 id=iff.0h1v.s3.57dcf0829633 from=translated src=- shape=1efddc98 vocab=2ead6f8a
-/
theorem isIntegerSquare_iff_isSquare (d : ℤ) : IsIntegerSquare d ↔ IsSquare d := by
  simpa [IsIntegerSquare, eq_comm] using (isSquare_iff_exists_sq d).symm

/-- 正 Pell 方程 `x² - d y² = 1` 的一个整数解。

结构中的 `x`、`y` 是整数坐标，`equation` 则保存它们确实满足方程的证明。因此，一个
`PellSolution d` 不只是数对，还携带了该数对是参数 `d` 的 Pell 解这一事实。

> **Entry**: number-theory.elementary.pell-equation-/
structure PellSolution (d : ℤ) where
  x : ℤ
  y : ℤ
  equation : x ^ 2 - d * y ^ 2 = 1

/-- 平凡 Pell 解 `(1, 0)`；它对任意整数参数 `d` 都满足 `1² - d · 0² = 1`。-/
def PellSolution.one (d : ℤ) : PellSolution d :=
  ⟨1, 0, by ring⟩

/-- 同一个 Pell 方程的两个解的 Brahmagupta 复合。

若 `a = (x₁, y₁)`、`b = (x₂, y₂)`，则复合解为
`(x₁x₂ + d y₁y₂, x₁y₂ + y₁x₂)`。恒等式
`(x₁² - d y₁²)(x₂² - d y₂²) = x² - d y²` 表明两个右端为 `1` 的解复合后仍然是解。

> **Entry**: number-theory.elementary.pell-composition-/
def PellSolution.comp (a b : PellSolution d) : PellSolution d where
  x := a.x * b.x + d * (a.y * b.y)
  y := a.x * b.y + a.y * b.x
  equation := by
    calc
      (a.x * b.x + d * (a.y * b.y)) ^ 2 -
          d * (a.x * b.y + a.y * b.x) ^ 2 =
        (a.x ^ 2 - d * a.y ^ 2) * (b.x ^ 2 - d * b.y ^ 2) := by ring
      _ = 1 := by rw [a.equation, b.equation, one_mul]

/-- 展开 Brahmagupta 复合所得解的第一坐标。
@isnad1 id=eq.0h3v.s5.1938678b01fb from=translated src=- shape=c77414c9 vocab=575ca1a3
-/
@[simp]
theorem pell_comp_x (a b : PellSolution d) :
    (a.comp b).x = a.x * b.x + d * (a.y * b.y) := by
  rfl

/-- 展开 Brahmagupta 复合所得解的第二坐标。
@isnad1 id=eq.0h3v.s5.e1e5f71c69fc from=translated src=- shape=38ab1e56 vocab=575ca1a3
-/
@[simp]
theorem pell_comp_y (a b : PellSolution d) :
    (a.comp b).y = a.x * b.y + a.y * b.x := by
  rfl

/-- 若 `d` 为正整数且不是平方数，则正 Pell 方程存在满足 `x > 1`、`y > 0` 的解。

这排除了对所有 `d` 都存在的平凡解 `(1, 0)`，所以结论给出的确实是非平凡正解。此处的非平方
条件采用 Mathlib 的 `IsSquare` 表述。

> **Entry**: number-theory.elementary.pell-positive-existence
@isnad1 id=ex.2h1v.s5.b2857efb36bd from=translated src=- shape=dfdaa293 vocab=49bcf430
-/
theorem exists_positive_pellSolution {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    ∃ a : PellSolution d, 1 < a.x ∧ 0 < a.y := by
  obtain ⟨a, hax, hay⟩ := Pell.Solution₁.exists_pos_of_not_isSquare hd hns
  exact ⟨⟨a.x, a.y, a.prop⟩, hax, hay⟩

/-- 若正整数参数不是本文件坐标定义下的平方数，则它具有一个非平凡正 Pell 解。

这一定理与上一条数学内容相同，只是通过 `isIntegerSquare_iff_isSquare` 把假设改写成读者更直观的
“不存在整数 `z` 使 `z² = d`”。
@isnad1 id=ex.2h1v.s5.5c28d482c686 from=translated src=- shape=b22a71cc vocab=d4e78c67
-/
theorem exists_positive_pellSolution_of_not_integerSquare {d : ℤ} (hd : 0 < d)
    (hns : ¬IsIntegerSquare d) :
    ∃ a : PellSolution d, 1 < a.x ∧ 0 < a.y := by
  apply exists_positive_pellSolution hd
  rwa [← isIntegerSquare_iff_isSquare]

/-- 基本 Pell 解是一个正的非平凡解，并且它的第一坐标在所有 `x > 1` 的解中最小。

具体地说，要求 `a.x > 1`、`a.y > 0`，并要求任意另一个满足 `b.x > 1` 的解都有
`a.x ≤ b.x`。这里允许最小第一坐标对应多个表示；定义没有额外声称唯一性。

> **Entry**: number-theory.elementary.pell-fundamental-solution-/
def IsFundamentalPellSolution (a : PellSolution d) : Prop :=
  1 < a.x ∧ 0 < a.y ∧
    ∀ b : PellSolution d, 1 < b.x → a.x ≤ b.x

/-- 每个正的非平方整数参数都存在一个用整数坐标表示的基本 Pell 解。

Mathlib 还会把其打包表示中的全部解分类为基本解的带符号整数次幂。本条目的公开接口刻意只使用
整数坐标与 Brahmagupta 复合，因此这里不重述那一群论化分类，也不暗示已经在当前接口上证明了
“所有解都是基本解的幂”。

> **Entry**: number-theory.elementary.pell-fundamental-solution
@isnad1 id=ex.2h1v.s4.7dac8acd016d from=translated src=- shape=fb808488 vocab=b29bad2b
-/
theorem exists_fundamentalPellSolution {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    ∃ a : PellSolution d, IsFundamentalPellSolution a := by
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hd hns
  refine ⟨⟨a.x, a.y, a.prop⟩, ha.1, ha.2.1, ?_⟩
  intro b hb
  let b' : Pell.Solution₁ d := Pell.Solution₁.mk b.x b.y b.equation
  have hb' : 1 < b'.x := by simpa [b'] using hb
  simpa [b'] using ha.2.2 hb'

/-- 若正整数参数不是本文件定义的整数平方数，则它存在基本 Pell 解。

这是上一条存在性定理的教材表述版本；证明通过平方概念的等价桥把假设转换给 Mathlib。
@isnad1 id=ex.2h1v.s4.3a519eb0e2b2 from=translated src=- shape=8ff852d8 vocab=639ddad8
-/
theorem exists_fundamentalPellSolution_of_not_integerSquare {d : ℤ} (hd : 0 < d)
    (hns : ¬IsIntegerSquare d) :
    ∃ a : PellSolution d, IsFundamentalPellSolution a := by
  apply exists_fundamentalPellSolution hd
  rwa [← isIntegerSquare_iff_isSquare]

end SandronesLibrary.NumberTheory.Elementary
