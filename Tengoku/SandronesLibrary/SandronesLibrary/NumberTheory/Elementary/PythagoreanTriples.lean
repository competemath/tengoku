/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.NumberTheory.PythagoreanTriples
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 勾股数及其参数化

本文件当前条目：

- `number-theory.elementary.pythagorean-triples`：勾股三元组的构造、一般分类与本原规范分类。

公开接口先用课程语言定义勾股三元组和本原性；Mathlib 的打包谓词只在分类证明内部作为桥。
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- 整数三元组 `(x,y,z)` 是勾股三元组，若 `x²+y²=z²`。
> **Entry**: number-theory.elementary.pythagorean-triples-/
def IsPythagoreanTriple (x y z : ℤ) : Prop :=
  x ^ 2 + y ^ 2 = z ^ 2

/-- 勾股三元组是本原的，若两条直角边 `x,y` 互素。
> **Entry**: number-theory.elementary.pythagorean-triples-/
def IsPrimitivePythagoreanTriple (x y z : ℤ) : Prop :=
  IsPythagoreanTriple x y z ∧ Int.gcd x y = 1

/-- Euclid 参数公式总会产生勾股三元组：
`(m²-n²)² + (2mn)² = (m²+n²)²`。
> **Entry**: number-theory.elementary.pythagorean-triples
@isnad1 id=ispythag.0h2v.s6.ea3c7666e835 from=translated src=- shape=48f6fec3 vocab=1b25ecab
-/
theorem pythagorean_parameters_form_triple (m n : ℤ) :
    IsPythagoreanTriple (m ^ 2 - n ^ 2) (2 * m * n) (m ^ 2 + n ^ 2) := by
  unfold IsPythagoreanTriple
  ring

/-- **本原勾股数的规范参数化**：若 `x` 是奇数、`z>0`，则本原勾股三元组可写成
教材常用的定向公式 `x=m²-n², y=2mn, z=m²+n²`；参数互素、奇偶性相反，并规范化为
`m≥0`。本定理给出规范代表所需的全部证书。
> **Entry**: number-theory.elementary.pythagorean-triples
@isnad1 id=ex.3h3v.s8.d2480589681f from=translated src=- shape=fd9f13bb vocab=819ddc54
-/
theorem primitivePythagorean_classification {x y z : ℤ}
    (h : IsPrimitivePythagoreanTriple x y z) (hx : x % 2 = 1) (hz : 0 < z) :
    ∃ m n : ℤ,
      x = m ^ 2 - n ^ 2 ∧
        y = 2 * m * n ∧
          z = m ^ 2 + n ^ 2 ∧
            Int.gcd m n = 1 ∧
              (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m := by
  rcases h with ⟨htrip, hgcd⟩
  have hmathlib : PythagoreanTriple x y z := by
    simpa [IsPythagoreanTriple, PythagoreanTriple, pow_two] using htrip
  exact hmathlib.coprime_classification' hgcd hx hz

/-- **所有整数勾股三元组的参数化**：允许公共倍数 `k`、交换两条直角边以及斜边符号。
因此该陈述同时覆盖非本原三元组、零三元组和负整数坐标。
> **Entry**: number-theory.elementary.pythagorean-triples
@isnad1 id=iff.0h3v.s8.1a9313904420 from=translated src=- shape=d5c43f86 vocab=67aa14d4
-/
theorem pythagorean_classification {x y z : ℤ} :
    IsPythagoreanTriple x y z ↔
      ∃ k m n : ℤ,
        (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
            x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
          (z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)) := by
  simpa [IsPythagoreanTriple, PythagoreanTriple, pow_two] using
    (PythagoreanTriple.classification (x := x) (y := y) (z := z))

end SandronesLibrary.NumberTheory.Elementary
