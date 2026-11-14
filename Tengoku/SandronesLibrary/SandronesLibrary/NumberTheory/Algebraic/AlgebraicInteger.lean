/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.RingTheory.IntegralClosure.Algebra.Basic
import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed
import Tengoku.Seed.Algebra.GCDMonoid.IntegrallyClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 代数整数与整闭包

本文件给出 N2.2 的教材接口。教材中，环 `R` 的扩张 `A` 里的元素 `x` 称为**整**（integral），
如果它是某个首一 `R`-系数多项式的零点；全体整元素构成 `R` 在 `A` 中的**整闭包**
（integral closure），并且对加、减、乘封闭，因此是一个子环。当 `R = ℤ`、`A` 为数域时，
整元素就是**代数整数**。

公开承载全部采用 Mathlib 的 `IsIntegral`、`integralClosure`、`IsIntegralClosure` 与
`IsIntegrallyClosed`，它们与教材定义逐字一致；本文件只补上展开、桥和教材结论，不复制同构定义。

## 本文件条目

* `number-theory.algebraic.algebraic-integer`
-/

namespace SandronesLibrary.NumberTheory.Algebraic

open Polynomial

/-- **整元素的刻画：首一多项式零点。** 元素 `x : A` 在 `R` 上整，当且仅当存在首一多项式
`p : R[X]` 使得 `p` 在 `x` 处取值为零。

这就是教材对「整元素 / 代数整数」的定义本身：右端是可直接操作的判据，左端 `IsIntegral R x`
是 Mathlib 正式承载。两个命题按定义相等。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem isIntegral_iff_monic {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {x : A} :
    IsIntegral R x ↔
      ∃ p : R[X], p.Monic ∧ Polynomial.eval₂ (algebraMap R A) x p = 0 :=
  Iff.rfl

/-- **整闭包的成员刻画。** `x` 属于整闭包 `integralClosure R A` 当且仅当 `x` 在 `R` 上整。

整闭包在 Lean 中是一个 `Subalgebra R A`（子代数），本定理把「子代数的成员关系」和
「整元素谓词」这两个公开接口连接起来，是使用整闭包的入口桥。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem isIntegral_iff_mem_integralClosure {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} :
    x ∈ integralClosure R A ↔ IsIntegral R x :=
  mem_integralClosure_iff R A

/-- **基环元素的像是整的。** 对任意 `x : R`，它在 `A` 中的像 `algebraMap R A x` 是整的：
它是以 `X - C x` 为零点的首一多项式零点。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem algebraMap_isIntegral {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {x : R} :
    IsIntegral R (algebraMap R A x) :=
  _root_.isIntegral_algebraMap

/-- **整数在任意 `R`-代数中是整的。** 整数 `n` 在 `A` 中的像是整元素；取 `R = ℤ` 时，
这表示整数都是代数整数。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem intCast_isIntegral {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (n : ℤ) :
    IsIntegral R (n : A) :=
  _root_.isIntegral_intCast n

/-- **整元素对加法封闭。** 两个整元素之和仍是整元素，这是整闭包构成子环的关键一步。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem isIntegral_add {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {x y : A}
    (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x + y) :=
  hx.add hy

/-- **整元素对乘法封闭。** 两个整元素之积仍是整元素，与加法封闭一起说明整元素集合是子环。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem isIntegral_mul {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {x y : A}
    (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x * y) :=
  hx.mul hy

/-- **整元素对取负封闭。** 与加法、乘法封闭合并，整元素的加群结构成立。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem isIntegral_neg {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {x : A}
    (hx : IsIntegral R x) : IsIntegral R (-x) :=
  hx.neg

/-- **整元素对减法封闭。** 这是「整闭包是子环」所需减法封闭的直接形式。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem isIntegral_sub {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {x y : A}
    (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x - y) :=
  hx.sub hy

/-- **`ℤ` 是整闭的。** 整数环包含其分式域 `ℚ` 中所有在 `ℤ` 上整的元素；等价地说，
`ℤ` 在 `ℚ` 中的整闭包就是 `ℤ` 自身。

这是「唯一分解整环（更一般地 GCD 整环）是整闭的」的实例。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem int_isIntegrallyClosed : IsIntegrallyClosed ℤ :=
  inferInstance

/-- **有理代数整数定理：`ℚ` 中的代数整数只能是整数。** 有理数 `q` 在 `ℤ` 上整，当且仅当
`q` 是某个整数在 `ℚ` 中的像。

证明思路：由 `int_isIntegrallyClosed`，`ℚ` 中在 `ℤ` 上整的元素必须来自 `algebraMap ℤ ℚ`；
反向由 `isIntegral_intCast` 给出。教材里「有理数若是代数整数则必为整数」的精确形式即此。

> **Entry**: number-theory.algebraic.algebraic-integer-/
theorem isIntegral_rat_iff (q : ℚ) : IsIntegral ℤ q ↔ ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := ℤ) (K := ℚ) h
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, rfl⟩
    simpa using _root_.isIntegral_intCast (R := ℤ) (B := ℚ) n

end SandronesLibrary.NumberTheory.Algebraic
