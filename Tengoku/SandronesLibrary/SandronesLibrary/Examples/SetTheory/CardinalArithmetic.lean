/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.CardinalTheory
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Cardinal
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Data.Fintype.EquivFin
import Tengoku.Seed.Data.Fintype.Sum
import Tengoku.Seed.Data.Fintype.Prod
import Tengoku.Seed.Data.Fintype.Pi
import Tengoku.Seed.Logic.Equiv.Fin.Basic
import Tengoku.Seed.Logic.Equiv.Nat
import Tengoku.Seed.Data.Set.Countable
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 集合论：有限基数加乘幂的计算与基数算术的两个反例

本文件为集合论 ST2 条目 `settheory.cardinal.addition`、`settheory.cardinal.multiplication`、
`settheory.cardinal.exponentiation`、`settheory.cardinal.finite-set`、
`settheory.cardinal.countable-def` 补齐可核对的例子：先给出有限基数加、乘、幂的显式等势见证与
真计算，再给出「可数 ∪ 有限仍可数」的具体集合，最后用两个 Lean 定理钉死两条常见误推：
基数相等不等于集合相等；无限基数的加法没有自然数那样的消去律。

> **Entry**: examples.settheory.cardinal-arithmetic
-/

noncomputable section

namespace SandronesLibrary.Examples.SetTheory.CardinalArithmetic

open SandronesLibrary.SetTheory.CardinalTheory

/-! ## 具体有限类型与有限基数计算 -/

/-- 两个元素与三个元素的不交并，即基数加法 `2 + 3` 的具体承载。-/
abbrev TwoSumThree : Type := CardinalSum (Fin 2) (Fin 3)

/-- 两个元素与三个元素的笛卡尔积，即基数乘法 `2 * 3` 的具体承载。-/
abbrev TwoProdThree : Type := CardinalProduct (Fin 2) (Fin 3)

/-- 从两个位置到三个取值的函数空间，即基数幂 `3 ^ 2` 的具体承载。-/
abbrev ThreePowTwo : Type := CardinalPower (Fin 3) (Fin 2)

/-- **定义展开**：本库的加法承载 `CardinalSum (Fin 2) (Fin 3)` 按定义就是 `Fin 2 ⊕ Fin 3`。
@isnad1 id=eq.0h0v.s4.7cbca1cd84fb from=translated src=- shape=5362e087 vocab=a1a6c61a
-/
theorem twoSumThree_eq_sum : TwoSumThree = (Fin 2 ⊕ Fin 3 : Type) := rfl

/-- **定义展开**：本库的乘法承载 `CardinalProduct (Fin 2) (Fin 3)` 按定义就是 `Fin 2 × Fin 3`。
@isnad1 id=eq.0h0v.s4.a97c89c64a19 from=translated src=- shape=5362e087 vocab=c272d36c
-/
theorem twoProdThree_eq_prod : TwoProdThree = (Fin 2 × Fin 3 : Type) := rfl

/-- **定义展开**：本库的幂承载 `CardinalPower (Fin 3) (Fin 2)` 按定义就是函数空间 `Fin 2 → Fin 3`。
@isnad1 id=eq.0h0v.s4.804aae41b5a8 from=translated src=- shape=8709cc18 vocab=174c33a7
-/
theorem threePowTwo_eq_arrow : ThreePowTwo = (Fin 2 → Fin 3 : Type) := rfl

/-- **有限基数加法真计算**：`|Fin 2 ⊕ Fin 3| = 5`。由 `twoSumThree_eq_sum`，这算的就是
本库加法承载 `TwoSumThree` 的元素个数。
@isnad1 id=eq.0h0v.s5.ccaa0aed28f3 from=translated src=- shape=0f32de20 vocab=622ea836
-/
theorem card_twoSumThree : Fintype.card (Fin 2 ⊕ Fin 3) = 5 := by
  decide

/-- **有限基数乘法真计算**：`|Fin 2 × Fin 3| = 6`。由 `twoProdThree_eq_prod`，这算的就是
本库乘法承载 `TwoProdThree` 的元素个数。
@isnad1 id=eq.0h0v.s5.19fd32d2a3de from=translated src=- shape=0f32de20 vocab=649328ce
-/
theorem card_twoProdThree : Fintype.card (Fin 2 × Fin 3) = 6 := by
  decide

/-- **有限基数幂真计算**：`|Fin 2 → Fin 3| = 3 ^ 2 = 9`。由 `threePowTwo_eq_arrow`，这算的就是
本库幂承载 `ThreePowTwo` 的元素个数。
@isnad1 id=eq.0h0v.s6.e55acbbfbd05 from=translated src=- shape=e9ab2fc9 vocab=dc2e8de2
-/
theorem card_threePowTwo : Fintype.card (Fin 2 → Fin 3) = 9 := by
  decide

/-! ## 显式等势见证 -/

/-- **基数加法的显式见证**：`Fin 2 ⊕ Fin 3 ≃ Fin 5`，由 mathlib 的 `finSumFinEquiv` 直接给出。
@isnad1 id=equinume.0h0v.s3.e732d86c4252 from=translated src=- shape=9ae76a30 vocab=7d6a770d
-/
theorem equinumerous_twoSumThree_fin5 : Equinumerous TwoSumThree (Fin 5) :=
  ⟨finSumFinEquiv⟩

/-- **基数乘法的显式见证**：`Fin 2 × Fin 3 ≃ Fin 6`，由 mathlib 的 `finProdFinEquiv` 直接给出。
@isnad1 id=equinume.0h0v.s3.aeafee1f3005 from=translated src=- shape=9ae76a30 vocab=d693ecdf
-/
theorem equinumerous_twoProdThree_fin6 : Equinumerous TwoProdThree (Fin 6) :=
  ⟨finProdFinEquiv⟩

/-- **基数幂的显式见证**：`(Fin 2 → Fin 3) ≃ Fin 3 × Fin 3 ≃ Fin 9`，
即函数先按两个位置拆成有序对，再沿 `finProdFinEquiv` 编码。
@isnad1 id=equinume.0h0v.s3.5489263ab2f2 from=translated src=- shape=9ae76a30 vocab=f9db1985
-/
theorem equinumerous_threePowTwo_fin9 : Equinumerous ThreePowTwo (Fin 9) :=
  ⟨(finTwoArrowEquiv (Fin 3)).trans finProdFinEquiv⟩

/-- **它是有限集的实例**：`Fin 2 ⊕ Fin 3` 与 `Fin 5` 等势，故按本库定义有限。
@isnad1 id=finiteby.0h0v.s1.a06c6c3fa606 from=translated src=- shape=49959d42 vocab=7527f26d
-/
theorem finiteByEnumeration_twoSumThree : FiniteByEnumeration TwoSumThree :=
  ⟨5, equinumerous_twoSumThree_fin5⟩

/-- **它是有限集的实例**：`Fin 2 × Fin 3` 与 `Fin 6` 等势，故按本库定义有限。
@isnad1 id=finiteby.0h0v.s1.f345b7adb859 from=translated src=- shape=49959d42 vocab=0ae4ba81
-/
theorem finiteByEnumeration_twoProdThree : FiniteByEnumeration TwoProdThree :=
  ⟨6, equinumerous_twoProdThree_fin6⟩

/-- **它是有限集的实例**：`Fin 2 → Fin 3` 与 `Fin 9` 等势，故按本库定义有限。
@isnad1 id=finiteby.0h0v.s1.42a1d8669e0f from=translated src=- shape=49959d42 vocab=e0465afa
-/
theorem finiteByEnumeration_threePowTwo : FiniteByEnumeration ThreePowTwo :=
  ⟨9, equinumerous_threePowTwo_fin9⟩

/-! ## 反例一：基数相等不等于集合相等 -/

/-- 具体集合 `{0,1} ⊆ ℕ`，写成 `i ↦ i`（`i : Fin 2`）的像。-/
def twoElemSet : Set ℕ :=
  Set.range (fun i : Fin 2 => (i.1 : ℕ))

/-- 具体集合 `{2,3} ⊆ ℕ`，写成 `i ↦ i + 2`（`i : Fin 2`）的像。-/
def twoElemSetShifted : Set ℕ :=
  Set.range (fun i : Fin 2 => (i.1 + 2 : ℕ))

/-- `{0,1}` 到 `Fin 2` 的显式双射：把元素本身当作它的编号。-/
def twoElemSetEquivFin2 : twoElemSet ≃ Fin 2 where
  toFun x := ⟨x.1, by
    obtain ⟨i, hi⟩ := x.2
    have hi' : (i.1 : ℕ) = x.1 := hi
    rw [← hi']
    exact i.2⟩
  invFun i := ⟨(i.1 : ℕ), ⟨i, rfl⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Fin.ext rfl

/-- `{2,3}` 到 `Fin 2` 的显式双射：把元素减二当作它的编号。-/
def twoElemSetShiftedEquivFin2 : twoElemSetShifted ≃ Fin 2 where
  toFun x := ⟨x.1 - 2, by
    obtain ⟨i, hi⟩ := x.2
    have hi' : (i.1 : ℕ) + 2 = x.1 := hi
    rw [← hi', Nat.add_sub_cancel]
    exact i.2⟩
  invFun i := ⟨(i.1 + 2 : ℕ), ⟨i, rfl⟩⟩
  left_inv x := Subtype.ext (by
    obtain ⟨i, hi⟩ := x.2
    have hi' : (i.1 : ℕ) + 2 = x.1 := hi
    change x.1 - 2 + 2 = x.1
    rw [← hi', Nat.add_sub_cancel])
  right_inv _ := Fin.ext (by simp)

/-- `{0,1}` 与 `Fin 2` 等势，即它的基数是 `2`。
@isnad1 id=equinume.0h0v.s3.556c4c3f9cf0 from=translated src=- shape=f74745da vocab=9a038489
-/
theorem twoElemSet_equinumerous_fin2 : Equinumerous twoElemSet (Fin 2) :=
  ⟨twoElemSetEquivFin2⟩

/-- `{2,3}` 与 `Fin 2` 等势，即它的基数也是 `2`。
@isnad1 id=equinume.0h0v.s3.9fef6f413fb6 from=translated src=- shape=f74745da vocab=9529b9e7
-/
theorem twoElemSetShifted_equinumerous_fin2 : Equinumerous twoElemSetShifted (Fin 2) :=
  ⟨twoElemSetShiftedEquivFin2⟩

/-- `{0,1}` 按本库定义有限，大小是 `2`。
@isnad1 id=finiteby.0h0v.s2.0136a918a4ab from=translated src=- shape=049cd614 vocab=fccc6bcf
-/
theorem finiteByEnumeration_twoElemSet : FiniteByEnumeration twoElemSet :=
  ⟨2, twoElemSet_equinumerous_fin2⟩

/-- `{2,3}` 按本库定义有限，大小是 `2`。
@isnad1 id=finiteby.0h0v.s2.7fbcaa5ba715 from=translated src=- shape=049cd614 vocab=65fb4151
-/
theorem finiteByEnumeration_twoElemSetShifted : FiniteByEnumeration twoElemSetShifted :=
  ⟨2, twoElemSetShifted_equinumerous_fin2⟩

/-- **反例：基数相等不等于集合相等**。`{0,1}` 与 `{2,3}` 都与 `Fin 2` 等势，因此基数相等；
但 `0` 属于前者而不属于后者，两个集合不相等。这否定了「基数相等的两个集合相等」这一误推：
等势只保证存在双射，不保证元素本身相同。
@isnad1 id=and.0h0v.s4.1709b0160a49 from=translated src=- shape=775d0e7e vocab=4d46c346
-/
theorem cardinal_equinumerous_not_set_eq :
    Equinumerous twoElemSet (Fin 2) ∧ Equinumerous twoElemSetShifted (Fin 2) ∧
      twoElemSet ≠ twoElemSetShifted := by
  refine ⟨twoElemSet_equinumerous_fin2, twoElemSetShifted_equinumerous_fin2, ?_⟩
  intro h
  have h0 : (0 : ℕ) ∈ twoElemSetShifted := by
    rw [← h]
    exact ⟨⟨0, by norm_num⟩, rfl⟩
  obtain ⟨i, hi⟩ := h0
  have hi' : (i.1 : ℕ) + 2 = 0 := hi
  omega

/-! ## 正例：可数集与有限集的运算 -/

/-- 偶数集 `{0,2,4,…} ⊆ ℕ`，写成 `k ↦ 2 * k` 的像。-/
def evenNats : Set ℕ :=
  Set.range (fun k : ℕ => 2 * k)

/-- 单点集 `{1} ⊆ ℕ`，一个具体的有限集。-/
def oneSet : Set ℕ :=
  {1}

/-- 偶数集可数：它是 `ℕ` 在单射 `k ↦ 2 * k` 下的像。
@isnad1 id=countabl.0h0v.s1.ef02aec34675 from=translated src=- shape=25b03439 vocab=d69c4605
-/
theorem evenNats_countable : evenNats.Countable :=
  Set.countable_range _

/-- 单点集 `{1}` 可数：有限集都可数。
@isnad1 id=countabl.0h0v.s1.24e88c791f0c from=translated src=- shape=25b03439 vocab=6350d6c6
-/
theorem oneSet_countable : oneSet.Countable :=
  (Set.finite_singleton 1).countable

/-- **正例：可数 ∪ 有限仍可数**。偶数集与单点集 `{1}` 的并仍可数，
虽然它不再是偶数集本身（`1` 是新增的奇数）。
@isnad1 id=countabl.0h0v.s3.eff3ed8033f8 from=translated src=- shape=a8ad5ddb vocab=61063455
-/
theorem countable_union_finite : (evenNats ∪ oneSet).Countable :=
  Set.Countable.union evenNats_countable oneSet_countable

/-- **可数定义展开**：把上一条的结论按本库 `countable-def` 的刻画读出来，
就是存在一个从 `evenNats ∪ {1}` 到 `ℕ` 的单射（即一份不重复的编号）。
@isnad1 id=ex.0h0v.s5.ad3d90fcc251 from=translated src=- shape=e650a484 vocab=e4d73d0a
-/
theorem countable_union_finite_injection :
    ∃ f : ↥(evenNats ∪ oneSet) → ℕ, Function.Injective f :=
  (SandronesLibrary.SetTheory.Cardinal.countable_iff_injective_nat _).mp countable_union_finite

/-! ## 反例二：无限基数的加法没有自然数那样的消去律 -/

/-- **无限基数加法不增长**：`ℕ ⊕ ℕ` 与 `ℕ` 等势（mathlib 的 `Equiv.natSumNatEquivNat`
把左副本编成偶数 `2 * n`、右副本编成奇数 `2 * n + 1`），即 `ℵ₀ + ℵ₀ = ℵ₀`。
@isnad1 id=equinume.0h0v.s2.6c84b0dbfa8f from=translated src=- shape=0b0a4f6e vocab=9d46180b
-/
theorem equinumerous_natSumNat : Equinumerous (CardinalSum ℕ ℕ) ℕ :=
  ⟨Equiv.natSumNatEquivNat⟩

/-- **反例：无限基数算术不能照搬自然数消去律**。前件 `Equinumerous (ℕ ⊕ ℕ) ℕ` 成立
（无限加自身不改变基数），但后件 `Equinumerous ℕ (Fin 0)` 为假（`ℕ` 非空而 `Fin 0` 空）。
因此从 `Equinumerous (CardinalSum x y) x` 不能推出 `Equinumerous y (Fin 0)`：
在无限情形，`x + y = x` 里的 `y` 不必为 `0`。
@isnad1 id=and.0h0v.s3.2f563aca106f from=translated src=- shape=28935095 vocab=13a056b0
-/
theorem infinite_addition_cancellation_fails :
    Equinumerous (CardinalSum ℕ ℕ) ℕ ∧ ¬ Equinumerous ℕ (Fin 0) :=
  ⟨equinumerous_natSumNat, fun h => by
    rcases h with ⟨e⟩
    exact Fin.elim0 (e 0)⟩

/-- **对比：有限情形的消去律仍然成立**。`Fin 2 ⊕ Fin 3` 有 `5` 个元素，与 `Fin 2` 不等势，
所以「`x + y` 与 `x` 等势」在有限情形确实迫使 `y` 为空。反例二说明失效只发生在无限情形。
@isnad1 id=not.0h0v.s4.af3054fe8206 from=translated src=- shape=72f1e91f vocab=13a056b0
-/
theorem finite_addition_cancellation_holds :
    ¬ Equinumerous (CardinalSum (Fin 2) (Fin 3)) (Fin 2) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr (finSumFinEquiv.symm.trans e)
  simp only [Fintype.card_fin] at h
  omega

end SandronesLibrary.Examples.SetTheory.CardinalArithmetic
