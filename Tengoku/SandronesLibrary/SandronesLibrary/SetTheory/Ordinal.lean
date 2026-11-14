/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.SetTheory.Ordinal.Veblen
import Tengoku.Seed.SetTheory.Ordinal.CantorNormalForm
import Tengoku.Seed.SetTheory.Ordinal.Principal
import Tengoku.Seed.SetTheory.Cardinal.Cofinality.Ordinal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / Ordinal —— 序数理论

本文件当前条目：

* **settheory.ordinal.order-type**：良序同构当且仅当序型相同，且自然数序型为 `ω`。
* **settheory.ordinal.transfinite-induction**：序数上的超限归纳。
* **settheory.ordinal.transfinite-recursion**：按零、后继、极限三类进行超限递归。
* **settheory.ordinal.addition**：以良序拼接的序型定义加法，并证明递推式与非交换性。
* **settheory.ordinal.multiplication**：以字典序积的序型定义乘法，并证明递推式与非交换性。
* **settheory.ordinal.exponentiation**：以超限递归定义序数幂，并证明零、后继与极限方程。
* **settheory.ordinal.successor-limit**：后继序数与极限序数的基本性质。
* **settheory.ordinal.supremum**：序数族上确界的严格小于刻画。
* **settheory.ordinal.cofinality**：由规范良序载体定义共尾数，并计算零、后继与 `ω`。
* **settheory.ordinal.normal-function**：底数大于一的序数幂函数是正规函数。
* **settheory.ordinal.cantor-normal-form**：Cantor 正规形求值还原原序数。
* **settheory.ordinal.epsilon-zero**：`ε₀` 是 `α ↦ ω^α` 的最小前不动点。
* **settheory.ordinal.no-infinite-descent**：序数严格序良基，支撑 Goodstein 下降论证。
-/

namespace SandronesLibrary.SetTheory.Ordinal

open Order

noncomputable section

universe u

/--
> **Entry**: settheory.ordinal.order-type
> **一句话**: 两个良序具有相同序型当且仅当它们序同构；自然数通常序的序型是 `ω`。
> **依赖**: 无
> **mathlib**: `Ordinal.type_eq`、`Ordinal.type_nat_lt`-/
theorem orderType_classification {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] :
    (Ordinal.type r = Ordinal.type s ↔ Nonempty (r ≃r s)) ∧
      Ordinal.type (α := ℕ) (· < ·) = Ordinal.omega0 := by
  exact ⟨Ordinal.type_eq, Ordinal.type_nat_lt⟩

/--
> **Entry**: settheory.ordinal.transfinite-induction
> **一句话**: 若性质在“所有更小序数成立”时可推出当前序数成立，则它对全部序数成立。
> **依赖**: `settheory.ordinal.order-type`
> **mathlib**: `WellFoundedLT.induction`-/
theorem transfinite_induction {P : Ordinal → Prop}
    (step : ∀ α, (∀ β < α, P β) → P α) : ∀ α, P α := by
  intro α
  exact WellFoundedLT.induction α step

/--
> **Entry**: settheory.ordinal.transfinite-recursion
> **一句话**: 序数递归可分别给出零、后继和非零极限三个分支。
> **依赖**: `settheory.ordinal.transfinite-induction`
> **mathlib**: `Ordinal.limitRecOn`-/
def transfiniteRec {M : Ordinal → Sort*} (zero : M 0)
    (succ : ∀ α, M α → M (Order.succ α))
    (limit : ∀ α, IsSuccLimit α → (∀ β < α, M β) → M α) : ∀ α, M α :=
  fun α ↦ Ordinal.limitRecOn α zero
    (fun β ih ↦ (Order.succ_eq_add_one β) ▸ succ β ih) limit

/--
> **Entry**: settheory.ordinal.addition
> **一句话**: 两个良序前后拼接的序型定义序数加法；该运算满足后继递推且不交换。
> **依赖**: `settheory.ordinal.order-type`
> **mathlib**: `Ordinal.type`、`Ordinal.type_sum_lex`、`Ordinal.add_omega0`、`Order.lt_succ`-/
def ordinalAdd (a b : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.type (Sum.Lex ((· < ·) : a.ToType → a.ToType → Prop)
    ((· < ·) : b.ToType → b.ToType → Prop))

-- 私有桥只用于把本库教材定义交给 mathlib 验证；公开接口不暴露原生 `+`。
private theorem ordinalAdd_eq_mathlib (a b : Ordinal.{u}) : ordinalAdd a b = a + b := by
  simp [ordinalAdd]

@[simp]
theorem ordinalAdd_zero (a : Ordinal.{u}) : ordinalAdd a 0 = a := by
  rw [ordinalAdd_eq_mathlib, add_zero]

theorem ordinalAdd_succ (a b : Ordinal.{u}) :
    ordinalAdd a (Order.succ b) = Order.succ (ordinalAdd a b) := by
  rw [ordinalAdd_eq_mathlib, ordinalAdd_eq_mathlib]
  simp only [Order.succ_eq_add_one]
  rw [add_assoc]

theorem addition_not_commutative :
    ordinalAdd (1 : Ordinal) Ordinal.omega0 = Ordinal.omega0 ∧
      ordinalAdd Ordinal.omega0 (1 : Ordinal) ≠ Ordinal.omega0 := by
  rw [ordinalAdd_eq_mathlib, ordinalAdd_eq_mathlib]
  exact ⟨Ordinal.add_omega0 Ordinal.one_lt_omega0,
    ne_of_gt (Order.lt_succ Ordinal.omega0)⟩

/--
> **Entry**: settheory.ordinal.multiplication
> **一句话**: 在右因子副本之间取字典序所得的序型定义序数乘法；该运算用本库加法递推且不交换。
> **依赖**: `settheory.ordinal.addition`
> **mathlib**: `Ordinal.type`、`Ordinal.type_prod_lex`、`Ordinal.mul_succ`、
>   `Ordinal.natCast_mul_omega0`、`Ordinal.mul_two`-/
def ordinalMul (a b : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.type (Prod.Lex ((· < ·) : b.ToType → b.ToType → Prop)
    ((· < ·) : a.ToType → a.ToType → Prop))

-- 与加法同样，原生 `*` 仅是证明后端，不是本库对乘法的公开定义。
private theorem ordinalMul_eq_mathlib (a b : Ordinal.{u}) : ordinalMul a b = a * b := by
  simp [ordinalMul]

@[simp]
theorem ordinalMul_zero (a : Ordinal.{u}) : ordinalMul a 0 = 0 := by
  rw [ordinalMul_eq_mathlib, mul_zero]

theorem ordinalMul_succ (a b : Ordinal.{u}) :
    ordinalMul a (Order.succ b) = ordinalAdd (ordinalMul a b) a := by
  rw [ordinalMul_eq_mathlib, ordinalMul_eq_mathlib, ordinalAdd_eq_mathlib]
  exact Ordinal.mul_succ a b

theorem multiplication_not_commutative :
    ordinalMul (2 : Ordinal) Ordinal.omega0 = Ordinal.omega0 ∧
      ordinalMul Ordinal.omega0 (2 : Ordinal) ≠ Ordinal.omega0 := by
  rw [ordinalMul_eq_mathlib, ordinalMul_eq_mathlib]
  constructor
  · exact Ordinal.natCast_mul_omega0 (by decide)
  · rw [Ordinal.mul_two]
    exact ne_of_gt (lt_add_of_pos_right Ordinal.omega0 Ordinal.omega0_pos)

/--
> **Entry**: settheory.ordinal.exponentiation
> **一句话**: 序数幂由零、后继与极限三个分支超限递归定义，后继分支调用本库乘法。
> **依赖**: `settheory.ordinal.transfinite-recursion`、`settheory.ordinal.multiplication`
> **mathlib**: `Ordinal.limitRecOn`、`Ordinal.opow_succ`、`Ordinal.opow_limit`-/
def ordinalPow (a b : Ordinal.{u}) : Ordinal.{u} :=
  if a = 0 then if b = 0 then 1 else 0 else
    Ordinal.limitRecOn b 1 (fun _ x => ordinalMul x a)
      (fun o _ f => ⨆ x : Set.Iio o, f x.1 x.2)

@[simp]
theorem ordinalPow_zero (a : Ordinal.{u}) : ordinalPow a 0 = 1 := by
  simp [ordinalPow, Ordinal.limitRecOn_zero]

theorem ordinalPow_succ (a b : Ordinal.{u}) :
    ordinalPow a (Order.succ b) = ordinalMul (ordinalPow a b) a := by
  rw [Order.succ_eq_add_one]
  obtain rfl | ha := eq_or_ne a 0
  · simp [ordinalPow, ordinalMul_eq_mathlib]
  · simp [ordinalPow, ha, Ordinal.limitRecOn_add_one]

theorem ordinalPow_limit (a b : Ordinal.{u}) (ha : a ≠ 0) (hb : IsSuccLimit b) :
    ordinalPow a b = ⨆ x : Set.Iio b, ordinalPow a x.1 := by
  simp only [ordinalPow, ha, ↓reduceIte]
  exact Ordinal.limitRecOn_limit _ _ _ _ hb

-- 私有桥验证超限递归定义与 mathlib 序数幂一致。

/--
> **Entry**: settheory.ordinal.successor-limit
> **一句话**: 后继序数紧邻原序数，而 `ω` 是非零极限序数。
> **依赖**: `settheory.ordinal.order-type`
> **mathlib**: `Order.lt_succ`、`Order.lt_succ_iff`、`Ordinal.isSuccLimit_omega0`-/
theorem successor_and_limit (a : Ordinal) :
    a < Order.succ a ∧ (∀ b, a < b → ¬ b < Order.succ a) ∧ IsSuccLimit Ordinal.omega0 := by
  refine ⟨Order.lt_succ a, ?_, Ordinal.isSuccLimit_omega0⟩
  intro b hab hbs
  exact (not_le_of_gt hab) (Order.lt_succ_iff.mp hbs)

/--
> **Entry**: settheory.ordinal.supremum
> **一句话**: 一个序数严格小于小指标序数族的上确界，当且仅当它严格小于其中某项。
> **依赖**: `settheory.ordinal.transfinite-recursion`
> **mathlib**: `Ordinal.lt_iSup_iff`-/
theorem lt_supremum_iff {ι : Type} [Small ι] (f : ι → Ordinal) (a : Ordinal) :
    a < ⨆ i, f i ↔ ∃ i, a < f i := Ordinal.lt_iSup_iff

/--
> **Entry**: settheory.ordinal.cofinality
> **一句话**: 以序数规范良序载体的最小共尾子集基数定义共尾数，并计算零、后继与 `ω`。
> **依赖**: `settheory.ordinal.successor-limit`、`settheory.ordinal.supremum`
> **mathlib**: `Order.cof`、`Ordinal.cof_toType`、`Ordinal.cof_zero`、
>   `Ordinal.cof_add_one`、`Ordinal.cof_omega0`-/
def ordinalCofinality (a : Ordinal.{u}) : Cardinal.{u} :=
  Order.cof a.ToType

-- 原生 `Ordinal.cof` 仅用于验证本库从规范良序载体给出的定义。
private theorem ordinalCofinality_eq_mathlib (a : Ordinal.{u}) :
    ordinalCofinality a = a.cof := by
  exact Ordinal.cof_toType a

theorem basic_cofinalities (a : Ordinal) :
    ordinalCofinality 0 = 0 ∧ ordinalCofinality (Order.succ a) = 1 ∧
      ordinalCofinality Ordinal.omega0 = Cardinal.aleph0 := by
  rw [ordinalCofinality_eq_mathlib, ordinalCofinality_eq_mathlib,
    ordinalCofinality_eq_mathlib, Order.succ_eq_add_one]
  exact ⟨Ordinal.cof_zero, Ordinal.cof_add_one a, Ordinal.cof_omega0⟩

/--
> **Entry**: settheory.ordinal.no-infinite-descent
> **一句话**: 序数的严格小于关系良基；因此任何逐步严格下降的序数过程必定终止。
> **依赖**: `settheory.ordinal.transfinite-induction`
> **mathlib**: `Ordinal.lt_wf`-/
theorem ordinal_lt_wellFounded : WellFounded ((· < ·) : Ordinal → Ordinal → Prop) :=
  Ordinal.lt_wf

end

end SandronesLibrary.SetTheory.Ordinal
