/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Computability.Primrec.List
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Order.Interval.Finset.Nat
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Googology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / PrimitiveRecursiveClass —— 原始递归函数类及其闭包

本文件把 Strict Recursion Theory 教材中的「原始递归函数类」冻结为 mathlib 的**教科书版**
多元函数类 `Nat.Primrec'`（`n` 元函数 `List.Vector ℕ n → ℕ`）。mathlib 的 `Nat.Primrec'` 正是
Odifreddi 教材意义的类：含零函数、后继与投影，并对复合与原始递归封闭；它还有一个到
一元配对形式 `Nat.Primrec` 的等价桥 `Nat.Primrec'.prim_iff`。

本文件不重造这套类，而是补上 ST3 下游要用的三条**派生闭包**：有界求和、有界求积与有限迭代，
并把本库既有的 `primitiveRecursion` 递归模板接入该类。所有公开结论都以 `Nat.Primrec'` 表述，
mathlib 的构造子 `comp`、`prec` 是正式闭包原则，不是证明后端替身。
-/

namespace SandronesLibrary.SetTheory.Googology

/-- `w.tail.tail` 作为向量值函数是原始递归的：它是同一向量的高两位投影。-/
private theorem primrec_tailTailVec {n : ℕ} :
    @Nat.Primrec'.Vec (n + 2) n (fun w : List.Vector ℕ (n + 2) => w.tail.tail) := by
  intro i
  refine (@Nat.Primrec'.get (n + 2) (Fin.succ (Fin.succ i))).of_eq ?_
  intro w
  simp

/-- 把 `f` 作用在「首项 + 尾部再尾部」的向量上仍是原始递归的。-/
private theorem primrec_compHeadTail {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : @Nat.Primrec' (n + 1) f) :
    @Nat.Primrec' (n + 2) (fun w : List.Vector ℕ (n + 2) => f (w.head ::ᵥ w.tail.tail)) :=
  hf.comp' (Nat.Primrec'.cons (Nat.Primrec'.head (n := n + 1)) primrec_tailTailVec)

/-- 递归步骤 `IH + f y`：累加前一步结果与新一项。-/
private theorem primrec_stepSum {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : @Nat.Primrec' (n + 1) f) :
    @Nat.Primrec' (n + 2) (fun w : List.Vector ℕ (n + 2) =>
      w.tail.head + f (w.head ::ᵥ w.tail.tail)) :=
  Nat.Primrec'.add.comp₂ _ (Nat.Primrec'.tail (@Nat.Primrec'.head (n := n)))
    (primrec_compHeadTail hf)

/--
> **Entry**: settheory.googology.primitive-recursive-class
> **一句话**: 原始递归函数类是含初始函数并对复合、原始递归封闭的最小函数类；本库直接采用
> mathlib 的教科书版 `Nat.Primrec'`，并证明它关于有界求和、有界求积与有限迭代封闭。
> **依赖**: `settheory.googology.primitive-recursion`
> **mathlib**: `Nat.Primrec'`, `Nat.Primrec'.prim_iff`
@isnad1 id=primrec.2h3v.s6.4a74af294635 from=translated src=- shape=97c9b3cb vocab=ae6c875e
-/
theorem primrec_boundedSum {n : ℕ} {b : List.Vector ℕ n → ℕ}
    {f : List.Vector ℕ (n + 1) → ℕ}
    (hb : @Nat.Primrec' n b) (hf : @Nat.Primrec' (n + 1) f) :
    @Nat.Primrec' n (fun v => Finset.sum (Finset.range (b v)) (fun i => f (i ::ᵥ v))) := by
  have hrec : @Nat.Primrec' n
      (fun v => Nat.rec 0 (fun y IH => IH + f (y ::ᵥ v)) (b v)) :=
    Nat.Primrec'.prec' hb (Nat.Primrec'.const 0) (primrec_stepSum hf)
  refine hrec.of_eq (fun v => ?_)
  induction b v with
  | zero => simp
  | succ k ih => simp [ih, Finset.sum_range_succ]

/-- 有界求和的乘积版本：递归步骤为 `IH * f y`。
@isnad1 id=primrec.2h3v.s6.267c85b62086 from=translated src=- shape=97c9b3cb vocab=8391003c
-/
theorem primrec_boundedProd {n : ℕ} {b : List.Vector ℕ n → ℕ}
    {f : List.Vector ℕ (n + 1) → ℕ}
    (hb : @Nat.Primrec' n b) (hf : @Nat.Primrec' (n + 1) f) :
    @Nat.Primrec' n (fun v => Finset.prod (Finset.range (b v)) (fun i => f (i ::ᵥ v))) := by
  have hh : @Nat.Primrec' (n + 2) (fun w : List.Vector ℕ (n + 2) =>
      w.tail.head * f (w.head ::ᵥ w.tail.tail)) :=
    Nat.Primrec'.mul.comp₂ _ (Nat.Primrec'.tail (@Nat.Primrec'.head (n := n)))
      (primrec_compHeadTail hf)
  have hrec : @Nat.Primrec' n
      (fun v => Nat.rec 1 (fun y IH => IH * f (y ::ᵥ v)) (b v)) :=
    Nat.Primrec'.prec' hb (Nat.Primrec'.const 1) hh
  refine hrec.of_eq (fun v => ?_)
  induction b v with
  | zero => simp
  | succ k ih => simp [ih, Finset.prod_range_succ]

/--
有限迭代：给定原始递归的初值 `base`、单步 `step` 与迭代次数 `count`，反复施加 `count v` 次
`step` 得到的函数仍属类。这是 ST3 中「带燃料增长」模板的闭包基础。
@isnad1 id=primrec.3h4v.s6.93f303a748df from=translated src=- shape=2a68b7b9 vocab=80136425
-/
theorem primrec_iterated {n : ℕ} {base : List.Vector ℕ n → ℕ}
    {step : List.Vector ℕ (n + 1) → ℕ} {count : List.Vector ℕ n → ℕ}
    (hbase : @Nat.Primrec' n base) (hstep : @Nat.Primrec' (n + 1) step)
    (hcount : @Nat.Primrec' n count) :
    @Nat.Primrec' n (fun v => Nat.rec (base v) (fun _ IH => step (IH ::ᵥ v)) (count v)) :=
  Nat.Primrec'.prec' hcount hbase
    (hstep.comp' (Nat.Primrec'.cons (Nat.Primrec'.tail (@Nat.Primrec'.head (n := n)))
      primrec_tailTailVec))

/-- 本库 `primitiveRecursion` 展开为 `Nat.rec`，用于接入函数类。-/
private theorem primrec_primitiveRecursion_eq_rec (z : ℕ) (step : ℕ → ℕ → ℕ) (n : ℕ) :
    primitiveRecursion z step n = Nat.rec z (fun y IH => step y IH) n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [primitiveRecursion, ih]

/--
本库 `primitiveRecursion` 的接入：若更新规则 `step` 作为二元函数属于类，则
`fun v => primitiveRecursion z step v.head` 也属于类。这样 `Googology` 的一元递归模板
不再是类外的孤立构造。
@isnad1 id=primrec.1h2v.s6.3ccf8388b4c9 from=translated src=- shape=a415bdf0 vocab=ec6d9032
-/
theorem primrec_primitiveRecursion {z : ℕ} {step : ℕ → ℕ → ℕ}
    (hstep : @Nat.Primrec' 2 (fun v : List.Vector ℕ 2 => step v.head v.tail.head)) :
    @Nat.Primrec' 1 (fun v : List.Vector ℕ 1 => primitiveRecursion z step v.head) := by
  have h3 : @Nat.Primrec' 3 (fun w : List.Vector ℕ 3 => step w.head w.tail.head) :=
    hstep.comp' (Nat.Primrec'.cons (Nat.Primrec'.head (n := 2))
      (Nat.Primrec'.cons (Nat.Primrec'.tail (@Nat.Primrec'.head (n := 1)))
        Nat.Primrec'.nil))
  refine (Nat.Primrec'.prec' (@Nat.Primrec'.head 0) (Nat.Primrec'.const z) h3).of_eq ?_
  intro v
  exact (primrec_primitiveRecursion_eq_rec z step v.head).symm

end SandronesLibrary.SetTheory.Googology
