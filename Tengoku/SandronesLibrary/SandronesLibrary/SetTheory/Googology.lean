/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Data.Nat.Hyperoperation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / Googology —— 递归与有限大数的第一批基础

本文件当前条目：

* **settheory.googology.primitive-recursion**：从初值和前一步构造自然数函数。
* **settheory.googology.hyperoperation**：从后继、加法、乘法、幂继续迭代运算。
* **settheory.googology.ackermann**：双重递归定义 Ackermann 函数。
* **settheory.googology.knuth-arrow**：用箭头数量记录超运算等级。
* **settheory.googology.graham-number**：有限递归定义 Graham 数。
* **settheory.googology.hereditary-base**：指数也递归展开的遗传基表达式。
* **settheory.googology.goodstein-step**：换底后减一的 Goodstein 单步。

这里的值始终是有限自然数。增长很快不等于成为无限基数。
-/

namespace SandronesLibrary.SetTheory.Googology

/-- 给定初值 `z` 与更新规则 `step`，沿自然数逐步生成一个函数。-/
def primitiveRecursion (z : ℕ) (step : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => z
  | n + 1 => step n (primitiveRecursion z step n)

/--
> **Entry**: settheory.googology.primitive-recursion
> **一句话**: 原始递归用一个零点值和一个只调用前一步的更新规则定义自然数函数。
> **依赖**: 无
> **mathlib**: `Nat.rec`-/
theorem primitiveRecursion_zero_succ (z : ℕ) (step : ℕ → ℕ → ℕ) (n : ℕ) :
    primitiveRecursion z step 0 = z ∧
      primitiveRecursion z step (n + 1) = step n (primitiveRecursion z step n) := by
  exact ⟨rfl, rfl⟩

/--
第 `rank` 级超运算。零级是后继；再往上依次出现加法、乘法、幂、迭代幂等。
后继级的零输入需要分级设置单位元，确保前三个熟悉运算正确出现。-/
def hyperOperation : ℕ → ℕ → ℕ → ℕ
  | 0, _, b => b + 1
  | 1, a, 0 => a
  | 2, _, 0 => 0
  | _ + 3, _, 0 => 1
  | rank + 1, a, b + 1 =>
      hyperOperation rank a (hyperOperation (rank + 1) a b)

/--
> **Entry**: settheory.googology.hyperoperation
> **一句话**: 每一级超运算都通过反复调用前一级运算生成下一级。
> **依赖**: `settheory.googology.primitive-recursion`
> **mathlib**: `Nat.hyperoperation`-/
private theorem hyperOperation_one (a b : ℕ) : hyperOperation 1 a b = a + b := by
  induction b with
  | zero => simp [hyperOperation]
  | succ b ih => simp only [hyperOperation, ih, Nat.add_assoc]

private theorem hyperOperation_two (a b : ℕ) : hyperOperation 2 a b = a * b := by
  induction b with
  | zero => simp [hyperOperation]
  | succ b ih =>
      rw [hyperOperation, hyperOperation_one, ih, Nat.mul_succ, Nat.add_comm]

private theorem hyperOperation_three (a b : ℕ) : hyperOperation 3 a b = a ^ b := by
  induction b with
  | zero => simp [hyperOperation]
  | succ b ih =>
      rw [hyperOperation, hyperOperation_two, ih, pow_succ, Nat.mul_comm]

theorem hyperOperation_first_levels (a b : ℕ) :
    hyperOperation 0 a b = b + 1 ∧
      hyperOperation 1 a b = a + b ∧
      hyperOperation 2 a b = a * b ∧
      hyperOperation 3 a b = a ^ b := by
  exact ⟨by simp [hyperOperation], hyperOperation_one a b,
    hyperOperation_two a b, hyperOperation_three a b⟩

/-- Ackermann–Péter 函数。内层递归完成后，其结果成为外层较低等级递归的新输入。-/
def ackermann : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)

/--
> **Entry**: settheory.googology.ackermann
> **一句话**: Ackermann 函数由双重递归定义，并满足三条可直接计算的递归方程。
> **依赖**: `settheory.googology.primitive-recursion`
> **mathlib**: `Nat.ack`-/
theorem ackermann_equations (m n : ℕ) :
    ackermann 0 n = n + 1 ∧
      ackermann (m + 1) 0 = ackermann m 1 ∧
      ackermann (m + 1) (n + 1) = ackermann m (ackermann (m + 1) n) := by
  simp [ackermann]

/-- `a ↑^arrows b` 的 Knuth 上箭头值；一支箭头从幂运算开始。-/
def knuthArrow (a arrows b : ℕ) : ℕ :=
  hyperOperation (arrows + 2) a b

/--
> **Entry**: settheory.googology.knuth-arrow
> **一句话**: 一支上箭头表示幂，每多一支箭头就把前一级运算再迭代一层。
> **依赖**: `settheory.googology.hyperoperation`
> **mathlib**: `Nat.hyperoperation`-/
theorem knuthArrow_one (a b : ℕ) : knuthArrow a 1 b = a ^ b := by
  exact (hyperOperation_first_levels a b).2.2.2

theorem knuthArrow_succ_succ (a arrows b : ℕ) :
    knuthArrow a (arrows + 1) (b + 1) =
      knuthArrow a arrows (knuthArrow a (arrows + 1) b) := by
  simp only [knuthArrow, Nat.add_assoc, hyperOperation]

/-- Graham 序列：`g₀=3↑↑↑↑3`，下一项使用前一项那么多支箭头。-/
def grahamSequence : ℕ → ℕ
  | 0 => knuthArrow 3 4 3
  | n + 1 => knuthArrow 3 (grahamSequence n) 3

/-- Graham 数是上述序列的第 64 项（采用从 `g₀` 开始编号的约定）。-/
def grahamNumber : ℕ :=
  grahamSequence 63

/--
> **Entry**: settheory.googology.graham-number
> **一句话**: Graham 数由 64 个有限阶段定义，每一步把前一项变成下一步的箭头数量。
> **依赖**: `settheory.googology.knuth-arrow`
> **mathlib**: 无（本库显式定义）-/
theorem grahamSequence_equations (n : ℕ) :
    grahamSequence 0 = knuthArrow 3 4 3 ∧
      grahamSequence (n + 1) = knuthArrow 3 (grahamSequence n) 3 := by
  exact ⟨rfl, rfl⟩

theorem grahamNumber_is_64th_stage : grahamNumber = grahamSequence 63 := rfl

/--
遗传基表达式的语法树。`basePow e` 表示“当前底数的 `e` 次幂”，而指数 `e` 自身仍是
同一种表达式，所以底数在指数内部的出现也能随换底一起改变。-/
inductive HereditaryBaseExpr where
  | zero
  | digit (n : ℕ)
  | add (left right : HereditaryBaseExpr)
  | mul (left right : HereditaryBaseExpr)
  | basePow (exponent : HereditaryBaseExpr)
deriving DecidableEq, Repr

/-- 在指定自然数底数下解释遗传基表达式。-/
def HereditaryBaseExpr.eval (base : ℕ) : HereditaryBaseExpr → ℕ
  | .zero => 0
  | .digit n => n
  | .add left right => left.eval base + right.eval base
  | .mul left right => left.eval base * right.eval base
  | .basePow exponent => base ^ exponent.eval base

/-- 数字叶必须小于底数；其余节点递归满足同一要求。-/
def HereditaryBaseExpr.Valid (base : ℕ) : HereditaryBaseExpr → Prop
  | .zero => True
  | .digit n => n < base
  | .add left right | .mul left right => left.Valid base ∧ right.Valid base
  | .basePow exponent => exponent.Valid base

/--
> **Entry**: settheory.googology.hereditary-base
> **一句话**: 遗传基表示不仅展开原数，也把指数递归写成同一底数的表达式。
> **依赖**: `settheory.googology.primitive-recursion`
> **mathlib**: 无（本库显式语法与求值）-/
theorem hereditary_four_example :
    let four := HereditaryBaseExpr.basePow (.basePow (.digit 1))
    four.Valid 2 ∧ four.eval 2 = 4 ∧ four.eval 3 = 27 := by
  norm_num [HereditaryBaseExpr.Valid, HereditaryBaseExpr.eval]

/-- 换底不改语法树，只把所有 `basePow` 节点统一放到新底数下解释。-/
def hereditaryBaseChangeValue (newBase : ℕ) (expr : HereditaryBaseExpr) : ℕ :=
  expr.eval newBase

/-- Goodstein 单步：把遗传表达式中的底数提升到 `base+1`，求值后减一。-/
def goodsteinStep (base : ℕ) (expr : HereditaryBaseExpr) : ℕ :=
  hereditaryBaseChangeValue (base + 1) expr - 1

/--
> **Entry**: settheory.googology.goodstein-step
> **一句话**: Goodstein 单步先统一提高遗传表示中的底数，再对得到的自然数减一。
> **依赖**: `settheory.googology.hereditary-base`
> **mathlib**: 无（本库显式定义）-/
theorem goodsteinStep_four_base_two :
    let four := HereditaryBaseExpr.basePow (.basePow (.digit 1))
    goodsteinStep 2 four = 26 := by
  decide

end SandronesLibrary.SetTheory.Googology
