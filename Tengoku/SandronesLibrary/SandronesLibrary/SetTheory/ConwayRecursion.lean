/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoogologyNotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / ConwayRecursion —— 一般有限 Conway 链的递归求值

链采用从右端追加元素的归纳语法。求值的嵌套递归以“链长、末项、倒数第二项”的
字典序为终止度量：删去 `1` 会缩短链，主递推的内层调用降低倒数第二项，外层调用
降低末项。公开数学接口限制在正整数链；定义中关于零的分支只负责使 Lean 函数成为总函数。
-/

namespace SandronesLibrary.SetTheory.ConwayRecursion

/-- 从右端构造的非空有限链。`snoc c b` 表示在 `c` 的右边再接一个 `b`。-/
inductive ConwayArrowTerm where
  | singleton (a : ℕ)
  | snoc (init : ConwayArrowTerm) (last : ℕ)
deriving DecidableEq, Repr

/-- 链中元素的个数。-/
def ConwayArrowTerm.length : ConwayArrowTerm → ℕ
  | .singleton _ => 1
  | .snoc c _ => c.length + 1

/-- 链的末项。-/
def ConwayArrowTerm.last : ConwayArrowTerm → ℕ
  | .singleton a => a
  | .snoc _ b => b

/-- 链的倒数第二项；单项链没有倒数第二项，技术上记为零。-/
def ConwayArrowTerm.penultimate : ConwayArrowTerm → ℕ
  | .singleton _ => 0
  | .snoc c _ => c.last

/-- Conway 记号的数学定义域：链中每个数都是正整数。-/
def ConwayArrowTerm.Positive : ConwayArrowTerm → Prop
  | .singleton a => 0 < a
  | .snoc c b => c.Positive ∧ 0 < b

/-- 把右追加语法读成通常从左到右书写的列表。-/
def ConwayArrowTerm.entries : ConwayArrowTerm → List ℕ
  | .singleton a => [a]
  | .snoc c b => c.entries ++ [b]

/-- 终止性证明使用的字典序度量。-/
private def recursionMeasure (c : ConwayArrowTerm) : ℕ × ℕ × ℕ :=
  (c.length, c.last, c.penultimate)

/--
一般有限 Conway 链的求值。正整数输入上的三个数学规则是：单项链等于该项，
两项链是幂；末项为 `1` 时删去末项，倒数第二项为 `1` 时从该处删掉整个尾部；
若末两项均大于一，使用
`X→a→b = X→(X→(a-1)→b)→(b-1)`。零分支只是定义域外的总化约定。-/
def ConwayArrowTerm.eval : ConwayArrowTerm → ℕ
  | .singleton a => a
  | .snoc (.singleton a) b => a ^ b
  | .snoc c 1 => eval c
  | .snoc (.snoc c 1) _ => eval c
  | .snoc (.snoc c 0) _ => eval c
  | .snoc (.snoc c (a + 2)) 0 => eval (.snoc c (a + 2))
  | .snoc (.snoc c (a + 2)) (b + 2) =>
      let inner := eval (.snoc (.snoc c (a + 1)) (b + 2))
      eval (.snoc (.snoc c inner) (b + 1))
termination_by c => recursionMeasure c
decreasing_by
  · apply Prod.Lex.left
    simp [ConwayArrowTerm.length]
  · apply Prod.Lex.left
    simp [ConwayArrowTerm.length]
    omega
  · apply Prod.Lex.left
    simp [ConwayArrowTerm.length]
    omega
  · apply Prod.Lex.left
    simp [ConwayArrowTerm.length]
  · apply Prod.Lex.right
    apply Prod.Lex.right
    simp [ConwayArrowTerm.penultimate, ConwayArrowTerm.last]
  · apply Prod.Lex.right
    apply Prod.Lex.left
    simp [ConwayArrowTerm.last]

/-- 正链转换为原有的列表式 `ConwayChain` 语法。-/
def ConwayArrowTerm.toChain (c : ConwayArrowTerm) (hc : c.Positive) :
    GoogologyNotation.ConwayChain :=
  { entries := c.entries
    nonempty := by
      cases c <;> simp [ConwayArrowTerm.entries]
    positive := by
      induction c with
      | singleton a =>
          simpa [ConwayArrowTerm.entries, ConwayArrowTerm.Positive] using hc
      | snoc c b ih =>
          have hcb : c.Positive ∧ 0 < b := hc
          intro n hn
          simp only [ConwayArrowTerm.entries, List.mem_append, List.mem_singleton] at hn
          rcases hn with hn | rfl
          · exact ih hcb.1 n hn
          · exact hcb.2 }

/--
> **Entry**: settheory.googology.conway-recursion
> **一句话**: 一般有限正整数 Conway 链由三个基础规则和一个嵌套递推规则总地求值。
> **依赖**: settheory.googology.conway-chain
> **mathlib**: `Prod.Lex`（仅用于递归终止性）-/
theorem conwayEval_equations (a b : ℕ) (c : ConwayArrowTerm) :
    (ConwayArrowTerm.singleton a).eval = a ∧
      (ConwayArrowTerm.snoc (ConwayArrowTerm.singleton a) b).eval = a ^ b ∧
      (ConwayArrowTerm.snoc c 1).eval = c.eval := by
  constructor
  · rw [ConwayArrowTerm.eval.eq_def]
  constructor
  · rw [ConwayArrowTerm.eval.eq_def]
  · cases c with
    | singleton a =>
        rw [ConwayArrowTerm.eval.eq_2, ConwayArrowTerm.eval.eq_1, Nat.pow_one]
    | snoc c b =>
        apply ConwayArrowTerm.eval.eq_3
        intro a h
        cases h

/-- 倒数第二项为一时，这个一及其右侧尾部一起删去。-/
theorem conwayEval_penultimate_one (c : ConwayArrowTerm) (b : ℕ) :
    (ConwayArrowTerm.snoc (ConwayArrowTerm.snoc c 1) b).eval =
      c.eval := by
  rcases b with _ | _ | b
  · apply ConwayArrowTerm.eval.eq_4
    omega
  · rw [ConwayArrowTerm.eval.eq_3 (ConwayArrowTerm.snoc c 1) (by
      intro a h
      cases h)]
    exact (conwayEval_equations 0 0 c).2.2
  · apply ConwayArrowTerm.eval.eq_4
    omega

/-- 最小的非平凡三项例子核对了递推方向：`2→2→2 = 4`。-/
theorem conwayEval_two_two_two :
    (ConwayArrowTerm.snoc (ConwayArrowTerm.snoc (.singleton 2) 2) 2).eval = 4 := by
  rw [ConwayArrowTerm.eval.eq_7]
  rw [ConwayArrowTerm.eval.eq_4 _ 2 (by omega)]
  rw [ConwayArrowTerm.eval.eq_1]
  rw [ConwayArrowTerm.eval.eq_3 _ (by intro a h; cases h)]
  rw [ConwayArrowTerm.eval.eq_2]

/-- Conway 的一般递推方程；`a+2`、`b+2` 明示末两项均大于一。-/
theorem conwayEval_recursive (c : ConwayArrowTerm) (a b : ℕ) :
    (ConwayArrowTerm.snoc (ConwayArrowTerm.snoc c (a + 2)) (b + 2)).eval =
      (ConwayArrowTerm.snoc
        (ConwayArrowTerm.snoc c
          ((ConwayArrowTerm.snoc (ConwayArrowTerm.snoc c (a + 1)) (b + 2)).eval))
        (b + 1)).eval := by
  simpa only [Nat.succ_eq_add_one] using ConwayArrowTerm.eval.eq_7 c a b

end SandronesLibrary.SetTheory.ConwayRecursion
