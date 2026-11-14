/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoodsteinHigherBorrow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GoodsteinFinitePowerBorrow —— 有限指数幂的递归借位

对新底数 `q=base+1`，本文件递归展开 `q^k-1`：
`q^(k+1)-1 = q^k·base + (q^k-1)`。这给出任意正有限数字指数
`0<k<base` 的显式借位，但不处理指数本身需要遗传展开的情形。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/--
在新底数 `base+1` 下对 `(base+1)^k-1` 的递归遗传展开。系数
`base` 是新底数下的最大合法数字。-/
def finitePowerBorrowExpansion (base : ℕ) : ℕ → HereditaryBaseExpr
  | 0 => .zero
  | k + 1 =>
      .add (.mul (.basePow (.digit k)) (.digit base))
        (finitePowerBorrowExpansion base k)

/--
以有限正数字为指数的带证书借位形。`exponent_valid` 保证指数叶子
在原底数下合法；这正是本条与任意遗传指数之间的边界。-/
structure FinitePowerBorrowForm (base : ℕ) where
  base_ge_two : 2 ≤ base
  exponent : ℕ
  exponent_positive : 0 < exponent
  exponent_valid : exponent < base
  head : HereditaryBaseExpr
  head_valid : head.Valid base

/-- 借位前的表达式 `head + B^exponent`。-/
def FinitePowerBorrowForm.expression {base : ℕ}
    (f : FinitePowerBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (.basePow (.digit f.exponent))

/-- 换到新底数后，以递归展开替换末尾的底数幂。-/
def FinitePowerBorrowForm.borrowedExpression {base : ℕ}
    (f : FinitePowerBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (finitePowerBorrowExpansion base f.exponent)

theorem finitePowerBorrowExpansion_eval (base k : ℕ) :
    (finitePowerBorrowExpansion base k).eval (base + 1) =
      (base + 1) ^ k - 1 := by
  induction k with
  | zero => simp [finitePowerBorrowExpansion, HereditaryBaseExpr.eval]
  | succ k ih =>
      simp only [finitePowerBorrowExpansion, HereditaryBaseExpr.eval, ih]
      rw [← Nat.add_sub_assoc (Nat.one_le_pow k (base + 1) (by omega))]
      simp [Nat.pow_succ, Nat.mul_add]

theorem finitePowerBorrowExpansion_valid {base k : ℕ} (hk : k ≤ base) :
    (finitePowerBorrowExpansion base k).Valid (base + 1) := by
  induction k with
  | zero => trivial
  | succ k ih =>
      simp only [finitePowerBorrowExpansion, HereditaryBaseExpr.Valid]
      exact ⟨⟨lt_trans (Nat.lt_of_succ_le hk) (Nat.lt_succ_self base),
          Nat.lt_succ_self base⟩,
        ih (Nat.le_trans (Nat.le_succ k) hk)⟩

end

end SandronesLibrary.SetTheory.Googology
