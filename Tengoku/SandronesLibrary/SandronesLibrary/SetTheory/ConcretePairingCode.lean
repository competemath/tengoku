/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.ComputabilityDiagonal
import Tengoku.Seed.Data.Nat.Pairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / ConcretePairingCode —— 可计算的自然数配对实例

本文件用 mathlib 的显式算术函数 `Nat.pair` 与 `Nat.unpair`，构造本库
`ComputabilityDiagonal.PairingCode` 的具体实例。公开对象只负责自然数有序对的编码和恢复；它不是
通用解释器、runner 或翻转编译器。
-/

namespace SandronesLibrary.SetTheory.ConcretePairingCode

open ComputabilityDiagonal

/--
具体自然数配对规格：配对使用 `Nat.pair`，左右投影分别取 `Nat.unpair` 的两个分量。-/
def natPairingCode : PairingCode where
  pair := Nat.pair
  left := fun code => code.unpair.1
  right := fun code => code.unpair.2
  left_pair := by
    intro x y
    exact congrArg Prod.fst (Nat.unpair_pair x y)
  right_pair := by
    intro x y
    exact congrArg Prod.snd (Nat.unpair_pair x y)

/-- 具体配对的两个投影同时恢复原有序对。-/
theorem natPairingCode_recover (x y : ℕ) :
    (natPairingCode.left (natPairingCode.pair x y),
      natPairingCode.right (natPairingCode.pair x y)) = (x, y) := by
  exact natPairingCode.recover x y

/-- 具体配对函数在自然数有序对上没有碰撞。-/
theorem natPairingCode_injective :
    Function.Injective (fun p : ℕ × ℕ => natPairingCode.pair p.1 p.2) := by
  exact natPairingCode.pair_injective

/--
> **Entry**: settheory.computability.concrete-pairing-code
> **一句话**: `Nat.pair` 与 `Nat.unpair` 给出一个可计算、可恢复且无碰撞的自然数有序对编码。
> **依赖**: `settheory.computability.pairing-code`
> **mathlib**: `Nat.pair`, `Nat.unpair`, `Nat.unpair_pair`-/
theorem natPairingCode_specification (x y : ℕ) :
    natPairingCode.left (natPairingCode.pair x y) = x ∧
      natPairingCode.right (natPairingCode.pair x y) = y := by
  exact ⟨natPairingCode.left_pair x y, natPairingCode.right_pair x y⟩

end SandronesLibrary.SetTheory.ConcretePairingCode
