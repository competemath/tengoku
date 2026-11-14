/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Hydra
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Ordinal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A structural ordinal assignment for finite hydras

The assignment in this file is built only from the library's public
`ordinalAdd` and `ordinalPow`.  We prove a strict decrease for the precise
subclass that removes the rightmost head at the root, and isolate replication
as a repeated ordinal sum.  We do not claim decrease for every `Hydra.Step` or
termination of the full game.
-/

namespace SandronesLibrary.SetTheory.HydraOrdinalAssignment

open SandronesLibrary.SetTheory
open SandronesLibrary.SetTheory.Ordinal

mutual
  /-- The ordinal assigned to a hydra.  A leaf has value zero; a non-leaf is
  evaluated through its ordered forest of children.-/
  noncomputable def hydraOrdinal : Hydra → Ordinal
    | .node children => forestOrdinal children

  /-- The ordered forest assignment
  `ω^(value of first tree) + value of the remaining forest`.-/
  noncomputable def forestOrdinal : List Hydra → Ordinal
    | [] => 0
    | child :: rest =>
        ordinalAdd (ordinalPow Ordinal.omega0 (hydraOrdinal child))
          (forestOrdinal rest)
end

/-- Repeating an ordinal term a finite number of times, with the repeated sum
itself defined using the library's ordinal addition.-/
noncomputable def ordinalRepeat (term : Ordinal) : Nat → Ordinal
  | 0 => 0
  | n + 1 => ordinalAdd term (ordinalRepeat term n)

/-- A restricted cut that removes exactly the rightmost root-level head.-/
def RightmostRootHeadCut (before after : Hydra) : Prop :=
  ∃ children, before = .node (children ++ [Hydra.head]) ∧ after = .node children

@[simp]
theorem hydraOrdinal_head : hydraOrdinal Hydra.head = 0 := by
  rfl

theorem forestOrdinal_append_head (children : List Hydra) :
    forestOrdinal (children ++ [Hydra.head]) = Order.succ (forestOrdinal children) := by
  induction children with
  | nil =>
      rw [List.nil_append]
      simp only [forestOrdinal]
      rw [hydraOrdinal_head, ordinalPow_zero, ordinalAdd_zero]
      rw [Order.succ_eq_add_one, zero_add]
  | cons child rest ih =>
      simp only [List.cons_append, forestOrdinal]
      rw [ih, ordinalAdd_succ]

/-- Every rightmost root-head cut strictly lowers the structural assignment.-/
theorem rightmostRootHeadCut_decreases {before after : Hydra}
    (cut : RightmostRootHeadCut before after) :
    hydraOrdinal after < hydraOrdinal before := by
  rcases cut with ⟨children, rfl, rfl⟩
  rw [hydraOrdinal, hydraOrdinal, forestOrdinal_append_head]
  exact Order.lt_succ _

/-- Replicating one pruned parent produces exactly a finite repeated ordinal
sum of its contribution.  This is the algebraic interface needed for later
analysis of the stage-dependent regrowth clause.-/
theorem forestOrdinal_replicate (copies : Nat) (parent : Hydra) :
    forestOrdinal (List.replicate copies parent) =
      ordinalRepeat (ordinalPow Ordinal.omega0 (hydraOrdinal parent)) copies := by
  induction copies with
  | zero => rfl
  | succ copies ih =>
      simp only [List.replicate_succ, forestOrdinal, ordinalRepeat]
      rw [ih]

/--
> **Entry**: settheory.googology.hydra-ordinal-assignment
> **一句话**: 用本库序数幂与序数加法为有限 Hydra 赋值，并证明最右根头删除严格下降、阶段复制化为有限重复和。
> **依赖**: `settheory.googology.hydra-game-step`、`settheory.ordinal.addition`、
>   `settheory.ordinal.exponentiation`
> **mathlib**: `Order.lt_succ`

This theorem packages the two verified interfaces; it does not assert that the
assignment decreases under every hydra step.-/
theorem hydraOrdinal_verified_interfaces :
    (∀ {before after}, RightmostRootHeadCut before after →
      hydraOrdinal after < hydraOrdinal before) ∧
    (∀ copies parent,
      forestOrdinal (List.replicate copies parent) =
        ordinalRepeat (ordinalPow Ordinal.omega0 (hydraOrdinal parent)) copies) := by
  exact ⟨fun cut => rightmostRootHeadCut_decreases cut,
    fun copies parent => forestOrdinal_replicate copies parent⟩

end SandronesLibrary.SetTheory.HydraOrdinalAssignment
