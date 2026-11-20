/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.LinearAlgebra.Matrix.DotProduct
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.Tactic.Module
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace SRG266.QuasiSymmetric.TernaryStarRecovery

theorem complement_mem_of_three_columns
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (C : Submodule (ZMod 3) V) (u a b c : V)
    (hab : (2 : ZMod 3) • u - a - b ∈ C)
    (hac : (2 : ZMod 3) • u - a - c ∈ C)
    (hbc : (2 : ZMod 3) • u - b - c ∈ C) :
    u - a ∈ C := by
  have h := C.add_mem (C.sub_mem (C.neg_mem hab) hac) hbc
  have heq : u - a =
      -((2 : ZMod 3) • u - a - b) -
        ((2 : ZMod 3) • u - a - c) +
        ((2 : ZMod 3) • u - b - c) := by
    match_scalars <;> decide
  rw [heq]
  exact h

def complementVector (B : Finset (Fin 56)) : Fin 56 → ZMod 3 :=
  fun p => if p ∈ B then 0 else 1

theorem complement_dotProduct (B D : Finset (Fin 56)) :
    dotProduct (complementVector B) (complementVector D) =
      ((Bᶜ ∩ Dᶜ).card : ZMod 3) := by
  classical
  unfold dotProduct complementVector
  calc
    (∑ p : Fin 56, (if p ∈ B then 0 else 1) *
        (if p ∈ D then 0 else 1) : ZMod 3) =
        ∑ p : Fin 56, if p ∈ Bᶜ ∩ Dᶜ then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hB : p ∈ B <;> by_cases hD : p ∈ D <;> simp [hB, hD]
    _ = _ := by
      simp
      congr 1
      apply congrArg Finset.card
      ext p
      simp

theorem overlap_eq_two_mod_three
    (B D : Finset (Fin 56)) (hB : B.card = 11) (hD : D.card = 11)
    (horth : dotProduct (complementVector B) (complementVector D) = 0) :
    ((B ∩ D).card : ZMod 3) = 2 := by
  have hsize : (Bᶜ ∩ Dᶜ).card = 34 + (B ∩ D).card := by
    have hc := Finset.card_compl (B ∪ D)
    have hu := Finset.card_union_add_card_inter B D
    have hle := Finset.card_le_univ (B ∪ D)
    rw [Finset.compl_union] at hc
    simp only [Fintype.card_fin] at hc hle
    omega
  rw [complement_dotProduct, hsize, Nat.cast_add,
    show ((34 : ℕ) : ZMod 3) = 1 by decide] at horth
  calc
    ((B ∩ D).card : ZMod 3) = (1 + ((B ∩ D).card : ZMod 3)) - 1 := by ring
    _ = -1 := by rw [horth]; simp
    _ = 2 := by decide

end SRG266.QuasiSymmetric.TernaryStarRecovery
