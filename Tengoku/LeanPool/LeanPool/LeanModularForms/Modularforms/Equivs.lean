/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku

/-! # Equivs -/

@[expose] public section

open TopologicalSpace Set
  Metric Filter Function

/-- Negation as an equivalence `ℤ ≃ ℤ`. -/
def negEquiv : ℤ ≃ ℤ where
  toFun n := -n
  invFun n := -n
  left_inv := neg_neg
  right_inv := neg_neg

/-- The successor map as an equivalence `ℤ ≃ ℤ`. -/
def succEquiv : ℤ ≃ ℤ where
  toFun n := n.succ
  invFun n := n.pred
  left_inv := Int.pred_succ
  right_inv := Int.succ_pred

/-- Swaps the two entries of a length-2 vector. -/
def swap {α : Type*} : (Fin 2 → α) → (Fin 2 → α) := fun x => ![x 1, x 0]

/--
@isnad1 id=eq.0h2v.s6.c3f5a2a44f71 from=translated src=- shape=7908dc93 vocab=f3ead3f5
-/
@[simp]
lemma swap_apply {α : Type*} (b : Fin 2 → α) : swap b = ![b 1, b 0] := rfl

/--
@isnad1 id=eq.0h2v.s4.baff3014d58c from=translated src=- shape=2b38ad0b vocab=21ecb859
-/
lemma swap_involutive {α : Type*} (b : Fin 2 → α) : swap (swap b) = b := by
  ext i
  fin_cases i <;> rfl

/-- Swapping the two entries of a length-2 vector as an equivalence. -/
def swapEquiv {α : Type*} : Equiv (Fin 2 → α) (Fin 2 → α) := Equiv.mk swap swap
  swap_involutive swap_involutive
