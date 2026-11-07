/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Cslib.Cslib.Computability.Circuit.Program
public import Tengoku.Seed.Data.Fintype.BigOperators

import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite circuit syntax

A finite signature gives computable enumerations of lines and programs of each fixed size.
Their cardinalities count syntax and are independent of any interpretation or carrier.
`Line.card_le` bounds the number of lines when all operation arities are bounded.
-/

@[expose] public section

namespace Cslib.Circuits

universe v
variable {σ : Signature.{v}} [Fintype σ.Op]

instance Line.instFintype (n g : ℕ) : Fintype (Line σ n g) :=
  Fintype.ofEquiv _ (Line.equiv σ n g).symm

instance Program.instFintype (n : ℕ) : (g : ℕ) → Fintype (Program σ n g)
  | 0 => Fintype.ofEquiv PUnit (Program.emptyEquiv σ n).symm
  | g + 1 =>
      letI := Program.instFintype n g
      Fintype.ofEquiv _ (Program.gateEquiv σ n g).symm

/-- For each operation, choose one wire for each of its arguments.
@isnad1 id=eq.0h3v.s5.e4df28fe5e8d from=translated src=- shape=0baa776b vocab=67c68e8e
-/
theorem Line.card (n g : ℕ) :
    Fintype.card (Line σ n g) = ∑ op : σ.Op, (n + g) ^ σ.Arity op := by
  rw [Fintype.card_congr (Line.equiv σ n g), Fintype.card_sigma]
  simp

/-- A uniform arity bound gives a uniform bound on the number of lines, including when
there are no available wires.
@isnad1 id=le.1h4v.s6.877a675332ab from=translated src=- shape=f3b6be01 vocab=b4358447
-/
theorem Line.card_le (n g r : ℕ) (arity_le : ∀ op, σ.Arity op ≤ r) :
    Fintype.card (Line σ n g) ≤ Fintype.card σ.Op * (n + g + 1) ^ r := by
  rw [Line.card]
  calc
    ∑ op : σ.Op, (n + g) ^ σ.Arity op ≤ ∑ _op : σ.Op, (n + g + 1) ^ r := by
      apply Finset.sum_le_sum
      intro op _
      exact (Nat.pow_le_pow_left (by omega : n + g ≤ n + g + 1) _).trans
        (Nat.pow_le_pow_right (by omega) (arity_le op))
    _ = _ := by simp

/-- There is one empty program, regardless of the signature or number of inputs.
@isnad1 id=eq.0h2v.s5.04ecba78c5cb from=translated src=- shape=83d43fe6 vocab=ce740de5
-/
@[simp] theorem Program.card_zero (n : ℕ) : Fintype.card (Program σ n 0) = 1 := by
  rw [Fintype.card_congr (Program.emptyEquiv σ n)]
  simp

/-- Choose a prefix program and then its last line.
@isnad1 id=eq.0h3v.s6.8391ff5d82f1 from=translated src=- shape=317adba4 vocab=af96c4fa
-/
theorem Program.card_succ (n g : ℕ) :
    Fintype.card (Program σ n (g + 1)) =
      Fintype.card (Program σ n g) * Fintype.card (Line σ n g) := by
  rw [Fintype.card_congr (Program.gateEquiv σ n g), Fintype.card_prod]

/-- The line at each position may refer to the inputs and all preceding gates.
@isnad1 id=eq.0h3v.s6.f87477cf6dc8 from=translated src=- shape=6f4e4236 vocab=1a60bc84
-/
theorem Program.card (n g : ℕ) :
    Fintype.card (Program σ n g) =
      ∏ j ∈ Finset.range g, ∑ op : σ.Op, (n + j) ^ σ.Arity op := by
  induction g with
  | zero => simp
  | succ g ih => simp [Program.card_succ, ih, Line.card, Finset.prod_range_succ]

end Cslib.Circuits
