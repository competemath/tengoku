/-
Copyright (c) 2026 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
module

public import Tengoku

/-!
# List repetition utilities

Defines `nTimes` (notation `l ^+^ n`), the `n`-fold repetition of a list,
together with basic rewriting lemmas about it.
-/

@[expose] public section

variable {α : Type _}

/-- `nTimes l n` (notation `l ^+^ n`) is the concatenation of `n` copies of the list `l`. -/
def nTimes (l : List α) (n : ℕ) : List α :=
  (List.replicate n l).flatten

@[inherit_doc]
infixl:69 " ^+^ " => nTimes

variable {l : List α} {n : ℕ}

/--
@isnad1 id=eq.0h3v.s5.2df58a02e1b4 from=translated src=- shape=5df0958d vocab=52efa8fa
-/
lemma nTimes_succ_l : l^+^n.succ = l ++ l^+^n := by simp [nTimes, List.replicate_succ]

/--
@isnad1 id=eq.0h3v.s5.67ac79f54348 from=translated src=- shape=17f26815 vocab=52efa8fa
-/
lemma nTimes_succ_r : l^+^n.succ = l^+^n ++ l := by simp [nTimes, List.replicate_succ']

/--
@isnad1 id=eq.0h5v.s5.13842015d8cf from=translated src=- shape=0a4eba69 vocab=f1ff96d0
-/
lemma nTimes_map {β : Type _} {f : α → β} : (l.map f)^+^n = (l^+^n).map f := by simp [nTimes]

-- not used anywhere, just for fun
/--
@isnad1 id=eq.0h4v.s5.c8ad7628d28b from=translated src=- shape=47748144 vocab=9ab24f25
-/
lemma nTimes_add {m : ℕ} : l ^+^ (m + n) = l ^+^ m ++ l ^+^ n := by
  induction n with
  | zero => exact (l ^+^ m).append_nil.symm
  | succ _ ih => rw [Nat.add_succ, nTimes_succ_r, nTimes_succ_r, ih, List.append_assoc]

-- not used anywhere, just for fun
/--
@isnad1 id=eq.0h4v.s4.4005b7b711e1 from=translated src=- shape=43649c1e vocab=8c5026af
-/
lemma nTimes_mul {m : ℕ} : l ^+^ m * n = l ^+^ m ^+^ n := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Nat.mul_succ, nTimes_add, ih, nTimes_succ_r]
