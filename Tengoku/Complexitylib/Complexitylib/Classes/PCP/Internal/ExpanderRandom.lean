/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.PermArith
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.PermCount

/-!
# A tuple of permutations that expands

The counting argument. Of the `(n!)^30` tuples of thirty permutations of
`Fin n`, not all can fail to expand: a tuple fails at a vertex set `S` of at
most half the vertices exactly when every one of its thirty permutations keeps
all but a tenth of `S` inside `S`. `PermCount` bounds how many permutations do
that for a fixed `S`; `PermArith.key_estimate` turns the thirtieth power of that
bound into `(n!)^30 / 2^{|S|}`, with room to spare for the `C(n,s)` sets of each
size; and summing `2^{-s}` over `s ≥ 1` stays below one.

Everything is done with natural numbers — the geometric series appears as an
induction that carries the slack `+ K` explicitly, so no division is needed.

## Main definitions

- `Complexity.escLE` — the permutations keeping all but `t` points of `S` in `S`
- `Complexity.tOf` — the escape a set of a given size is allowed

## Main results

- `Complexity.exists_good_perms` — a tuple of thirty permutations for which
  every set of at most half the vertices is moved out of itself, by at least a
  tenth of it, by one of them
-/

@[expose] public section

namespace Complexity

open Finset

variable {n : ℕ}

/-- The permutations moving at most `t` points of `S` out of `S`. -/
noncomputable def escLE (S : Finset (Fin n)) (t : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun σ => escape σ S ≤ t

/-- The escape a set of size `s` is allowed before it counts as expanding. -/
def tOf (S : Finset (Fin n)) : ℕ := (S.card - 1) / 10

theorem ten_mul_tOf_le (S : Finset (Fin n)) : 10 * tOf S ≤ S.card := by
  rw [tOf]
  omega

theorem mem_escLE_iff {S : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (hS : 1 ≤ S.card) :
    σ ∈ escLE S (tOf S) ↔ ¬ S.card ≤ 10 * escape σ S := by
  simp only [escLE, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold tOf
  omega

/-- The bound on how many permutations fail to expand a set of size `s`. -/
def escB (n s : ℕ) : ℕ :=
  s.choose ((s - 1) / 10) * s.descFactorial (s - (s - 1) / 10)
    * Nat.factorial (n - (s - (s - 1) / 10))

theorem card_escLE_le (S : Finset (Fin n)) : (escLE S (tOf S)).card ≤ escB n S.card := by
  have hts : tOf S ≤ S.card := by have := ten_mul_tOf_le S; omega
  have h := card_perm_escape_le S (tOf S)
  rw [Nat.choose_symm hts] at h
  rw [escLE, escB, ← tOf]
  calc (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => escape σ S ≤ tOf S).card
      ≤ S.card.choose (tOf S)
        * (S.card.descFactorial (S.card - tOf S) * Nat.factorial (n - (S.card - tOf S))) := h
    _ = S.card.choose (tOf S) * S.card.descFactorial (S.card - tOf S)
        * Nat.factorial (n - (S.card - tOf S)) := by ring

/-! ### The geometric slack -/

/-! ### The union bound -/

end Complexity
