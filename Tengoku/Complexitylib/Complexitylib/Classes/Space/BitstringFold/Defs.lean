/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Mathlib.NatBits

/-!
# Ordered folds over fixed-width bitstrings

The first `count` strings are enumerated by their little-endian numeric value.
The complete fold visits all `2 ^ width` strings, including the single empty
string when `width = 0`. The update need not be associative or commutative.
-/

@[expose] public section

namespace Complexity

/-- Fold over the first `count` fixed-width bitstrings in little-endian numeric
order. Prefixes past `2 ^ width` repeat candidates; the space theorem only
bounds and uses prefixes up to that endpoint. -/
def bitstringFoldPrefix (update : List Bool → List Bool → List Bool)
    (seed : List Bool) (width : ℕ) : ℕ → List Bool
  | 0 => seed
  | count + 1 => update (Nat.toBitsLE width count)
      (bitstringFoldPrefix update seed width count)

/--
@isnad1 id=eq.0h3v.s4.9972cee12c9a from=translated src=- shape=754dc655 vocab=5797d492
-/
@[simp] theorem bitstringFoldPrefix_zero (update : List Bool → List Bool → List Bool)
    (seed : List Bool) (width : ℕ) : bitstringFoldPrefix update seed width 0 = seed := rfl

/--
@isnad1 id=eq.0h4v.s5.01508c25ff2a from=translated src=- shape=fc8c729a vocab=89ee6542
-/
@[simp] theorem bitstringFoldPrefix_succ (update : List Bool → List Bool → List Bool)
    (seed : List Bool) (width count : ℕ) :
    bitstringFoldPrefix update seed width (count + 1) =
      update (Nat.toBitsLE width count) (bitstringFoldPrefix update seed width count) := rfl

/-- Fold over every string of exactly `width` bits, in little-endian numeric order. -/
def bitstringFold (update : List Bool → List Bool → List Bool)
    (seed : List Bool) (width : ℕ) : List Bool :=
  bitstringFoldPrefix update seed width (2 ^ width)

/-- A zero-width fold still performs one update, with the empty candidate.
@isnad1 id=eq.0h2v.s4.a0d8dda02664 from=translated src=- shape=5ad2f797 vocab=f6fa5c7c
-/
@[simp] theorem bitstringFold_zero (update : List Bool → List Bool → List Bool)
    (seed : List Bool) : bitstringFold update seed 0 = update [] seed := rfl

end Complexity
