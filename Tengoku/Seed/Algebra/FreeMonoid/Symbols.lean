/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.FreeMonoid.Basic
public import Tengoku.Seed.Data.Finset.Lattice.Lemmas

/-!
# The finite set of symbols in a FreeMonoid element

This is separated from the main FreeMonoid file, as it imports the finiteness hierarchy
-/

@[expose] public section

variable {α : Type*} [DecidableEq α]

namespace FreeMonoid

/-- the set of unique symbols in a free monoid element -/
@[to_additive /-- The set of unique symbols in an additive free monoid element -/]
def symbols (a : FreeMonoid α) : Finset α := List.toFinset a

/--
@isnad1 id=eq.0h1v.s5.df6a2b781831 from=seed src=0 shape=776cc157 vocab=141612c2
-/
@[to_additive (attr := simp)]
theorem symbols_one : symbols (1 : FreeMonoid α) = ∅ := rfl

/--
@isnad1 id=eq.0h2v.s4.8d34368a4837 from=seed src=0 shape=0ba07cec vocab=b3c4d480
-/
@[to_additive (attr := simp)]
theorem symbols_of {m : α} : symbols (of m) = {m} := rfl

/--
@isnad1 id=eq.0h3v.s5.f69283b9a541 from=seed src=0 shape=c4226983 vocab=5e34cd16
-/
@[to_additive (attr := simp)]
theorem symbols_mul {a b : FreeMonoid α} : symbols (a * b) = symbols a ∪ symbols b :=
  List.toFinset_append

/--
@isnad1 id=iff.0h3v.s5.7ef2107e92ba from=seed src=0 shape=07553638 vocab=d3323cdf
-/
@[to_additive (attr := simp)]
theorem mem_symbols {m : α} {a : FreeMonoid α} : m ∈ symbols a ↔ m ∈ a :=
  List.mem_toFinset

end FreeMonoid
