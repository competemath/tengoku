/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.Seed.NumberTheory.NumberField.ClassNumber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Class Number Two from a Two-Element Class Group

Material destined for mathlib.

If every ideal class of a number field `K` is either the trivial class or a
fixed nontrivial class `C₀`, then the class number of `K` is exactly `2`. This
is the closing step of hand computations of class number two (e.g. for
`ℚ(√-5)`).
-/

open scoped NumberField

namespace NumberField

/-- If every ideal class is `1` or a fixed class `C₀ ≠ 1`, the class number
is `2`.
@isnad1 id=eq.2h2v.s7.ac52c06f0754 from=translated src=- shape=cd0d4bda vocab=16bf56fa
-/
theorem classNumber_eq_two_of_forall_eq_one_or
    {K : Type*} [Field K] [NumberField K] {C₀ : ClassGroup (𝓞 K)}
    (hC₀ : C₀ ≠ 1) (h : ∀ C : ClassGroup (𝓞 K), C = 1 ∨ C = C₀) :
    classNumber K = 2 := by
  rw [classNumber, Fintype.card_eq_nat_card, Nat.card_eq_two_iff]
  refine ⟨1, C₀, Ne.symm hC₀, ?_⟩
  ext C
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm] using h C

end NumberField
