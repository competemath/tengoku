/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Tengoku.Seed.Data.PNat.Order
import Tengoku.Seed.Order.Interval.Set.Infinite
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Power Structure of Monoid Elements

This file studies the sequence of powers of a monoid element, in particular the
dichotomy between having pairwise distinct powers and having an idempotent power,
and its consequences for finite monoids.

## Main results

* `Monoid.distinct_powers_or_idempotent_pow`: every monoid element either has
  pairwise distinct positive powers or has an idempotent positive power.
* `Monoid.forall_isUnit_or_exists_idempotent_pow_ne_one`: in a finite monoid, every
  element is a unit, or some element has an idempotent positive power different from `1`.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/

namespace Monoid

variable {M : Type*} [Monoid M]

/-- Auxiliary lemma: if the powers of `x` satisfy the recurrence
`x ^ (a + (e + 1)) = x ^ a` (eventual periodicity with period `e + 1`), then some
positive power of `x` is idempotent; the witness is `x ^ ((a + 1) * (e + 1))`.
@isnad1 id=ex.1h4v.s6.6f2653fb1c88 from=translated src=- shape=7df35ed6 vocab=61496d89
-/
lemma exists_idem_pow_aux (x : M) (a e : ℕ)
    (h : x ^ (a + (e + 1)) = x ^ a) :
    ∃ k : ℕ+, x ^ (k : ℕ) * x ^ (k : ℕ) = x ^ (k : ℕ) := by
  have per : ∀ c t : ℕ, x ^ (a + c + t * (e + 1)) = x ^ (a + c) := by
    intro c t
    induction t with
    | zero => simp
    | succ t ih =>
      have e1 : a + c + (t + 1) * (e + 1) = a + (e + 1) + (c + t * (e + 1)) := by ring
      have e2 : a + (c + t * (e + 1)) = a + c + t * (e + 1) := by ring
      rw [e1, pow_add, h, ← pow_add, e2, ih]
  refine ⟨⟨(a + 1) * (e + 1), Nat.mul_pos a.succ_pos e.succ_pos⟩, ?_⟩
  change x ^ ((a + 1) * (e + 1)) * x ^ ((a + 1) * (e + 1)) = x ^ ((a + 1) * (e + 1))
  have key := per (a * e + e + 1) (a + 1)
  have e3 : a + (a * e + e + 1) = (a + 1) * (e + 1) := by ring
  rw [e3] at key
  rw [← pow_add]
  exact key

/-- Every monoid element `x` either has pairwise distinct positive powers, or some
positive power of `x` is idempotent.
@isnad1 id=or.0h2v.s6.1134cf86136e from=translated src=- shape=d5142c85 vocab=9943236e
-/
theorem distinct_powers_or_idempotent_pow (x : M) :
    (∀ i j : ℕ+, i ≠ j → x ^ (i : ℕ) ≠ x ^ (j : ℕ)) ∨
    (∃ k : ℕ+, x ^ (k : ℕ) * x ^ (k : ℕ) = x ^ (k : ℕ)) := by
  by_cases h : ∀ i j : ℕ+, i ≠ j → x ^ (i : ℕ) ≠ x ^ (j : ℕ)
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨i, j, hij, heq⟩ := h
  have hne : (i : ℕ) ≠ (j : ℕ) := by exact_mod_cast hij
  rcases hne.lt_or_gt with hgt | hlt
  · obtain ⟨e, he⟩ : ∃ e, (j : ℕ) = (i : ℕ) + (e + 1) :=
      ⟨(j : ℕ) - (i : ℕ) - 1, by omega⟩
    exact exists_idem_pow_aux x (i : ℕ) e (by rw [← he]; exact heq.symm)
  · obtain ⟨e, he⟩ : ∃ e, (i : ℕ) = (j : ℕ) + (e + 1) :=
      ⟨(i : ℕ) - (j : ℕ) - 1, by omega⟩
    exact exists_idem_pow_aux x (j : ℕ) e (by rw [← he]; exact heq)

/-- In a finite monoid, every element is a unit (so the monoid is a group), or some
element has an idempotent positive power different from `1`.
@isnad1 id=or.0h1v.s6.bfb976cbb427 from=translated src=- shape=7e22780e vocab=e7e0347e
-/
theorem forall_isUnit_or_exists_idempotent_pow_ne_one [Finite M] :
    (∀ x : M, IsUnit x) ∨
      ∃ (x : M) (k : ℕ+), x ^ (k : ℕ) * x ^ (k : ℕ) = x ^ (k : ℕ) ∧ x ^ (k : ℕ) ≠ 1 := by
  have key : ∀ x : M, ∃ k : ℕ+, x ^ (k : ℕ) * x ^ (k : ℕ) = x ^ (k : ℕ) := by
    intro x
    rcases distinct_powers_or_idempotent_pow x with hd | hi
    · exfalso
      have hinj : Function.Injective (fun i : ℕ+ => x ^ (i : ℕ)) := by
        intro i j hij
        by_contra hne
        exact hd i j hne hij
      exact not_injective_infinite_finite _ hinj
    · exact hi
  by_cases h : ∃ (x : M) (k : ℕ+), x ^ (k : ℕ) * x ^ (k : ℕ) = x ^ (k : ℕ) ∧ x ^ (k : ℕ) ≠ 1
  · exact Or.inr h
  · left
    push Not at h
    intro x
    obtain ⟨k, hk⟩ := key x
    have h1 : x ^ (k : ℕ) = 1 := h x k hk
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (k : ℕ) = m + 1 := ⟨(k : ℕ) - 1, by have := k.pos; omega⟩
    exact ⟨⟨x, x ^ m,
      by rw [← pow_succ', ← hm]; exact h1,
      by rw [← pow_succ, ← hm]; exact h1⟩, rfl⟩

end Monoid
