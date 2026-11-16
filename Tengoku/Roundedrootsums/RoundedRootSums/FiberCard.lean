/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fiber cardinality lemmas

Auxiliary lemmas expressing the cardinality of filtered Cartesian products
as sums over the fibers of the first or second coordinate.

These lemmas are used in the double-counting proof.
-/

namespace RoundedRootSums

variable {α β : Type*}

/--
The cardinality of a filtered Cartesian product, computed by summing
the cardinalities of the fibers over the first coordinate.
@isnad1 id=eq.0h5v.s6.9faf712911d3 from=translated src=- shape=436e7284 vocab=9e0cc559
-/
theorem card_filter_product_eq_sum
    (A : Finset α)
    (B : Finset β)
    (P : α → β → Prop)
    [DecidableRel P] :
    ((A.product B).filter
        (fun p => P p.1 p.2)).card =
      Finset.sum A
        (fun a =>
          (B.filter (fun b => P a b)).card) := by
  classical
  simp only [Finset.card_filter]
  simpa using
    (Finset.sum_product' A B
      (fun a b => if P a b then (1 : Nat) else 0))

/--
The cardinality of a filtered Cartesian product, computed by summing
the cardinalities of the fibers over the second coordinate.
@isnad1 id=eq.0h5v.s6.0779f1e2520e from=translated src=- shape=aa60be59 vocab=9e0cc559
-/
theorem card_filter_product_eq_sum_right
    (A : Finset α)
    (B : Finset β)
    (P : α → β → Prop)
    [DecidableRel P] :
    ((A.product B).filter
        (fun p => P p.1 p.2)).card =
      Finset.sum B
        (fun b =>
          (A.filter (fun a => P a b)).card) := by
  classical
  simp only [Finset.card_filter]
  calc
    (∑ p ∈ A.product B,
        if P p.1 p.2 then (1 : Nat) else 0) =
      ∑ a ∈ A,
        ∑ b ∈ B,
          if P a b then (1 : Nat) else 0 := by
      simpa using
        (Finset.sum_product' A B
          (fun a b => if P a b then (1 : Nat) else 0))
    _ =
      ∑ b ∈ B,
        ∑ a ∈ A,
          if P a b then (1 : Nat) else 0 := by
      rw [Finset.sum_comm]

end RoundedRootSums
