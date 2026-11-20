/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/
import Tengoku.Seed.Data.Finset.Prod
import Tengoku.Seed.Data.Int.Interval
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.RcsrLeanProofs.RcsrProofs.Bcs.Distance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shell partition for the bcs coordination sequence

The shell of radius `n` (states at graph distance exactly `n` from the base)
is confined to the box `[-n, n]³` by `dist_box`, hence finite; partitioning it
by vertex class expresses its cardinality as the sum of the eight class-wise
level-set counts. The per-class counts are computed in `CountEven.lean` and
`CountOdd.lean`; the closing arithmetic is in `SumIdentities.lean`.
-/

namespace Bcs

open Finset

/-- The coordinate box `[-n, n]³` as a finset of integer triples.-/
def box (n : ℕ) : Finset (Int × Int × Int) :=
  Icc (-(n : Int)) n ×ˢ Icc (-(n : Int)) n ×ˢ Icc (-(n : Int)) n

/-- Class-`v` level count: lattice points in the box where `D (v, ·) = n`.-/
def classCard (v : Fin 8) (n : ℕ) : ℕ :=
  ((box n).filter (fun p => D (v, p.1, p.2.1, p.2.2) = n)).card

/-- Shell count: states in the (finite) box slab at graph distance value `n`.-/
def shellCard (n : ℕ) : ℕ :=
  (((univ : Finset (Fin 8)) ×ˢ box n).filter (fun s => D s = n)).card

/-- The shell splits as the sum of the eight class counts.-/
theorem shellCard_eq_sum (n : ℕ) :
    shellCard n = ∑ v : Fin 8, classCard v n := by
  classical
  unfold shellCard classCard
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := (univ : Finset (Fin 8))) (fun s _ => mem_univ s.1)]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.card_bij' (fun s _ => s.2) (fun p _ => (v, p)) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hs ⊢
    obtain ⟨⟨hbox, hD⟩, hfst⟩ := hs
    rw [← hfst]
    exact ⟨hbox, hD⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨⟨hp.1, hp.2⟩, trivial⟩
  · intro s hs
    simp only [Finset.mem_filter] at hs
    obtain ⟨w, p2⟩ := s
    obtain ⟨-, hfst⟩ := hs
    subst hfst
    rfl
  · intro p _
    rfl
end Bcs
