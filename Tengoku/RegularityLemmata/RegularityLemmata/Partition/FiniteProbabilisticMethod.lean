/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Tactic.Push

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite probabilistic-method union bound

The deterministic endpoint of the equal-block sampling argument. Once each bad trace/block
event is represented by a finite set of permutations, a sum of their cardinalities strictly
below the permutation-space cardinality produces one permutation avoiding every event.
-/

open Finset

namespace RegularityLemmata

variable {Omega I : Type*} [Fintype Omega] [Fintype I] [DecidableEq Omega]

omit [Fintype Omega] in
/-- The union of all bad events has cardinality at most the sum of their cardinalities.
@isnad1 id=le.0h3v.s5.1fc7d3869ba1 from=translated src=- shape=58c9a427 vocab=bbc2e611
-/
theorem card_biUnion_le_sum_card (bad : I → Finset Omega) :
    (univ.biUnion bad).card ≤ ∑ i : I, (bad i).card := by
  exact card_biUnion_le

/-- If the sum of bad-event cardinalities is smaller than the finite sample space, some outcome
avoids every bad event.  This is the exact finite probabilistic-method step used after the
hypergeometric/permutation concentration estimate.
@isnad1 id=ex.1h3v.s5.91eb8a2f7c82 from=translated src=- shape=9622dcf5 vocab=2acad63a
-/
theorem exists_avoids_all_of_sum_card_lt (bad : I → Finset Omega)
    (hbad : ∑ i : I, (bad i).card < Fintype.card Omega) :
    ∃ omega : Omega, ∀ i : I, omega ∉ bad i := by
  have hunion : (univ.biUnion bad).card < Fintype.card Omega :=
    lt_of_le_of_lt (card_biUnion_le_sum_card bad) hbad
  by_contra hnone
  push Not at hnone
  have heq : univ.biUnion bad = (univ : Finset Omega) :=
    eq_univ_of_forall fun omega ↦ by
      obtain ⟨i, hi⟩ := hnone omega
      exact mem_biUnion.mpr ⟨i, mem_univ i, hi⟩
  rw [heq, card_univ] at hunion
  exact (lt_irrefl _ hunion)

/-- Uniform-cardinality corollary: at most `|I|` bad-event families, each of size at most `B`.
@isnad1 id=ex.2h4v.s6.a71b46615900 from=translated src=- shape=4de76b17 vocab=93013f3a
-/
theorem exists_avoids_all_of_uniform_bound (bad : I → Finset Omega) (B : ℕ)
    (hcard : ∀ i : I, (bad i).card ≤ B)
    (hsmall : Fintype.card I * B < Fintype.card Omega) :
    ∃ omega : Omega, ∀ i : I, omega ∉ bad i := by
  apply exists_avoids_all_of_sum_card_lt bad
  calc
    ∑ i : I, (bad i).card ≤ ∑ _i : I, B := Finset.sum_le_sum fun i _ ↦ hcard i
    _ = Fintype.card I * B := by simp
    _ < Fintype.card Omega := hsmall

end RegularityLemmata
