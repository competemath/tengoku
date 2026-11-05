/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.AclGeom.AclGeom.Transfer.Intersections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transcendence degree and fresh elements

The transfer and configuration layers use a small fresh-element oracle:
outside the relative algebraic closure of every parameter set of bounded
finite size, another element exists.  This module derives that oracle from
the blueprint's transcendence-degree hypothesis.

The proof is the contrapositive of the standard generator bound.  If every
element of `K` is algebraic over the ring `k[S]`, then
`Algebra.trdeg k K ≤ #S`; therefore a set whose cardinality is strictly
below the transcendence degree cannot span the algebraic-independence
matroid.

**Status:** complete (M5 transcendence-degree interface).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A set of cardinality strictly below `trdeg_k K` does not relatively
algebraically generate all of `K`.-/
theorem exists_notMem_racl_of_mk_lt_trdeg (S : Set K)
    (hS : Cardinal.mk S < Algebra.trdeg k K) :
  ∃ z : K, z ∉ racl k S := by
  by_contra h
  push Not at h
  letI : Algebra.IsAlgebraic (Algebra.adjoin k S) K := ⟨fun z ↦
    (mem_racl_iff_isAlgebraic_adjoin
      (k := k) (S := S) (x := z)).1 (h z)⟩
  exact (not_le_of_gt hS) (Algebra.IsAlgebraic.trdeg_le_cardinalMk k S)

/-- A natural lower bound on transcendence degree supplies a fresh element
over every finite parameter set of smaller cardinality.-/
theorem exists_notMem_racl_of_card_lt_trdeg {n : ℕ}
    (htr : (n : Cardinal) < Algebra.trdeg k K)
    (S : Finset K) (hS : S.card ≤ n) :
  ∃ z : K, z ∉ racl k (S : Set K) := by
  apply exists_notMem_racl_of_mk_lt_trdeg (S : Set K)
  change Cardinal.mk S < Algebra.trdeg k K
  rw [Cardinal.mk_coe_finset]
  have hScard : (S.card : Cardinal) ≤ (n : Cardinal) := by
    exact_mod_cast hS
  exact hScard.trans_lt htr

/-- The rank-five hypothesis used by the 21-point configuration gives its
four-parameter fresh-element oracle.-/
theorem fresh_four_of_five_le_trdeg
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    ∀ S : Finset K, S.card ≤ 4 → ∃ z, z ∉ racl k (S : Set K) := by
  intro S hS
  apply exists_notMem_racl_of_card_lt_trdeg
    (n := 4) (lt_of_lt_of_le (by norm_num) htr) S hS

/-- The same rank-five hypothesis gives the three-parameter oracle used by
the j-rigidity descent argument.-/
theorem fresh_three_of_five_le_trdeg
    (htr : (5 : Cardinal) ≤ Algebra.trdeg k K) :
    ∀ S : Finset K, S.card ≤ 3 → ∃ z, z ∉ racl k (S : Set K) := by
  intro S hS
  apply exists_notMem_racl_of_card_lt_trdeg
    (n := 3) (lt_of_lt_of_le (by norm_num) htr) S hS

end

end AclGeom
