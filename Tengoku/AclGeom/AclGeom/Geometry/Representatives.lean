/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.FiniteRank
import Tengoku.AclGeom.AclGeom.Transfer.Transcendence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite representative calculus

Blueprint Lemma `finite-representative-calculus` (Lemma 4.2), for tuples
`v₁, …, vₙ ∈ K`:

* (a) independence is the absence of closure membership among the entries —
  `algebraicIndependent_iff_forall_notMem_racl` (`AclGeom.Closure.Basic`);
* (b) replacing each entry by an interalgebraic one preserves independence
  (`algebraicIndependent_congr_racl`), the closure of the tuple
  (`racl_range_congr`), its matroid rank (`eRk_range_congr`) and the join of
  its points (`iSup_point_congr`, `AclGeom.Geometry.FiniteRank`);
* (c) rank below the transcendence degree leaves room for fresh elements:
  `exists_notMem_racl_of_eRk_lt` and the two-step
  `exists_two_fresh_of_eRk_add_two_le`; the cardinality forms used by the
  configuration layer are `exists_notMem_racl_of_card_lt_trdeg`,
  `fresh_three_of_five_le_trdeg` and `fresh_four_of_five_le_trdeg`
  (`AclGeom.Transfer.Transcendence`);
* (d) a change of coordinates whose new and old entries generate each other
  algebraically preserves independence
  (`AlgebraicIndependent.of_racl_range_eq`); the three changes listed in the
  blueprint are `algebraicIndependent_mul_mul_left`,
  `algebraicIndependent_mul_one_add` and `algebraicIndependent_mul_left`.

Many concrete instances of (b) and (d) are already proved where they are
used, for the witness tables (`qtable_indep_*`, `mtable_indep_*`); they are
not restated here.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (blueprint Lemma 4.2). Other foundational carryovers remain
tracked separately in issue #24.
-/

namespace AclGeom

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Congr

variable {ι : Type*} {v w : ι → K}

end Congr

section Fresh

end Fresh

section Birational

/-- **Lemma 4.2(d), general form**: an `n`-tuple generating the same
closure as an independent `n`-tuple is itself independent.  This covers
every birational (indeed every algebraic) change of coordinates.-/
theorem AlgebraicIndependent.of_racl_range_eq {n : ℕ} {v w : Fin n → K}
    (hv : AlgebraicIndependent k v)
    (h : racl k (Set.range v) = racl k (Set.range w)) :
    AlgebraicIndependent k w := by
  refine algebraicIndependent_of_rankEq_iSup_point ?_
  have hv' := rankEq_iSup_point hv
  refine hv'.congr (iSup_point_congr h)

/-- Mutual membership of the entries gives equal closures.-/
theorem racl_range_eq_of_mem {n m : ℕ} {v : Fin n → K} {w : Fin m → K}
    (hw : ∀ j, w j ∈ racl k (Set.range v)) (hv : ∀ i, v i ∈ racl k (Set.range w)) :
    racl k (Set.range v) = racl k (Set.range w) :=
  racl_congr_of_subset_racl (by rintro _ ⟨i, rfl⟩; exact hv i)
    (by rintro _ ⟨j, rfl⟩; exact hw j)

variable {x y a : K}

end Birational

section Triples

/-! Sub-pairs of independent triples and insertion of fresh elements, used by the direct-link
soundness proofs (`AclGeom.Interpretation.FrobLinkSoundness`).  Moved from
`AclGeom.Counterexamples.GenericArithmetic`; `insert_middle` now proves `range_pair` inline, which
lives in `AclGeom.Config.Quadrangle`. -/

/-- A pair taken from the entries of an independent triple is independent.-/
theorem AlgebraicIndependent.pair_of_triple {u v w : K}
    (h : AlgebraicIndependent k ![u, v, w]) {i j : Fin 3} (hij : i ≠ j) :
    AlgebraicIndependent k ![![u, v, w] i, ![u, v, w] j] := by
  have hinj : Function.Injective ![i, j] := by
    intro m n hmn
    fin_cases m <;> fin_cases n <;> simp_all [eq_comm]
  have := h.comp ![i, j] hinj
  convert this using 1
  ext m
  fin_cases m <;> rfl

/-- The entries `0, 2` of an independent triple are independent.-/
theorem AlgebraicIndependent.pair_zero_two {p q r : K} (h : AlgebraicIndependent k ![p, q, r]) :
    AlgebraicIndependent k ![p, r] :=
  AlgebraicIndependent.pair_of_triple h (i := 0) (j := 2) (by decide)

/-- The entries `1, 2` of an independent triple are independent.-/
theorem AlgebraicIndependent.pair_one_two {p q r : K} (h : AlgebraicIndependent k ![p, q, r]) :
    AlgebraicIndependent k ![q, r] :=
  AlgebraicIndependent.pair_of_triple h (i := 1) (j := 2) (by decide)

/-- `1 + r` is nonzero for the last entry `r` of an independent triple.-/
theorem AlgebraicIndependent.one_add_ne_zero_two {p q r : K}
    (hind : AlgebraicIndependent k ![p, q, r]) : 1 + r ≠ 0 := fun h ↦ hind.transcendental 2 (by
  change IsAlgebraic k r
  rw [show r = algebraMap k K (-1) by rw [map_neg, map_one]; linear_combination h]
  exact isAlgebraic_algebraMap _)

/-- Two triples generating the same closure are simultaneously independent.-/
theorem AlgebraicIndependent.triple_of_mem {u v w u' v' w' : K}
    (h : AlgebraicIndependent k ![u, v, w])
    (h₁ : ∀ i, ![u', v', w'] i ∈ racl k (Set.range ![u, v, w]))
    (h₂ : ∀ i, ![u, v, w] i ∈ racl k (Set.range ![u', v', w'])) :
    AlgebraicIndependent k ![u', v', w'] :=
  AlgebraicIndependent.of_racl_range_eq h (racl_range_eq_of_mem h₁ h₂)

/-- Insert a fresh element in the middle of an independent pair.-/
theorem AlgebraicIndependent.insert_middle {p q t : K} (h : AlgebraicIndependent k ![p, q])
    (ht : t ∉ racl k ({p, q} : Set K)) : AlgebraicIndependent k ![p, t, q] := by
  have h3 : AlgebraicIndependent k ![p, q, t] := by
    have hr : Set.range ![p, q] = ({p, q} : Set K) := by
      ext z
      simp [Matrix.range_cons, Matrix.range_empty]
      tauto
    have hs := algebraicIndependent_snoc h (z := t) (by rwa [hr])
    convert hs using 1
    funext i
    fin_cases i <;> rfl
  have := h3.comp ![0, 2, 1] (by decide)
  convert this using 1
  funext i
  fin_cases i <;> rfl

/-- Insert a fresh element in front of an independent pair.-/
theorem AlgebraicIndependent.insert_left {p q t : K} (h : AlgebraicIndependent k ![p, q])
    (ht : t ∉ racl k ({p, q} : Set K)) : AlgebraicIndependent k ![t, p, q] := by
  have := (AlgebraicIndependent.insert_middle h ht).comp ![1, 0, 2] (by decide)
  convert this using 1
  funext i
  fin_cases i <;> rfl

end Triples

end

end AclGeom
