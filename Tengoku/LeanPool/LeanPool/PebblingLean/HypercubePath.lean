/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import Tengoku.LeanPool.LeanPool.PebblingLean.Hypercube
public import Tengoku.LeanPool.LeanPool.PebblingLean.Delivery
public import Tengoku

/-!
# Paths in hypercubes

This file connects Hamming distance to the graph-walk API: vertices at Hamming
distance `d` are joined by a walk of length `d`.  This is the geometric input
needed for direct delivery in the upper-bound proof.
-/

@[expose] public section

namespace PebblingLean

namespace Hypercube

open Pebbling

/--
@isnad1 id=eq.0h2v.s4.e82495d5ad51 from=translated src=- shape=c1aab5f2 vocab=d1365db7
-/
@[simp]
theorem fromDiffSet_empty {n : ℕ} (base : HypercubeVertex n) :
    fromDiffSet base ∅ = base := by
  funext i
  simp [fromDiffSet]

/--
@isnad1 id=eq.1h4v.s6.cda4f149d792 from=translated src=- shape=b90fc566 vocab=2fefa430
-/
theorem diffSet_fromDiffSet_insert {n : ℕ} (base : HypercubeVertex n)
    {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) :
    diffSet (fromDiffSet base s) (fromDiffSet base (insert i s)) = {i} := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [diffSet, fromDiffSet, hi]
  · have hj_insert : j ∈ insert i s ↔ j ∈ s := by
      simp [hji]
    by_cases hjs : j ∈ s
    · simp [diffSet, fromDiffSet, hji, hjs]
    · simp [diffSet, fromDiffSet, hji, hjs]

/-- Flipping one new coordinate gives an adjacent hypercube vertex.
@isnad1 id=adj.1h4v.s5.f26dc0d710c9 from=translated src=- shape=ef69768c vocab=cce2fa31
-/
theorem adj_fromDiffSet_insert {n : ℕ} (base : HypercubeVertex n)
    {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) :
    (graph n).Adj (fromDiffSet base s) (fromDiffSet base (insert i s)) := by
  simp [graph, dist_eq_card_diffSet, diffSet_fromDiffSet_insert base hi]

/-- Flipping the coordinates in `s`, one at a time, gives a walk back to the
base vertex of length `s.card`.
@isnad1 id=ex.0h3v.s5.f0f71fc39fee from=translated src=- shape=e2e14a4f vocab=e02231cf
-/
theorem exists_walk_fromDiffSet_to_base {n : ℕ} (base : HypercubeVertex n)
    (s : Finset (Fin n)) :
    ∃ walk : (graph n).Walk (fromDiffSet base s) base, walk.length = s.card := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · refine ⟨Graph.Walk.nil base, ?_⟩
    simp [Graph.Walk.length]
  · intro i s hi ih
    rcases ih with ⟨tail, htail⟩
    refine ⟨Graph.Walk.cons ((graph n).symm (adj_fromDiffSet_insert base hi)) tail, ?_⟩
    simp [Graph.Walk.length, htail, Finset.card_insert_of_notMem hi]

/-- Hypercube Hamming distance is realized by a graph walk of the same length.
@isnad1 id=ex.0h3v.s5.af8537bcbdde from=translated src=- shape=bcc1c397 vocab=4141d71c
-/
theorem exists_walk_length_dist {n : ℕ} (x y : HypercubeVertex n) :
    ∃ walk : (graph n).Walk x y, walk.length = dist x y := by
  classical
  rcases exists_walk_fromDiffSet_to_base x (diffSet x y) with ⟨walkToBase, hlen⟩
  have htarget : fromDiffSet x (diffSet x y) = y := fromDiffSet_diffSet x y
  rw [← htarget]
  refine ⟨Graph.Walk.reverse (graph n) walkToBase, ?_⟩
  simp [Graph.Walk.length_reverse, hlen, dist_eq_card_diffSet]

/-- A single pile of `T * 2^d` pebbles can directly deliver `T` pebbles across
Hamming distance `d`.
@isnad1 id=canreach.0h4v.s6.7aada7a63b76 from=translated src=- shape=e35399af vocab=500b2b7b
-/
theorem canReachAtLeast_single_dist {n : ℕ} (center target : HypercubeVertex n)
    (T : ℕ) :
    CanReachAtLeast (graph n)
      (Pebbling.single center (T * 2 ^ dist center target)) target T := by
  rcases exists_walk_length_dist center target with ⟨walk, hwalk⟩
  simpa [hwalk] using Pebbling.canReachAtLeast_single_of_walk walk T

end Hypercube

end PebblingLean
