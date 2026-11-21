/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosConvexHull
import Tengoku.Randomsettheory.RandomSetTheory.Geometry
import Tengoku.Seed.Analysis.Convex.Caratheodory
import Tengoku.Seed.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite depth of iterated binary convexification

In a finite-dimensional real vector space, the binary convexification
procedure `convexJoinIterate` stabilizes after an explicit finite number of
steps.  The proof first shows by induction that the convex hull of a finset
of cardinality `m` is contained in stage `m`, then applies Carathéodory's
theorem to reduce every convex combination to at most `finrank + 1` points.
-/

open Set Module

noncomputable section

namespace RandomSetTheory

/-- The convex hull of a finite subset of `S` is reached no later than the
binary-convexification stage indexed by its cardinality.-/
theorem convexHull_finset_subset_convexJoinIterate_card
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : S.Nonempty) (T : Finset E)
    (hTS : (T : Set E) ⊆ S) :
    convexHull ℝ (T : Set E) ⊆ convexJoinIterate S T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      have haS : a ∈ S := hTS (by simp)
      have hTS' : (T : Set E) ⊆ S := by
        intro x hx
        exact hTS (by simp [hx])
      rw [Finset.card_insert_of_notMem ha]
      by_cases hT : T.Nonempty
      · rw [Finset.coe_insert, convexHull_insert (by simpa using hT),
          convexJoinIterate_succ]
        apply convexJoin_mono
        · intro x hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          exact convexJoinIterate_mono_nat hS (Nat.zero_le T.card) haS
        · exact ih hTS'
      · rw [Finset.not_nonempty_iff_eq_empty] at hT
        subst T
        simpa only [Finset.coe_insert, Finset.coe_empty, insert_empty_eq,
          Finset.coe_singleton, convexHull_singleton, Finset.card_empty,
          convexJoinIterate_succ,
          convexJoinIterate_zero] using
          (Set.singleton_subset_iff.mpr haS).trans
            (subset_convexJoin_left (𝕜 := ℝ) (s := S) (t := S) hS)

/-- Carathéodory's theorem gives a uniform finite stage at which iterated
binary convexification reaches the whole convex hull.-/
theorem convexHull_subset_convexJoinIterate_finrank_add_one
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : S.Nonempty) :
    convexHull ℝ S ⊆
      convexJoinIterate S (finrank ℝ E + 1) := by
  rw [convexHull_eq_union]
  intro x hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨T, hTS, hTind, hxT⟩ := hx
  have hcard : T.card ≤ finrank ℝ E + 1 := by
    simpa only [Fintype.card_coe] using
      hTind.card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  exact convexJoinIterate_mono_nat hS hcard
    (convexHull_finset_subset_convexJoinIterate_card hS T hTS hxT)

/-- In a finite-dimensional real vector space, the `finrank + 1` stage of
binary convexification is exactly the convex hull.-/
theorem convexJoinIterate_finrank_add_one_eq_convexHull
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : S.Nonempty) :
    convexJoinIterate S (finrank ℝ E + 1) = convexHull ℝ S := by
  apply Set.Subset.antisymm
  · exact convexJoinIterate_subset_convex
      (subset_convexHull ℝ S) (convex_convexHull ℝ S) _
  · exact convexHull_subset_convexJoinIterate_finrank_add_one hS

/-- For a compact nonempty set in a finite-dimensional normed space, the
same finite stage is also the closed convex hull.-/
theorem convexJoinIterate_finrank_add_one_eq_closedConvexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {S : Set E} (hScompact : IsCompact S) (hS : S.Nonempty) :
    convexJoinIterate S (finrank ℝ E + 1) = closedConvexHull ℝ S := by
  have hstage := convexJoinIterate_finrank_add_one_eq_convexHull hS
  have hhullClosed : IsClosed (convexHull ℝ S) := by
    rw [← hstage]
    exact (convexJoinIterate_compact hScompact _).isClosed
  rw [hstage, closedConvexHull_eq_closure_convexHull,
    hhullClosed.closure_eq]

/-- The convex hull of a compact nonempty set is already closed in finite
dimension, hence agrees with the closed convex hull.-/
theorem convexHull_eq_closedConvexHull_of_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {S : Set E} (hScompact : IsCompact S) (hS : S.Nonempty) :
    convexHull ℝ S = closedConvexHull ℝ S := by
  rw [← convexJoinIterate_finrank_add_one_eq_convexHull hS,
    convexJoinIterate_finrank_add_one_eq_closedConvexHull hScompact hS]

/-- Compactness of the ordinary convex hull of a compact nonempty set in
finite dimension.-/
theorem convexHull_compact_of_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {S : Set E} (hScompact : IsCompact S) (hS : S.Nonempty) :
    IsCompact (convexHull ℝ S) := by
  rw [convexHull_eq_closedConvexHull_of_compact hScompact hS]
  exact closedConvexHull_compact hScompact

end RandomSetTheory
