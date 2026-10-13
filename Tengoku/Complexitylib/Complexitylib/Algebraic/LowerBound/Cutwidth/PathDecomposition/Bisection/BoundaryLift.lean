/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.TreeComponent
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Internal

/-!
# From red/black witnesses to helpful moves

This is the lifting step in Monien and Preis's bounded helpful-set proof.
Assume that the boundary `C` of a side `S` is independent and every boundary
vertex has one outside neighbor. In a cubic graph each vertex of `C` then
has two neighbors in `S \ C`, and represents a red edge between them.
The original edges between vertices of `S \ C` are black.

For an interior set `X`, the lift adds every boundary vertex adjacent to it.
Its helpfulness equals its internal red edges minus its external black
edges. Different boundary vertices are counted separately, even when they
represent parallel red edges. `BoundaryNormalization` supplies these
hypotheses, and `RedBlack.Clusters` proves the bounded positive-witness
theorem. `Helpful` composes the three steps.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

omit [Fintype W] in
/-- The lift stays in the original side.
@isnad1 id=le.1h4v.s5.4c37c9053551 from=translated src=- shape=e241d836 vocab=27228212
-/
theorem boundaryLift_subset {S X : Finset W} (hX : X ⊆ S) : boundaryLift H S X ⊆ S :=
  Internal.boundaryLift_subset H hX

/-- In a subcubic graph, each selected vertex adds at most three boundary vertices.
@isnad1 id=le.1h4v.s6.0bb2a88602d2 from=translated src=- shape=193a651f vocab=cd463bbe
-/
theorem card_boundaryLift_le {S X : Finset W} (degree : ∀ v ∈ X, H.degree v ≤ 3) :
    (boundaryLift H S X).card ≤ 4 * X.card :=
  Internal.card_boundaryLift_le H degree

/-- With one crossing edge per boundary vertex, cut size equals boundary size.
@isnad1 id=eq.1h3v.s6.939d086a4fc6 from=translated src=- shape=bacb0324 vocab=e96a400c
-/
theorem card_cutBoundary_eq_cut {S : Finset W}
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1) :
    (cutBoundary H S).card = (H.cutFinset S).card :=
  Internal.card_cutBoundary_eq_cut H outside

/-- Each normalized boundary vertex represents an edge with two distinct interior endpoints.
@isnad1 id=eq.4h4v.s8.a63195f93abd from=translated src=- shape=1eb87ff5 vocab=3b5ca14c
-/
theorem card_boundary_interior_neighbors {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    {c : W} (hc : c ∈ cutBoundary H S) :
    (H.neighborFinset c ∩ (S \ cutBoundary H S)).card = 2 :=
  Internal.card_boundary_interior_neighbors H regular outside independent hc

/-- The red and black incidence counts of an interior vertex sum to three.
@isnad1 id=eq.2h4v.s7.f5201d1aa243 from=translated src=- shape=113c0c52 vocab=ae105d0f
-/
theorem card_interior_neighbors {S : Finset W} (regular : H.IsRegularOfDegree 3)
    {v : W} (hv : v ∈ S \ cutBoundary H S) :
    (H.neighborFinset v ∩ cutBoundary H S).card +
      (H.neighborFinset v ∩ (S \ cutBoundary H S)).card = 3 :=
  Internal.card_interior_neighbors H regular hv

/-- Cut density above `1/3 + ξ` gives red-edge density above `1/2 + 3 ξ / 2`
in the suppressed graph.
@isnad1 id=lt.3h4v.s8.9b9fc0957b02 from=translated src=- shape=2992dabb vocab=c168f6dd
-/
theorem boundary_red_density {S : Finset W} {ξ : ℝ} (hξ : 0 < ξ)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (dense : (1 / 3 + ξ) * S.card < (H.cutFinset S).card) :
    (1 / 2 + 3 * ξ / 2) * (S \ cutBoundary H S).card < (cutBoundary H S).card :=
  Internal.boundary_red_density H hξ outside dense

/-- The suppressed graph has total red-plus-black degree three. Red edges
are counted as boundary vertices, retaining their multiplicities.
@isnad1 id=eq.3h3v.s9.ab5a08426ff4 from=translated src=- shape=79526eff vocab=3abdc6c3
-/
theorem card_interior_edges {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d) :
    2 * (H.induce {v | v ∈ S \ cutBoundary H S}).edgeFinset.card +
      2 * (cutBoundary H S).card = 3 * (S \ cutBoundary H S).card :=
  Internal.card_interior_edges H regular outside independent

/-- Positive cut-density slack forces a black tree component with uniformly
bounded size. This alone does not ensure a positive red/black witness.
@isnad1 id=ex.6h5v.s10.adbe2e0f90d6 from=translated src=- shape=21280834 vocab=0bcc48e5
-/
theorem exists_small_interior_tree_component {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    {ξ : ℝ} (hξ : 0 < ξ)
    (dense : (1 / 3 + ξ) * S.card < (H.cutFinset S).card) (M : Nat)
    (budget : 1 ≤ ((M : ℝ) + 1) * (3 * ξ / 2)) :
    ∃ C : (H.induce {v | v ∈ S \ cutBoundary H S}).ConnectedComponent,
      C.toSimpleGraph.IsTree ∧ Fintype.card C ≤ M :=
  Internal.exists_small_interior_tree_component H regular outside independent hξ dense M budget

/-- The lift's helpfulness is exactly internal red edges minus external black edges.
@isnad1 id=eq.4h4v.s8.58ad1a843a99 from=translated src=- shape=bb35588d vocab=6fb4efa7
-/
theorem helpfulness_boundaryLift {S X : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    (hX : X ⊆ S \ cutBoundary H S) :
    helpfulness H S (boundaryLift H S X) = (sharedBoundary H S X).card -
      ((H.cutFinset X \ H.cutFinset (cutBoundary H S)).card : ℤ) :=
  Internal.helpfulness_boundaryLift H regular outside independent hX

/-- A positive red/black witness produces a helpful set of at most four times its size.
@isnad1 id=ex.5h4v.s8.ca78c473e29e from=translated src=- shape=40efba23 vocab=c711e0bd
-/
theorem exists_helpful_set_of_red_surplus {S X : Finset W}
    (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    (hX : X ⊆ S \ cutBoundary H S)
    (positive : (H.cutFinset X \ H.cutFinset (cutBoundary H S)).card <
      (sharedBoundary H S X).card) :
    ∃ Y ⊆ S, Y.card ≤ 4 * X.card ∧ 1 ≤ helpfulness H S Y :=
  Internal.exists_helpful_set_of_red_surplus H regular outside independent hX positive

end Algebraic.Cutwidth.Bisection
