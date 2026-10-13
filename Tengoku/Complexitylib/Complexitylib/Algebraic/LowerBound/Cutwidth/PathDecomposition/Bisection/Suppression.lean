/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Suppression.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Suppression.Internal

/-!
# The suppressed graph and its helpful-set transfer

An independent boundary with one outside neighbor per vertex in a cubic
graph has a loopless red suppression. The original interior edges form the
black graph. The red and black degrees sum to three, internal red edges
count shared boundary vertices, and black cuts count the remaining interior
crossings. Thus every positive red/black set lifts to a helpful move.

`NeighborNormalization` supplies normalization of an arbitrary cubic side,
unless a uniformly small helpful set already exists. Its exclusion of
interior vertices with three boundary neighbors ensures positive black degree.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection

open scoped Classical

/-- Suppress each boundary vertex to the red edge joining its two interior neighbors.
@isnad1 id=nonempty.3h3v.s7.ed4221eaab6e from=translated src=- shape=d72543cf vocab=c6bf7800
-/
theorem exists_boundarySuppression {W : Type} [Fintype W] (H : SimpleGraph W)
    {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d) :
    Nonempty (BoundarySuppression H S) :=
  Internal.exists_boundarySuppression H regular outside independent

/-- The cut in the black graph equals the original cut after removing edges
incident to the boundary.
@isnad1 id=eq.0h4v.s8.8fd3f8134ae4 from=translated src=- shape=85135658 vocab=a07a9f19
-/
theorem boundaryInterior_cut_card {W : Type} [Fintype W] (H : SimpleGraph W) {S : Finset W}
    (X : Finset {v : W // v ∈ S \ cutBoundary H S}) :
    ((H.induce {v | v ∈ S \ cutBoundary H S}).cutFinset X).card =
      (H.cutFinset (X.map (Function.Embedding.subtype _)) \
        H.cutFinset (cutBoundary H S)).card :=
  Internal.boundaryInterior_cut_card H X

namespace BoundarySuppression

variable {W : Type} [Fintype W] {H : SimpleGraph W} {S : Finset W}
  (Q : BoundarySuppression H S)

/-- Red degree counts the original boundary neighbors.
@isnad1 id=eq.0h5v.s8.cc4f555562d5 from=translated src=- shape=cd5d4f3b vocab=45e06424
-/
theorem red_degree (v : {v : W // v ∈ S \ cutBoundary H S}) :
    Q.red.degree v = (H.neighborFinset v.val ∩ cutBoundary H S).card :=
  Internal.BoundarySuppression.red_degree H Q v

/-- Suppression preserves the total degree three at each interior vertex.
@isnad1 id=eq.1h5v.s9.eb90b5aaecf0 from=translated src=- shape=76450d9e vocab=7b4c0fab
-/
theorem degree_sum (regular : H.IsRegularOfDegree 3)
    (v : {v : W // v ∈ S \ cutBoundary H S}) :
    (H.induce {v | v ∈ S \ cutBoundary H S}).degree v + Q.red.degree v = 3 :=
  Internal.BoundarySuppression.degree_sum H Q regular v

/-- Internal red edges count shared boundary vertices, including parallel edges.
@isnad1 id=eq.0h5v.s7.1ac172ca2509 from=translated src=- shape=5f67e669 vocab=8a4a3d90
-/
theorem internalEdges_card (X : Finset {v : W // v ∈ S \ cutBoundary H S}) :
    (RedBlack.internalEdges Q.red X).card =
      (sharedBoundary H S (X.map (Function.Embedding.subtype _))).card :=
  Internal.BoundarySuppression.internalEdges_card H Q X

/-- A positive set in the suppressed graph gives a helpful move in the
original side with at most four times as many vertices.
@isnad1 id=ex.4h5v.s8.4aa1c2803ba4 from=translated src=- shape=233b34d6 vocab=3024efdd
-/
theorem exists_helpful_set_of_positive (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    {X : Finset {v : W // v ∈ S \ cutBoundary H S}}
    (positive : RedBlack.Positive (H.induce {v | v ∈ S \ cutBoundary H S}) Q.red X) :
    ∃ Y ⊆ S, Y.card ≤ 4 * X.card ∧ 1 ≤ helpfulness H S Y :=
  Internal.BoundarySuppression.exists_helpful_set_of_positive H Q regular outside independent positive

end BoundarySuppression

end Algebraic.Cutwidth.Bisection
