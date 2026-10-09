/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal.Structure
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Internal
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal

/-!
# Positive witnesses from adjacent core pieces

A core edge passes through a region whose two boundary edges join distinct
core components. Their union therefore absorbs the whole region boundary.
It is closed after all region cuts are deleted, even if only some cuts were
deleted before forming the core graph. Simultaneous restoration gives a
positive witness in the original graph, with one size charge per restored
region and attachment.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}
  (F : RestorationFamily B R ι) (H : SimpleGraph V)

variable [Fintype E]

theorem exists_positive_of_restricted_core_adj (indices : Finset ι) (L d : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    (degree : ∀ v, B.degree v ≤ d)
    (f : ι ↪ ((F.restrict indices).deletedGraph.deleteEdges
      (⋃ i, ((F.restrict indices).deletedGraph.cutFinset
        (F.region i) : Set (Sym2 V)))).ConnectedComponent)
    (support : ∀ i, (f i).supp.toFinset = F.region i)
    (u v : {C // C ∉ Finset.univ.image f})
    (adjacent : (PathSuppression.coreGraph (F.restrict indices).deletedGraph F.region f).Adj u v) :
    ∃ Y, u.val.supp.toFinset ∪ v.val.supp.toFinset ⊆ Y ∧
      Y.card ≤ (1 + d * L) * (Fintype.card u.val + Fintype.card v.val) ∧ Positive B R Y :=
  exists_positive_of_core_adj F (F.restrict indices).deletedGraph
    (deletedGraph_le_restrict F indices) (SimpleGraph.deleteEdges_le _)
    L d small degree f support u v adjacent

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal
