/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.WeightedTree
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal.Weighted

/-!
# Small positive witnesses from the core graph

Adjacent core pieces absorb the whole boundary of their connecting region.
Restoring all incident regions and their chosen attachments therefore gives
a positive witness in the original graph. This includes boundaries deleted
before forming the core graph and charges restoration only once.

Natural weights that dominate the piece sizes can be used to find a small
pair by the weighted-tree lemma. The weight and leaf hypotheses remain
explicit; these theorems do not assert that reorganization has supplied them.
For the constructed thin family, `L = 3 M` and black degree at most three
give a witness of size at most `2 M (1 + 9 M)` from a pair of total size
at most `2 M`.

Source: Burkhard Monien and Robert Preis, *Upper bounds on the bisection
width of 3- and 4-regular graphs*, Journal of Discrete Algorithms 4 (2006),
475–498, https://doi.org/10.1016/j.jda.2005.12.009.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype E] [Fintype ι]
  {B : SimpleGraph V} {R : Multigraph V E} (F : RestorationFamily B R ι)

section Core

variable (H : SimpleGraph V) (kept : F.deletedGraph ≤ H) (original : H ≤ B) (L d : ℕ)
  (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L) (degree : ∀ v, B.degree v ≤ d)
  (f : ι ↪ (H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent)
  (support : ∀ i, (f i).supp.toFinset = F.region i)

include kept original small degree support

variable [Fintype {C // C ∉ Finset.univ.image f}]

end Core

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily
