/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Order.Internal

/-!
# Jumping the median band of edge scores

Fix `c > 0` and a real score on the edges of a cubic graph. An edge is low when its score is
below `-c`, in the band when its score lies in `[-c, c)`, and high when its score is at least
`c`. Label the band edges by blocks so that band edges sharing a vertex share a label, for
example by the connected components of the band.

The band-jump order lists the low edges by score, then the band blocks one whole block at a
time, then the high edges by score. The blocks are taken in increasing order of the
imbalance `B_j - A_j`, where `A_j` (resp. `B_j`) counts the vertices touching block `j` with a
low (resp. high) edge. Between blocks, a bag holds the vertices with no band edge but both a
low and a high edge, the high endpoints of the finished blocks, and the low endpoints of the
blocks still to come. The vertices straddling `-c` are those of the first kind together with
all `A_j` vertices, and those straddling `c` are those of the first kind together with all
`B_j` vertices. Taking the blocks by increasing imbalance keeps every prefix sum of the
imbalances at most `max 0 (∑ (B_j - A_j))`, so every bag of the band phase has at most the
larger of the two straddling counts plus the vertices of the block in progress.

* `exists_pathDecomposition_of_bandJump`: if every threshold `t < -c` or `t ≥ c` has at most
  `B` vertices with an edge scoring at most `t` and one scoring at least `t`, and for every
  block `j` both straddling counts of `±c` plus the endpoints of block `j` are at most `B`,
  then every bag has at most `B` vertices.
* `card_filter_edgeScore_le_window`: a threshold `t ∈ [u, u')` has at most the straddling
  vertices of `u` plus twice the edges scoring in `[u, u')`.
* `card_filter_edgeScore_le_of_grid`: grid thresholds `a + i δ` with few straddling vertices
  and few edges in each window bound every `t ∈ [a, a + M δ)`.
* `card_filter_edgeScore_le_of_grids`: a low grid reaching `-c`, a high grid starting at or
  below `c`, and the two tails bound every threshold outside the band, as required by
  `exists_pathDecomposition_of_bandJump`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

end Algebraic.Cutwidth.Gaussian
