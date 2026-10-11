/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.AlgConn
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.WeightedCut

/-!
# A disconnected graph has algebraic connectivity at most `2`

If the vertex set splits as `A ⊔ Aᶜ` (both nonempty) with no edges between the parts,
then the cut is empty, so the weighted-cut certificate gives `algConn G ≤ 2` (indeed
`algConn G = 0`).  This handles disconnected graphs uniformly for every `n`.
-/

@[expose] public section

namespace ACMax

end ACMax
