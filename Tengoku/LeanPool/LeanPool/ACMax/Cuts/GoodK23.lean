/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.AlgConn
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.WeightedCut

/-!
# The "good `K_{2,3}`" certificate

An induced `K_{2,3}` (parts `{a,b}` and `{c,d,e}`, complete between, no edges inside parts) is a
weighted cut on 5 vertices with 6 internal edges: each of `a,b` has 3 neighbours inside, each of
`c,d,e` has 2, so the cut value is `∑deg − 12`.  The weighted-cut inequality
`n · (∑deg − 12) ≤ 2·5·(n−5)` certifies `algConn G ≤ 2`.

This is the dedicated cut for the `n = 12` sparse-hub residual that good `C₄` misses: a `K_{2,3}`
with two degree-4 vertices on the small side has `C₄`s of degree-sum `14 > 13` (not a good `C₄`),
yet the denser 5-vertex set still yields `cut = 5`.
-/

@[expose] public section

namespace ACMax

end ACMax
