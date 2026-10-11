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
# The "good `C₄`" certificate

An induced 4-cycle `a–b–c–d–a` (with `a ≁ c`, `b ≁ d`) whose four vertices have small total degree
is a sparse weighted cut: each cycle vertex has exactly two neighbours inside `{a,b,c,d}`, so the
cut value is `∑ deg − 8`, and the weighted-cut inequality `n · (∑deg − 8) ≤ 2·4·(n−4)` certifies
`algConn G ≤ 2`.  This complements the "good triangle" certificate and, since `C₄` is `2K₂`-free,
applies in the no-`2K₂` regime where the induced-`2K₂` method fails.
-/

@[expose] public section

namespace ACMax

end ACMax
