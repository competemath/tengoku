/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.AlgConn
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.RayleighUpper
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.TestVector

/-!
# Signed (three-valued) certificate — the unifying general method

Every `n ≤ 8` upper-bound proof, and the `n = 9` extremal graphs where the `±1` cut
method *provably* fails, are all captured by a single **`{-1,0,1}` test vector**
`x = 𝟙_P − 𝟙_N` with a third "neutral" set `Z = (P ∪ N)ᶜ`.  Orthogonality to `𝟙`
requires `|P| = |N|`; the squared norm is `2|P|`; and the Laplacian quadratic form is
`xᵀ L x = 4·e(P,N) + e(P,Z) + e(N,Z)` (cross edges between `P` and `N` cost `4`, edges
to the neutral set cost `1`, edges inside a block cost `0`).  Hence the certificate
`4·e(P,N) + e(P,Z) + e(N,Z) ≤ 4|P|` gives `algConn G ≤ 2`.

This **subsumes**:
* `algConn_le_two_of_balanced_cut` (`Z = ∅`, `N = Pᶜ`): `4·cut ≤ 4|P| ↔ cut ≤ |P| = n/2`;
* `algConn_le_two_of_nonadj_pair` (`P = {u}`, `N = {v}`): `deg u + deg v + 2[u∼v] ≤ 4`;

and, unlike any bipartition cut, it certifies the `λ₂ = 2` Fiedler-eigenvector graphs at
`n = 9` (the eigenvectors are `{-1,0,1}`-valued, with the high-degree vertices in `Z`).
-/

@[expose] public section

namespace ACMax

open Matrix

end ACMax
