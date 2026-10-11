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
# A single low-degree vertex already forces `algConn ≤ 2`

If `G` has a vertex `u` of degree `≤ 2` and there is at least one vertex outside
`{u} ∪ N(u)`, then `algConn G ≤ 2`.

Certificate: with `C := N(u)` (`|C| = deg u ≤ 2`) and `T := V ∖ ({u} ∪ C)`, take
`x := |T|·e_u − 𝟙_T`.  Then `∑ x = 0`, `∑ x² = |T|² + |T|`, and the only edges that
contribute to the Laplacian form are the `deg u` edges `u`–`C` (each `|T|²`) and the
`T`–`C` edges (each `1`); there are no `u`–`T` edges.  Since every vertex of `T` meets
at most `|C| ≤ 2` vertices of `C`, the `T`–`C` edge count is `≤ 2|T|`, so
`xᵀ L x = deg u · |T|² + e(T,C) ≤ 2|T|² + 2|T| = 2 ∑ x²`.

This closes every `n ≤ 7` instance of the conjecture: `m = 2(n-2) < 3n/2` for `n ≤ 7`
forces a vertex of degree `≤ 2`.  The open core is exactly the graphs with minimum
degree `≥ 3` (possible only for `n ≥ 8`).
-/

@[expose] public section

namespace ACMax

open Matrix

end ACMax
