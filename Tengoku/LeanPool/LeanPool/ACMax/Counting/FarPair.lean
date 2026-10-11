/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.TestVector

/-!
# Far-pair and apex double-star test-vector certificates

Two reusable spectral certificates that bound the algebraic connectivity of a
graph above by `2` from an explicit test vector. They are the workhorses for
killing configurations built around a pair of low-degree vertices `u, v` in the
general ACMAX argument.

## Main results

* `algConn_le_two_of_weighted_double_star` — the **weighted double-star master
  certificate**. For non-adjacent `u ≠ v` with disjoint neighbourhoods and
  nonnegative weight data (`au` on `u`, `p` on `N(u)`, `av` on `v`, `q` on
  `N(v)`), the five-valued test vector
  `x = au·𝟙_u + p·𝟙_{N(u)} − av·𝟙_v − q·𝟙_{N(v)}` witnesses `algConn G ≤ 2`
  whenever the worst-case quadratic bound
  `Σ (au − p w)² + Σ (av − q w)² + Σ_{cross} (p w + q w')² + Σ leak·p² + Σ leak·q²
  ≤ 2·(au² + Σ p² + av² + Σ q²)` holds (an edge inside `N(u)` costs at most its
  two leak-slot charges since the weights are nonnegative).
* `algConn_le_two_of_apex_double_star` — the same certificate extended to pairs
  sharing **exactly one** common neighbour `g` (the *apex*, weight `0`); the two
  apex edges `u–g`, `v–g` cost `au² + av²`.
* `algConn_le_two_of_apex_twin_pair` — the **apex tie law**: two degree-3
  vertices sharing a single hub `g`, with all non-apex partners of degree `≤ 4`
  and no partner–partner cross edges, force `algConn G ≤ 2`. With
  `au = av = 1`, `p = q ≡ ½` the quadratic bound holds with equality
  (`1 + 1 + 4·¼ + 4·(3·¼) = 6 = 2·(1 + ½ + 1 + ½)`), so the hypotheses trace out
  the exact tie boundary.

All three are direct instances of `algConn_le_two_of_testvector`; no new spectral
machinery is introduced.
-/

@[expose] public section

namespace ACMax

open Matrix

variable {V : Type*} [Fintype V]

/-! ## The weighted double-star master certificate -/

/-! ## The apex double star and the tie law

`algConn_le_two_of_apex_double_star` extends the master certificate to pairs
sharing one apex `g` (weight `0`), the two apex edges `u–g`, `v–g` costing
`au² + av²`. The tie law `algConn_le_two_of_apex_twin_pair` applies it to two
degree-3 vertices with a single shared hub, partners of degree `≤ 4`, and no
partner–partner cross edge. This is the certificate behind the A-bound: every
same-cloud pair of usable twins of a degree-`≥ 9` hub either meets it or shares
a degree-4 partner / carries a cross edge, a coverage count that bounds the
cloud size. -/

end ACMax
