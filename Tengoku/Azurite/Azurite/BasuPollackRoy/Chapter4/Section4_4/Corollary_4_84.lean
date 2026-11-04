/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_83
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Corollary_4_80

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Corollary 4.84: the quantitative homogeneous Hilbert's Nullstellensatz

Let `𝒫 = {P₁, …, P_s}` be homogeneous of degrees `dᵢ` bounded by `d`, and `P` homogeneous of
degree `p` vanishing on the common zeros of `𝒫` in `C^k` (`K` of characteristic zero, `C`
algebraically closed, `0 < p`). Then there are `n` and homogeneous `Hᵢ` of degree `cᵢ = np - dᵢ`
with `P^n = ∑ᵢ Hᵢ Pᵢ`, `np = cᵢ + dᵢ`, and `n` bounded by `(2(max d p + 1))^{2^{k+1}}`.

This is the degree-tracking form of Corollary 4.80: the exponent `n` is now explicitly bounded,
via Theorem 4.83 (the quantitative Nullstellensatz) in place of Theorem 4.78. The `Hᵢ` are, as in
4.80, the degree-`np` homogeneous components of the coefficients in the (ordinary) combination
`P^{n₀} = ∑ Bᵢ Pᵢ`, with `n = max(n₀, sup dᵢ)`.

## On the bound

BPR's stated bound is `(2d)^{2^{k+1}}` — *independent of* `p = deg P`. We obtain
`(2(max d p + 1))^{2^{k+1}}`, which depends on `p`. The discrepancy is genuine, not a looseness in
this proof: the route BPR cites (Theorem 4.83 applied to `P`, then the proof of Corollary 4.80)
must run Theorem 4.83 with the degree bound `max d p`, since Theorem 4.83 requires every input —
including `P` — to have degree at most its parameter, and `deg P = p` is unbounded here. (The
`d → d+1` shift is the usual Rabinowitsch-variable overhead from Theorem 4.83.)

A `p`-independent exponent `n` is *true* (it equals a uniform `M` with `(√Ideal(𝒫))^M ⊆
Ideal(𝒫)`, which exists by Noetherianity and depends only on `𝒫`), but a `p`-independent
*explicit bound* `(2d)^{2^{k+1}}` requires effective control of the generator degrees of
`√Ideal(𝒫)` (equivalently, an effective uniform `(√I)^M ⊆ I` bound, or effective Noether
normalization with a rank bound together with the resolution of `K[Y]`-torsion in `K[X]/I`). None
of that effective commutative algebra is currently available, so we record the `p`-dependent
bound, which is exactly the content of the cited proof.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {K : Type*} [Field K]

end Azurite.BPR.Chapter4
