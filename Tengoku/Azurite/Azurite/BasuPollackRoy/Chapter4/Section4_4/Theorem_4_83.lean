/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.QuantWeakNullstellensatz
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_78

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Theorem 4.83: the quantitative Hilbert's Nullstellensatz

Let `𝒫 = {P₁, …, P_s} ⊂ K[X₁, …, X_k]` be a finite set of polynomials of degrees bounded by `d`
(with `K` of characteristic zero and `C` algebraically closed). If a polynomial `P` of degree
`≤ d` vanishes on the common zeros of `𝒫` in `C^k`, then there is `n` and polynomials `Bᵢ`, both `n`
and the degrees of the `Bᵢ` bounded by `(d+1)·(2(d+1))^{2^{k+1}}`, such that `Pⁿ = ∑ᵢ Bᵢ Pᵢ`.

The proof is the degree-tracking version of Theorem 4.78 (Rabinowitsch): the system
`𝒫 ∪ {X₀·P − 1}` in `k+1` variables, of degree `≤ d+1`, has no common zero, so the *quantitative*
weak Nullstellensatz (`quant_weak_nss`) yields `1 = A₀·(X₀ P − 1) + ∑ᵢ Aᵢ Pᵢ` with each `Aᵢ` of
total degree `≤ w := wBound (d+1) (k+1)`. Substituting `X₀ = 1/P` kills the first term; clearing
denominators by `P^w` turns each `Aᵢ(1/P, X)` into `ψ(Aᵢ) := ∑_{a≤w} (finSuccEquiv Aᵢ).coeff a · P^{w-a}`,
a genuine polynomial of degree `≤ w·(d+1)`, and gives `P^w = ∑ᵢ ψ(Aᵢ) Pᵢ`. The displayed bound
follows from `wBound_le : w ≤ (2(d+1))^{2^{k+1}}`.

BPR's stated bound `d·(2d)^{2^{k+1}}` is matched up to the `d → d+1` shift forced by the
Rabinowitsch variable `X₀`. BPR's hypothesis that there are *fewer than `d`* polynomials is not
needed: the bound depends only on the degree and the number of variables.

We single out `X₀` as the Rabinowitsch variable; the original variables `X₁, …, X_k` embed via
`rename Fin.succ`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

end Azurite.BPR.Chapter4
