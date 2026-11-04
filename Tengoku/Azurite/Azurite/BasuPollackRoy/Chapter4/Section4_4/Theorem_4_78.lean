/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_72
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Theorem 4.78: Hilbert's Nullstellensatz

Let `𝒫 ⊂ K[X₁, …, X_k]` be finite (with `K` of characteristic zero and `C` algebraically closed).
If a polynomial `P` vanishes on `Zer(𝒫, C^k)`, then `P^n ∈ Ideal(𝒫, K)` for some `n`.

Proof (Rabinowitsch): `𝒫 ∪ {T·P - 1}` (in `X₁, …, X_k, T`) has no common zero in `C^{k+1}`, so by
the weak Nullstellensatz (Theorem 4.72) `1 = ∑ Aᵢ Pᵢ + A·(T·P - 1)` in `K[X₁, …, X_k, T]`.
Substituting `T = 1/P` (over the fraction field of `K[X₁, …, X_k]`) kills the last term, and
clearing denominators by a power of `P` shows a power of `P` lies in `Ideal(𝒫, K)`.

We single out `T = X₀` (the original variables `X₁, …, X_k` embed via `rename Fin.succ`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

end Azurite.BPR.Chapter4
