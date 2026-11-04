/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_77

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Theorem 4.72: Weak Hilbert's Nullstellensatz

For a finite `𝒫 = {P₁, …, P_s} ⊂ K[X₁, …, X_k]` (with `K` of characteristic zero and `C`
algebraically closed), `Zer(𝒫, C^k) = ∅` if and only if `1 ∈ Ideal(𝒫, K)`, i.e. there are
`A₁, …, A_s` with `A₁ P₁ + ⋯ + A_s P_s = 1`.

The forward direction is Proposition 4.77: if `Zer(𝒫) = ∅` then the geometric alternative is
impossible (a finite mapping onto `C^{k'}` is surjective, so its source `Zer(𝒫)` would be
non-empty), leaving `1 ∈ Ideal(𝒫)`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

end Azurite.BPR.Chapter4
