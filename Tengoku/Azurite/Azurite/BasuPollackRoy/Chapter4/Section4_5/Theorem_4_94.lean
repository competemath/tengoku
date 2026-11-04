/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_93
import Tengoku.Seed.RingTheory.Idempotents

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.5, Theorem 4.94: the product decomposition `Ā ≅ ∏_x Ā_x`

For each `x ∈ Zer(𝒫, Cᵏ)` there is an idempotent `e_x` with `e_x Ā ≅ Ā_x` (Propositions 4.92 and
4.93), and
`Ā ≅ ∏_{x ∈ Zer(𝒫, Cᵏ)} Ā_x`.

Proof: the idempotents `(e_x)` form a complete orthogonal family (`∑ e_x = 1`, `e_x e_y = 0`,
`e_x² = e_x` — Proposition 4.92), so `Ā ≅ ∏_x e_x Ā` (Mathlib's
`CompleteOrthogonalIdempotents.ringEquivOfComm`). Composing factor-wise with the isomorphisms
`e_x Ā ≅ Ā_x` of Proposition 4.93 gives `Ā ≅ ∏_x Ā_x`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

end Azurite.BPR.Chapter4
