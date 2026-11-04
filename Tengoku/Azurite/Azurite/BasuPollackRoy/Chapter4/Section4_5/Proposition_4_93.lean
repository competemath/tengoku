/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.LocalizationAtPoint
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Tengoku.Seed.RingTheory.Idempotents
import Tengoku.Seed.RingTheory.Localization.Basic
import Tengoku.Seed.RingTheory.Nilpotent.Basic
import Tengoku.Seed.Algebra.CharP.Algebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.5, Proposition 4.93: the corner ring `eₓ Ā` is the localization `Ā_x`

Let `K` be a field of characteristic zero, `C` an algebraically closed extension of `K`, and `𝒫`
a finite subset of `K[X₁, …, X_k]`. For `x ∈ Zer(𝒫, Cᵏ)`, let `eₓ ∈ Ā` be an idempotent with
`eₓ(x) = 1` and `eₓ(y) = 0` for every other zero `y` (such an `eₓ` exists by Proposition 4.92).
Then the corner ring `eₓ Ā` is isomorphic to the localization `Ā_x` of `Ā` at `x`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K]

end Azurite.BPR.Chapter4
