/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_3.PolynomialDeterminant
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_3.PolynomialDeterminants

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Proposition 8.27: the `m = n` and `m = 1` special cases

* When `m = n`, `pdet_{n,n}(𝒫) = det(Mat(𝒫))` (the polynomial determinant is the
  ordinary determinant, as a constant in `𝓕_1`).
* When `m = 1`, `pdet_{1,n}(P) = P` (the polynomial determinant is the identity).

Both are stated at the `K[X]` level to avoid the `n - m + 1` type arithmetic.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

end Azurite.BPR.Chapter8
