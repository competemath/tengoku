/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_3.Lemma_8_43
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_38

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR Corollary 8.44: the inverse of `B_{j,i}`

In the setting of Lemma 8.43 (`sResP_{i-1}(P,Q)` nonzero of degree `j`), the cofactor matrix
`B_{j,i}` has determinant `s_j t_{i-1} ≠ 0`, so `C(s_j t_{i-1})` is a unit in `K[X]` and
`B_{j,i}` is invertible with

  `B_{j,i}^{-1} = (1 / (s_j t_{i-1})) · [ sResV_{j-1}  -sResV_{i-1};
                                          -sResU_{j-1}   sResU_{i-1} ]`.

The matrix on the right is the adjugate of `B_{j,i}`; it has entries in `D[X]`, so
`s_j t_{i-1} · B_{j,i}^{-1} ∈ D[X]` (it equals that explicit polynomial matrix).
-/

namespace Azurite.BPR.Chapter8

open Polynomial Matrix

variable {K : Type*} [Field K]

/-- The adjugate of `B_{j,i}` is the explicit polynomial matrix
    `[ sResV_{j-1}, -sResV_{i-1}; -sResU_{j-1}, sResU_{i-1} ]` (the `2×2` adjugate of
    `[ sResU_{i-1}, sResV_{i-1}; sResU_{j-1}, sResV_{j-1} ]`).-/
theorem adjugate_cofactorMat (P Q : K[X]) (i j : ℕ) :
    Matrix.adjugate (cofactorMat P Q i j)
      = !![sResV P Q (j - 1), -sResV P Q (i - 1); -sResU P Q (j - 1), sResU P Q (i - 1)] := by
  rw [cofactorMat, Matrix.adjugate_fin_two_of]

end Azurite.BPR.Chapter8
