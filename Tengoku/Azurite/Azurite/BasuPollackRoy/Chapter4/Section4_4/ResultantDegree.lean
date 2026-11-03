/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_76
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.CoeffTotalDegree
import Tengoku.Seed.Algebra.MvPolynomial.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.4.2: degree bound on the resultant projection

For the quantitative Nullstellensatz (Theorem 4.83): if `P₁` and all members of `rest` have total
degree `≤ d`, then every coefficient (in the auxiliary `U`) of `Res_{X_k}(P₁, R)` has total degree
`≤ 2 d²` in the variables `X₁, …, X_{k-1}`. Equivalently, each generator of `Proj_{X_k}(𝒫)` has
degree `≤ 2 d²`.

This follows from the Sylvester-determinant description of `Res` (`CoeffTotalDegreeLE.det`): the
matrix has size `≤ 2d`, and each entry is an `X₀`-coefficient of `embedX0 P₁` / `Rbar`, which is a
constant `Polynomial.C q` (resp. a `U`-monomial) with `q` of total degree `≤ d`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {n : ℕ} {K : Type*} [Field K]

end Azurite.BPR.Chapter4
