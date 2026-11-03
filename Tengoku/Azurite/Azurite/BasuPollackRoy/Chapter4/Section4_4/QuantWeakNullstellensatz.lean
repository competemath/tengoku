/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.ResultantDegree
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_77
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.QuantitativeBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.4.2: the quantitative weak Nullstellensatz

If a finite system `𝒫 ⊆ K[X₁, …, X_m]` of polynomials of degree `≤ d` has no common zero in `C^m`
(with `K` of characteristic zero and `C` algebraically closed), then `1 = ∑ Aᵢ Pᵢ` with all `Aᵢ`
of total degree `≤ wBound d m ≤ (2d)^{2^m}`.

The proof is the degree-tracking version of Proposition 4.77's empty-zero-set case, by induction on
`m`: a linear shear (`exists_linear_shear`, degree-preserving) makes one polynomial quasi-monic;
the resultant projection (Proposition 4.76) yields `Proj` in `m-1` variables of degree `≤ 2d²` with
empty zero set; the induction hypothesis gives a combination of degree `≤ wBound (2d²) (m-1)`; and
the per-step lift (`quant_proj_mem`) re-expresses it over `𝒫` adding `≤ 3d²` to the degree, so
`wBound (2d²) (m-1) + 3d² = wBound d m`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

end Azurite.BPR.Chapter4
