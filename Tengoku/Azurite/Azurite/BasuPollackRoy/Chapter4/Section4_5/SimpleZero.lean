/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Multiplicity
import Tengoku.Seed.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.5: simple zeros

If the multiplicity of `x` is `1` we say that `x` is *simple* (`IsSimpleZero`). Then
`Ā_x = C` (`isSimpleZero_algEquiv`: `Ā_x ≅ C` as `C`-algebras), and the canonical surjection of
`Ā` onto `Ā_x` coincides with the homomorphism `Ā → C` sending `P` to its value at `x` (since the
multiplicity-one localization is `1`-dimensional over `C`, the evaluation map is an isomorphism).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]
  (Ps : Finset (MvPolynomial (Fin k) K)) (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps)

/-- **BPR Definition (simple zero).** A zero `x ∈ Zer(𝒫, Cᵏ)` is *simple* if its multiplicity
`μ(x)` is `1`.-/
def IsSimpleZero : Prop := multiplicityOfZero C Ps x hx = 1

end Azurite.BPR.Chapter4
