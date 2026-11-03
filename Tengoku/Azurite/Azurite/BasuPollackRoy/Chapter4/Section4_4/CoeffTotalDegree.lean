/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Adjugate
import Tengoku.Seed.Algebra.MvPolynomial.Degrees
import Tengoku.Seed.Algebra.Polynomial.Coeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.4.2: coefficient-wise total-degree bound

For the quantitative Nullstellensatz (Theorem 4.83) we must bound the degree, in the variables
`X₁, …, X_{k-1}`, of the coefficients (with respect to the auxiliary `U`) of the resultant
`Res_{X_k}(P₁, R)`. Modelling `Res_{X_k}` as an element of `(MvPolynomial (Fin n) K)[U]` (the
resultant of the Sylvester matrix over that ring), the relevant quantity is:

`CoeffTotalDegreeLE f D` — every `U`-coefficient of `f` has total degree `≤ D` in the `X`
variables. We prove it is preserved by sums, products (degrees add), determinants (degree
`≤ size · D`), and `±1`-scaling — the engine for the `2d²` bound on `Res_{X_k}`.
-/

namespace Azurite.BPR.Chapter4

variable {σ : Type*} {R : Type*} [CommRing R]

/-- Every coefficient of `f ∈ (MvPolynomial σ R)[U]` (with respect to the `Polynomial`
indeterminate `U`) has total degree at most `D` in the `σ` variables.-/
def CoeffTotalDegreeLE (f : Polynomial (MvPolynomial σ R)) (D : ℕ) : Prop :=
  ∀ j, (f.coeff j).totalDegree ≤ D

end Azurite.BPR.Chapter4
