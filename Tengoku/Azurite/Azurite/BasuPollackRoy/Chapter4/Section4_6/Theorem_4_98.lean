/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_6.Theorem_4_97
import Tengoku.Seed.LinearAlgebra.Eigenspace.Charpoly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.6, Theorem 4.98 (Stickelberger)

For `f ∈ Ā`, the multiplication map `L_f` has trace, determinant and characteristic polynomial
\[
  \mathrm{Tr}(L_f) = \sum_x \mu(x) f(x), \qquad \det(L_f) = \prod_x f(x)^{\mu(x)}, \qquad
  \chi(\mathcal{P}, f, T) = \prod_x (T - f(x))^{\mu(x)},
\]
the sums and products being over the zeros `x ∈ Zer(𝒫, Cᵏ)`. All three follow from Theorem 4.97:
over the algebraically closed field `C` the characteristic polynomial splits, so its trace and
determinant are the sum and product of its roots, and the roots are read off from the factored
characteristic polynomial.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] [CharZero K]
  {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

end Azurite.BPR.Chapter4
