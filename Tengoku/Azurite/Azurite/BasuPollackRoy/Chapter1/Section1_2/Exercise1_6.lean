/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.Algebra.Polynomial.RingDivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exercise 1.6

Over a field $K$, $x \in K$ is a root of $P \in K[X]$ if and only if
$(X - x)$ divides $P$.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- Exercise 1.6: x is a root of P iff (X − x) divides P in K[X].
@isnad1 id=iff.0h3v.s8.3bfd8e073093 from=translated src=- shape=1eba6466 vocab=7f66dea9
-/
theorem exercise_1_6 (P : K[X]) (x : K) :
    Polynomial.eval x P = 0 ↔ (X - Polynomial.C x) ∣ P :=
  dvd_iff_isRoot.symm

end Azurite.BPR
