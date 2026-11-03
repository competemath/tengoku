/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Coprime
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Corollary1_6
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_7
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_10
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_13
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Divisor
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.EuclideanDivision
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_5
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_6
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Exercise1_7
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Lcm
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_14Corollaries
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.PolynomialBasics
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_5
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_8
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_9
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_12
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Remark1_4
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.RootCharacterizations
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.SRemSTermination
import Tengoku.Seed.Algebra.Polynomial.Derivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 2, Section 2.2: Sturm sequence

Let `P` be a non-zero polynomial with coefficients in a real closed field
`R`. The sequence of signed remainders of `P` and `P'`, `SRemS(P, P')`
(see Definition 1.7), is the **Sturm sequence** of `P`.

The underlying construction `SRemS` (BPR Definition 1.7) is total over any
field, so we define `sturmSequence` on any field as well. The "non-zero `P`
in a real closed field" hypothesis becomes a precondition for downstream
theorems rather than for the definition itself.
-/

namespace Azurite.BPR

open Polynomial

/-- **BPR Chapter 2.2.** The Sturm sequence of `P`, defined as the signed
    remainder sequence `SRemS(P, P')` of `P` and its derivative.-/
noncomputable def sturmSequence {K : Type*} [Field K] (P : Polynomial K) :
    ℕ → Polynomial K :=
  SRemS P P.derivative

@[simp] theorem sturmSequence_zero {K : Type*} [Field K] (P : Polynomial K) :
    sturmSequence P 0 = P := rfl

@[simp] theorem sturmSequence_one {K : Type*} [Field K] (P : Polynomial K) :
    sturmSequence P 1 = P.derivative := rfl

end Azurite.BPR
