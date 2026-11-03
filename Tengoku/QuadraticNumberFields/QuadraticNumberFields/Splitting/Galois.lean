/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.QuadraticNumberFields.QNFMathlib.NumberTheory.NumberField.Galois
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.QuadraticField.RingOfIntegers
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Splitting.Factorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Galois Actions and Splitting

This file records Galois-action facts for the fraction-field extension attached
to the ring of integers of a quadratic number field, especially the orbit and
stabilizer behavior of primes above split rational primes.
-/

local notation "ℚ√" d => Qsqrtd d

namespace QuadraticNumberFields

open scoped NumberField Pointwise
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

section FractionRingGalois

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K]

local notation "OK" => NumberField.RingOfIntegers K

/-- The Galois action on algebraic integers induced from the fraction-field
extension.-/
noncomputable local instance instMulSemiringActionFractionRingGalRingOfIntegersSplittingGalois
    [NumberField K] :
    MulSemiringAction Gal(FractionRing OK / FractionRing ℤ) OK :=
  IsIntegralClosure.MulSemiringAction ℤ (FractionRing ℤ) (FractionRing OK) OK

/-! ## Fraction-ring Galois group -/

/-! ## Split prime orbits -/

end FractionRingGalois

end QuadraticNumberFields
