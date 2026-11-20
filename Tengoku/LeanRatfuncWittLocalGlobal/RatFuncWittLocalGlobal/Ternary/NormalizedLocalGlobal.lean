/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Ternary.Reduction.PolynomialCriteria
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Ternary.Quaternion.Polynomial.Endpoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalized ternary local-global theorem

This module closes the normalized polynomial Legendre argument from a
normalized ordering realization, then exposes the corresponding ternary
local-global statement.  It is the sole bridge needed by the public
ordered-real-closure endpoint.
-/

namespace RatFuncWittLocalGlobal

universe u

variable {R : Type u}

/-- The normalized polynomial Legendre argument from an ordering
realization.
@isnad1 id=normaliz.1h1v.s5.31f1673d8755 from=translated src=- shape=fb04960b vocab=f8b91905
-/
theorem normalizedTernaryLocalGlobal_of_normalizedOrderingRealization
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, u} R) :
    RatFunc.NormalizedTernaryLocalGlobal.{u, u} R :=
  RatFunc.normalizedTernaryLocalGlobal_of_polynomialLegendre_of_rootOrderedPos
    R hrealization
    (polynomialLegendreConstruction_of_normalizedOrderingRealization hrealization)
    (RatFunc.squarefreeGcdLegendreLinearRootOrderedPosPrinciples_laurentSeries R)
    (RatFunc.nonlinearIrreducibleDivisorSquareMod_of_realClosed (R := R))

/-- The ternary local-global statement obtained from the normalized one.
@isnad1 id=ternaryl.1h1v.s5.02edcd87b461 from=translated src=- shape=fb04960b vocab=6e1fad4f
-/
theorem ternaryLocalGlobal_of_normalizedOrderingRealization
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (hrealization : RatFunc.NormalizedOrderingRealization.{u, u} R) :
    RatFunc.TernaryLocalGlobal.{u, u} R :=
  RatFunc.ternaryLocalGlobal_of_normalized
    (normalizedTernaryLocalGlobal_of_normalizedOrderingRealization hrealization)

end RatFuncWittLocalGlobal
