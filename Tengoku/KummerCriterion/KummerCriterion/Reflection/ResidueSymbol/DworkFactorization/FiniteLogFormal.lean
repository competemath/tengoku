module

public import Tengoku.Seed.RingTheory.PowerSeries.Log

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Formal logarithm identities for the finite logarithm

This file isolates the formal-power-series identity behind finite-log
additivity. The identity is proved with a dummy variable `T`; substituting
`T * x` and `T * y` makes coefficients of `T^d` record total degree `d` in the
two principal-unit coordinates.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

namespace Furtwaengler

namespace FiniteLogFormal

open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

end FiniteLogFormal

end Furtwaengler

end KummerCriterion

end
