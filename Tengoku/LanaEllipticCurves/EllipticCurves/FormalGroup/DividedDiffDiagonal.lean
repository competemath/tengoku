/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.AdicEval
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.DividedDifference
import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.Algebra.BigOperators.Finsupp.Fin
import Tengoku.Seed.Algebra.Order.Antidiag.Prod
import Tengoku.Seed.Data.Finset.NatAntidiagonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The divided difference on the diagonal is the formal derivative

For `f ∈ R⟦X⟧`, the first divided difference `Δf = (f(z₁) − f(z₀)) / (z₁ − z₀)`
(`PowerSeries.dividedDiff`, a genuine bivariate power series) specialises on the diagonal
`z₀ = z₁ = x` to the formal derivative `f′(x)`:

`Δf(x, x) = ∑' d, (coeff (d 0 + d 1 + 1) f) · x^(d 0 + d 1) = ∑' n, (n + 1) · coeff (n + 1) f · x^n
          = f′(x)`,

grouping the bidegree sum `d 0 + d 1 = n` (which has `n + 1` solutions) — the algebraic content of
"the tangent slope is the derivative", the missing ingredient for the doubling / duplication case of
the Weierstrass formal group addition law (Silverman AEC IV.1).

## Main result

* `PowerSeries.adicEvalMv_dividedDiff_diagonal` :
  `adicEvalMv I ![x, x] (dividedDiff f) = adicEval I hx (derivativeFun f)`.
-/

open MvPowerSeries

namespace PowerSeries

variable {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A]

omit [IsAdicComplete I A] in
/-- The two-element diagonal family `![x, x]` lies in `I` when `x ∈ I`. -/
theorem diag_mem {x : A} (hx : x ∈ I) : ∀ s : Fin 2, (![x, x] : Fin 2 → A) s ∈ I := by
  intro s; fin_cases s <;> simpa using hx

end PowerSeries
