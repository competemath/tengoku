import Tengoku.PadicLFunctions.PadicLFunctions.KubotaLeopoldt.ZetaValues
import Tengoku.Seed.NumberTheory.LSeries.HurwitzZetaValues

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complex bridge for `zetaNeg`

Identifies the rational value `zetaNeg k` with the complex Riemann zeta function at
`−k` (mathlib's `riemannZeta_neg_nat_eq_bernoulli`). Quarantined in its own file so
that the p-adic development does not import complex analysis.
-/

namespace Tengoku.PadicLFunctions end Tengoku.PadicLFunctions open Tengoku.PadicLFunctions open Complex

/-- `zetaNeg k` really is `ζ(−k)`: the bridge to the complex Riemann zeta function.

Source: RJW TeX line 1455 (`ζ(−k) = (−1)^k B_{k+1}/(k+1)`); mathlib's
`riemannZeta_neg_nat_eq_bernoulli`.
@isnad1 id=eq.0h1v.s4.3df622ae92e8 from=translated src=- shape=cb780ddc vocab=b8232867
-/
theorem Tengoku.PadicLFunctions.zetaNeg_eq_riemannZeta (k : ℕ) :
    ((zetaNeg k : ℚ) : ℂ) = riemannZeta (-(k : ℂ)) := by
  rw [riemannZeta_neg_nat_eq_bernoulli, zetaNeg]
  push_cast
  ring
-- Tengoku: root names of this library moved to Tengoku.PadicLFunctions so they do not collide with other libraries (generated)
