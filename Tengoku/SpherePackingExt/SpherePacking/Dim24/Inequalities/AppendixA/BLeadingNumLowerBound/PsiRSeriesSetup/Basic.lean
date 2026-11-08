module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
### `ψI` numerator as an `r`-series

Appendix A (and `appendix.txt`) treats the theta contribution using the parameter
`r(t) = exp(-π t)` and `r`-series with integer coefficients.
We set up the minimal Cauchy-product API for `rseries` used to expand the `ψI`-numerator.
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA

open scoped BigOperators

/-- Cauchy product on integer coefficient functions `ℕ → ℤ`, written as an antidiagonal sum.-/
@[expose] public def convZ (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/-- The coefficient function of the constant series `1`: `oneCoeffFun 0 = 1`, otherwise `0`.-/
@[expose] public def oneCoeffFun (n : ℕ) : ℤ := if n = 0 then 1 else 0

/--
Iterated Cauchy product powers: `powConvZ a k` is the coefficient function of
`(rseries a)^k`.-/
@[expose] public def powConvZ (a : ℕ → ℤ) : ℕ → (ℕ → ℤ)
  | 0 => oneCoeffFun
  | Nat.succ k => convZ a (powConvZ a k)

/-!
#### Summability/tail bounds for `rseries` with polynomially bounded coefficients

We reuse the same `powGeomTerm` majorants as for `q`-series, but with base `r(t) = exp(-π t)`.
-/

end SpherePacking.Dim24.AppendixA
