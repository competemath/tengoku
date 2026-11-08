module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.RBounds
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
public import Tengoku.Seed.Data.Complex.Basic
public import Tengoku.Seed.Data.Finset.NatAntidiagonal
public import Tengoku.Seed.Topology.Algebra.InfiniteSum.Basic
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Constructions
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `r`-series infrastructure for the `ψS_num` truncation

We view (the relevant specializations of) theta expressions on the imaginary axis as absolutely
convergent power series in `r(t) = exp(-πt)`.

## Main definitions
* `rseries`
* `convZ`

## Main statements
* `rseries_mul_cast`
-/

noncomputable section

namespace SpherePacking.Dim24

namespace Ineq2PsiSnum

open scoped BigOperators

/-- The `r`-series `∑ a_n * r(t)^n` evaluated in `ℂ`.-/
@[expose] public def rseries (a : ℕ → ℤ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, (a n : ℂ) * ((AppendixA.r t : ℂ) ^ n)

/-- Convolution of integer coefficient functions (Cauchy product coefficients).-/
@[expose] public def convZ (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

end SpherePacking.Dim24.Ineq2PsiSnum
