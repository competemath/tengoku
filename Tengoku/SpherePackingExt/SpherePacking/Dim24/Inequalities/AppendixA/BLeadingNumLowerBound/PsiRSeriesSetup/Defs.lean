module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.RBounds
public import Tengoku.Seed.Topology.Algebra.InfiniteSum.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
### Basic `r`-series definitions

We use the real parameter `r(t) = exp(-π t)` and its cast `rC t : ℂ`. The `rseries` of an integer
coefficient function `a : ℕ → ℤ` is the complex series `∑' n, (a n : ℂ) * (rC t)^n`.
-/

namespace SpherePacking.Dim24.AppendixA

noncomputable section

open scoped BigOperators

/-- The complex number `r(t)` viewed in `ℂ`.-/
@[expose] public def rC (t : ℝ) : ℂ := (r t : ℂ)

/-- The `r`-series with integer coefficients `a`, evaluated at the parameter `t`.-/
@[expose] public def rseries (a : ℕ → ℤ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, (a n : ℂ) * (rC t) ^ n

end

end SpherePacking.Dim24.AppendixA
