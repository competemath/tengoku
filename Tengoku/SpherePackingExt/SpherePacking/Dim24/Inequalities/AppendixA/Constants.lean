module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.RBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Shared constants and basic functions used throughout the Appendix A truncation arguments.

We keep these definitions public (not `private`) so that other Appendix A files can reuse them
without carrying around hidden `_private` names in theorem statements.
-/

open scoped Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The error tolerance `10^(-50)` used in `appendix.txt`.-/
@[expose]
public def eps : ℝ := (10 : ℝ) ^ (-50 : ℤ)

/-- The `q`-parameter on the imaginary axis: `q(t) = exp(-2πt)`.-/
@[expose]
public def q (t : ℝ) : ℝ := Real.exp (-2 * Real.pi * t)

end

end SpherePacking.Dim24.AppendixA
