module

public import Tengoku.Erdos1196.PrimitiveSetsAboveX.Basic
public import Tengoku.Erdos1196.PrimitiveSetsAboveX.PreliminariesMertens
public import Tengoku.Erdos1196.PrimitiveSetsAboveX.PreliminariesTailAux
public import Tengoku

/-!
# Tail estimates for primitive sets above `x`

This file proves the logarithmic tail estimate used later in the Markov-chain arguments.
It combines the arithmetic input from `PrimitiveSetsAboveX.PreliminariesMertens`,
Abel summation, and explicit calculus on the model kernel `1 / log (mt)^2`.
The arithmetic input for the Mertens partial sums lives in
`PrimitiveSetsAboveX.PreliminariesMertens`.

## Main statements

* `tailEstimate`
-/

@[expose] public section

open scoped ArithmeticFunction BigOperators Topology
open Filter MeasureTheory

namespace PrimitiveSetsAboveX

/-- The kernel `t ↦ 1 / log (m t)^2` that appears in the tail estimate. -/
private noncomputable def tailKernel (m : ℕ) (t : ℝ) : ℝ :=
  (Real.log ((m : ℝ) * t) ^ 2)⁻¹

/-- The truncated coefficients used to start Abel summation at `y`. -/
private noncomputable def tailCutoffCoeff (y q : ℕ) : ℝ :=
  if y ≤ q then Λ q / (q : ℝ) else 0

end PrimitiveSetsAboveX
