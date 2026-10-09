module

public import Tengoku.Erdos1196.PrimitiveSetsAboveX.Basic
public import Tengoku

/-!
# Auxiliary tail lemmas for primitive sets above `x`

This file contains the standalone calculus lemmas reused in the proof of `tailEstimate`.
Its main output is a small API for the model kernels `1 / (t log(ct)^2)` and
`2 / (t log(ct)^3)`: each kernel is integrable on an admissible tail, and its tail integral can
be computed exactly.

## Main statements

* `integrableOn_Ioi_inv_log_sq`
* `integral_Ioi_inv_log_sq`
* `integrableOn_Ioi_two_inv_log_cube`
* `integral_Ioi_two_inv_log_cube`
-/

@[expose] public section

open scoped ArithmeticFunction BigOperators Topology
open Filter MeasureTheory

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX
