/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Internal

/-!
# A finite parameter choice with source capacity, rate, and error bounds

For `T = e + clog 2 (9*(n+1)*(k+1)) + 1`, retain the sparse choices
`b = sparseFieldBits u T` and `r = sparsePowerBits u T`. Round the extension
degree `d` to a power of three above both three and `ceil(n/b)`. Then `b*d`
covers the source, `d` is linear in `n`, and the integer error budget pays for
loss `2^(-e)`. The coordinate count is `condenserCoordinates k r`.

These explicit rounding choices are our deduction from the finite sparse
rate and loss bounds in `Parameters.Sparse`, whose source credit is given
there. This layer contains exact natural-number inequalities. Its sibling
`Explicit.Unary` supplies uniform certificates for constructing the numerical
parameters; no asymptotic or extractor statement is asserted here.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The error and degree budget is positive even when all inputs are zero.
@isnad1 id=lt.0h3v.s4.2140af23428c from=translated src=- shape=ac9c39a3 vocab=8de89fd5
-/
theorem explicitCondenserBudget_pos (n k e : Nat) : 0 < explicitCondenserBudget n k e :=
  Internal.explicitCondenserBudget_pos n k e

/-- Every selected base field has a positive bit width.
@isnad1 id=lt.0h4v.s4.be62e36b44d2 from=translated src=- shape=235fb233 vocab=bf27d668
-/
theorem explicitCondenserFieldBits_pos (n k e u : Nat) :
    0 < sparseFieldBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenserFieldBits_pos n k e u

/-- A positive rate parameter leaves positive capacity in every coordinate.
@isnad1 id=lt.1h4v.s5.d19770a9ddb1 from=translated src=- shape=35d458f2 vocab=34ab6fca
-/
theorem explicitCondenserPowerBits_pos (n k e : Nat) {u : Nat} (rate : 0 < u) :
    0 < sparsePowerBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenserPowerBits_pos n k e rate

/-- The selected extension exponent is always positive.
@isnad1 id=lt.0h4v.s4.4ae64a891fd1 from=translated src=- shape=a76df7ca vocab=21e2064b
-/
theorem explicitCondenserExtensionExponent_pos (n k e u : Nat) :
    0 < explicitCondenserExtensionExponent n k e u :=
  Internal.explicitCondenserExtensionExponent_pos n k e u

/-- The extension degree is at least three, as required for the expansion regime.
@isnad1 id=le.0h4v.s4.a8da244ab4c4 from=translated src=- shape=a76df7ca vocab=86426711
-/
theorem explicitCondenser_degree_lower (n k e u : Nat) :
    3 ≤ explicitCondenserExtensionDegree n k e u :=
  Internal.explicitCondenser_degree_lower n k e u

/-- The coefficient rectangle holds the entire `n`-bit source.
@isnad1 id=le.0h4v.s4.e3410fcf28e5 from=translated src=- shape=1c8249d9 vocab=c4122cba
-/
theorem explicitCondenser_source_capacity (n k e u : Nat) :
    n ≤ sparseFieldBits u (explicitCondenserBudget n k e) *
      explicitCondenserExtensionDegree n k e u :=
  Internal.explicitCondenser_source_capacity n k e u

/-- Rounding the extension degree costs at most a linear factor in source length.
@isnad1 id=le.0h4v.s5.89e9c8775377 from=translated src=- shape=8429db96 vocab=8bb32eca
-/
theorem explicitCondenser_degree_le (n k e u : Nat) :
    explicitCondenserExtensionDegree n k e u ≤ 9 * (n + 1) :=
  Internal.explicitCondenser_degree_le n k e u

/-- The selected number of coordinates carries at least `k` entropy bits.
@isnad1 id=le.1h4v.s5.75dda2d421df from=translated src=- shape=ba63daaa vocab=236b982b
-/
theorem explicitCondenser_entropy_capacity (n k e : Nat) {u : Nat} (rate : 0 < u) :
    k ≤ sparsePowerBits u (explicitCondenserBudget n k e) *
      condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) :=
  Internal.explicitCondenser_entropy_capacity n k e rate

/-- The seed bit length is bounded by six times the rate-adjusted slack budget.
@isnad1 id=le.0h4v.s5.e9b372231e1e from=translated src=- shape=fceebe46 vocab=30d4286a
-/
theorem explicitCondenser_fieldBits_le (n k e u : Nat) :
    sparseFieldBits u (explicitCondenserBudget n k e) ≤
      6 * (u + 1) * explicitCondenserBudget n k e :=
  Internal.explicitCondenser_fieldBits_le n k e u

/-- The coordinate output approaches rate `1+1/u`, with one field element of slack.
@isnad1 id=le.0h4v.s6.ba212d46bf33 from=translated src=- shape=84af3b4c vocab=a3ab1902
-/
theorem explicitCondenser_output_rate (n k e u : Nat) :
    u * (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
      sparseFieldBits u (explicitCondenserBudget n k e)) ≤
        (u + 1) * k + u * sparseFieldBits u (explicitCondenserBudget n k e) :=
  Internal.explicitCondenser_output_rate n k e u

/-- The exact integer budget needed for inverse-power-of-two error.
@isnad1 id=le.0h4v.s6.26ee6607b6c9 from=translated src=- shape=ff6969d0 vocab=a0670aa3
-/
theorem explicitCondenser_error_budget (n k e u : Nat) :
    explicitCondenserExtensionDegree n k e u * k * 2 ^ e ≤
      2 ^ explicitCondenserBudget n k e :=
  Internal.explicitCondenser_error_budget n k e u

end Algebraic.Cutwidth.Extractor
