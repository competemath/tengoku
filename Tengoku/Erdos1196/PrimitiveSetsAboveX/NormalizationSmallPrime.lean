module

public import Tengoku.Erdos1196.PrimitiveSetsAboveX.NormalizationCore
public import Tengoku

/-!
# Small-prime bounds for the normalization constant

This file isolates the contribution to `B_x` coming from divisors `q < Y`.
Its main theorem shows that this part is summable and contributes only `O(1 / log x)` for fixed
`Y`.

## Main statements

* `summable_normalizationSmallPrimePart_and_tsum_le`
-/

@[expose] public section

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

/-- The natural-number kernel in the small-prime tail. -/
noncomputable def smallPrimeTailTerm (q m : ℕ) : ℝ :=
  1 / ((m : ℝ) * (Real.log ((m * q : ℕ) : ℝ)) ^ 2)

/-- The corresponding real-variable kernel used for integral comparison. -/
noncomputable def smallPrimeKernel (q : ℕ) (t : ℝ) : ℝ :=
  1 / (t * (Real.log (t * q)) ^ 2)

end PrimitiveSetsAboveX
