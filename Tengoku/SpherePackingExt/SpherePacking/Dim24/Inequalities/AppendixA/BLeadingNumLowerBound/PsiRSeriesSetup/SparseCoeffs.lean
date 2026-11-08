module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
### Sparse theta coefficient functions

The theta-series in the `ψI` numerator have coefficients supported on squares and triangular
numbers. This file defines the corresponding dense coefficient functions
`theta01CoeffFun`/`theta10CoeffFun : ℕ → ℤ`, proves basic support and size lemmas, and reindexes the
associated `rseries` as `tsum`s over squares or triangular numbers.
-/

namespace SpherePacking.Dim24.AppendixA

open scoped BigOperators

/-!
#### Splitting `ℤ`-indexed sums

We use `Equiv.intEquivNatSumNat : ℤ ≃ ℕ ⊕ ℕ` (inverse `Int.ofNat`/`Int.negSucc`) to split
`ℤ`-indexed `tsum`s into a nonnegative part and a negative part.
-/

/-!
#### Sparse theta coefficient functions

The theta-series involved in `ψI` are supported on squares and triangular numbers.
We model them as "dense" coefficient functions `ℕ → ℤ` so that we can use Cauchy products.
-/

/-- The square map `k ↦ k^2`, used to describe the support of `theta01CoeffFun`.-/
@[expose] public def square (k : ℕ) : ℕ := k ^ (2 : ℕ)

/--
The triangular-number map `k ↦ k * (k + 1)`, used to describe the support of
`theta10CoeffFun`.-/
@[expose] public def triangular (k : ℕ) : ℕ := k * (k + 1)

/-- Dense coefficient function supported on squares, matching the `θ_{01}` coefficients.-/
@[expose] public def theta01CoeffFun (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    if k ^ (2 : ℕ) = n then (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) else 0

/--
Dense coefficient function supported on triangular numbers,
matching the `θ_{10}` coefficients.-/
@[expose] public def theta10CoeffFun (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if k * (k + 1) = n then (2 : ℤ) else 0

/-!
#### Reindexing the sparse theta coefficient `r`-series

We will compare the Jacobi-theta definitions (as `ℤ`-indexed sums) with the `rseries` defined from
the "dense" coefficient functions `theta01CoeffFun`/`theta10CoeffFun`.
-/

end SpherePacking.Dim24.AppendixA
