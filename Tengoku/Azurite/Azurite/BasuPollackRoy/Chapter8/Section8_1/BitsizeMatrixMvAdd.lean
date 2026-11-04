/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMvAdd
import Tengoku.Seed.Algebra.MvPolynomial.Degrees
import Tengoku.Seed.Data.Matrix.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §8.1: Total degree and coefficient bitsize of a sum of two matrices
            over `ℤ[Y₁, …, Y_t]`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact: if `M, N` are sum-compatible matrices over
`A = ℤ[Y₁, …, Y_t]` whose entries have total degree in `Y` bounded by
`c` and whose coefficient bitsizes are bounded by `τ`, then the entries
of `M + N` have total degree in `Y` bounded by `c` and their coefficient
bitsizes are bounded by `τ + 1`.

The degree claim is `totalDegree (P + Q) ≤ max (totalDegree P) (totalDegree Q)`
applied entrywise. The bitsize claim is the multivariate-polynomial-sum
bitsize bound (BPR §8.1) applied entrywise.
-/

namespace Azurite.BPR

/-- **BPR §8.1 (unnumbered lemma, degree part).** Entrywise total degrees
    of a sum of two matrices over `MvPolynomial σ ℤ` are bounded by the
    common entrywise total-degree bound on the summands.
@isnad1 id=le.2h8v.s7.188760239cdf from=translated src=- shape=9357ca0b vocab=db2f35af
-/
theorem Matrix.totalDegree_mvAdd_le {σ m n : Type _}
    {M N : Matrix m n (MvPolynomial σ ℤ)} {c : ℕ}
    (hM : ∀ i j, (M i j).totalDegree ≤ c)
    (hN : ∀ i j, (N i j).totalDegree ≤ c) :
    ∀ i j, ((M + N) i j).totalDegree ≤ c := by
  intro i j
  rw [_root_.Matrix.add_apply]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hM i j) (hN i j))

end Azurite.BPR
