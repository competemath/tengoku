/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.BitsizeMvAdd
import Tengoku.Seed.Data.Matrix.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §8.1: Bitsize of a sum of two matrices

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact: if `M` and `N` are sum-compatible matrices
over `ℤ` whose entries all have bitsize `≤ τ`, then every entry of
`M + N` has bitsize `≤ τ + 1`.

Proof: for each index pair `(i, j)`, `(M + N) i j = M i j + N i j`,
and `|a + b| ≤ |a| + |b| < 2^τ + 2^τ = 2^{τ + 1}`.
-/

namespace Azurite.BPR

/-- **BPR §8.1 (unnumbered lemma).** Adding two sum-compatible matrices
    over `ℤ` whose entry bitsizes are bounded by `τ` produces a matrix
    whose entry bitsizes are bounded by `τ + 1`.
@isnad1 id=le.2h7v.s6.29228b848469 from=translated src=- shape=8db6f589 vocab=6560299b
-/
theorem Matrix.bitsize_add_le {m n : Type _}
    {M N : Matrix m n ℤ} {τ : ℕ}
    (hM : ∀ i j, (M i j).natAbs.size ≤ τ)
    (hN : ∀ i j, (N i j).natAbs.size ≤ τ) :
    ∀ i j, ((M + N) i j).natAbs.size ≤ τ + 1 := by
  intro i j
  rw [_root_.Matrix.add_apply]
  exact Int.size_add_le _ _ τ (hM i j) (hN i j)

end Azurite.BPR
