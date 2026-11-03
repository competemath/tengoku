/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.Data.Nat.Size
import Tengoku.Seed.Algebra.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §8.1: Bitsize of a sum of two multivariate polynomials

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact: if every coefficient of two multivariate
polynomials `P, Q ∈ ℤ[X₁, …, Xₖ]` has bitsize `≤ τ`, then every
coefficient of `P + Q` has bitsize `≤ τ + 1`.

Proof: for each monomial `m`, `coeff m (P + Q) = coeff m P + coeff m Q`,
and `|a + b| ≤ |a| + |b| < 2^τ + 2^τ = 2^{τ + 1}`.
-/

namespace Azurite.BPR

/-- `bitsize(a + b) ≤ τ + 1` when `bitsize a ≤ τ` and `bitsize b ≤ τ`.-/
theorem Int.size_add_le (a b : ℤ) (τ : ℕ)
    (ha : a.natAbs.size ≤ τ) (hb : b.natAbs.size ≤ τ) :
    (a + b).natAbs.size ≤ τ + 1 := by
  rw [Nat.size_le] at ha hb ⊢
  have hab : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
  have : 2 ^ τ + 2 ^ τ = 2 ^ (τ + 1) := by rw [pow_succ]; omega
  omega

end Azurite.BPR
