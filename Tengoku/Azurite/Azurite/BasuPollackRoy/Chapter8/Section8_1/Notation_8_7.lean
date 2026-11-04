/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.Algebra.Polynomial.Coeff
import Tengoku.Seed.Algebra.Polynomial.Degree.Support
import Tengoku.Seed.Algebra.Polynomial.Eval.Degree
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §8.1 Notation 8.7: Horner polynomials

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1, Notation 8.7, p. 284.

Let `P = aₚ Xᵖ + ⋯ + a₀ ∈ A[X]`, where `A` is a ring. The **Horner
polynomials** associated to `P` are defined inductively by

  `Hor₀(P, X) = aₚ`,
  `Horᵢ(P, X) = X · Horᵢ₋₁(P, X) + aₚ₋ᵢ`,

for `0 ≤ i ≤ p`, so that

  `Horᵢ(P, X) = aₚ Xⁱ + aₚ₋₁ Xⁱ⁻¹ + ⋯ + aₚ₋ᵢ`.

In particular, `Horₚ(P, X) = P`. The Horner polynomials are the
intermediate state of Horner's method for evaluating `P` at a point
(Algorithm 8.7).

The definitions live in the `Polynomial` namespace (outside
`Azurite.BPR`) so they extend Mathlib's `Polynomial`.
-/

section Horner

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Notation 8.7 (Horner polynomials).** Given `P ∈ R[X]` with
    `p = natDegree P`, the `i`-th Horner polynomial is defined by:
    - `Hor₀(P, X) = C(aₚ)` (the leading coefficient as a constant polynomial)
    - `Horᵢ₊₁(P, X) = X · Horᵢ(P, X) + C(aₚ₋ᵢ₋₁)`-/
noncomputable def Polynomial.horner (P : R[X]) : ℕ → R[X]
  | 0 => C (P.coeff P.natDegree)
  | i + 1 => X * P.horner i + C (P.coeff (P.natDegree - (i + 1)))

/-- The base case: `Hor₀(P, X) = C(leadingCoeff P)`.
@isnad1 id=eq.0h2v.s6.a13487e1960e from=translated src=- shape=9c9c96e4 vocab=b892c16d
-/
theorem Polynomial.horner_zero (P : R[X]) :
    P.horner 0 = C P.leadingCoeff := by
  unfold Polynomial.horner; rw [leadingCoeff]

/-- **Closed-form characterization.**
    `Horᵢ(P, X) = ∑ j ∈ range (i+1), C(aₚ₋ⱼ) · X^{i−j}`
    `         = aₚ Xⁱ + aₚ₋₁ Xⁱ⁻¹ + ⋯ + aₚ₋ᵢ`.
@isnad1 id=eq.0h3v.s8.77ff4c14a0ed from=translated src=- shape=59eb7dc8 vocab=6c350c6c
-/
theorem Polynomial.horner_eq_sum (P : R[X]) (i : ℕ) :
    P.horner i = ∑ j ∈ range (i + 1),
      C (P.coeff (P.natDegree - j)) * X ^ (i - j) := by
  induction i with
  | zero => simp [Polynomial.horner]
  | succ n ih =>
    rw [Polynomial.horner, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_comm X (C _ * X ^ _), mul_assoc, ← pow_succ,
        show n - j + 1 = n + 1 - j from by omega]

/-- **`Horₚ(P, X) = P`.** The last Horner polynomial recovers `P`.
@isnad1 id=eq.0h2v.s5.edd52f011681 from=translated src=- shape=205427ac vocab=0e60c85c
-/
theorem Polynomial.horner_natDegree (P : R[X]) :
    P.horner P.natDegree = P := by
  rw [Polynomial.horner_eq_sum]
  conv_rhs => rw [Polynomial.as_sum_range P]
  rw [← Finset.sum_flip]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show P.natDegree - (P.natDegree - j) = j from by omega,
      C_mul_X_pow_eq_monomial]

end Horner
