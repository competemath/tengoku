/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.Notation_8_7
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter8.Section8_1.Algorithm_8_8
import Tengoku.Seed.Algebra.Polynomial.Degree.SmallDegree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §8.1 Algorithm 8.10: Special translation

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

Given `P = aₚ Xᵖ + ⋯ + a₀ ∈ A[X]` and `b, c ∈ A`, compute the
polynomial `Q = cᵖ · P((X − b) / c)` without leaving `A`:

  - Initialize `result := aₚ`, `d := 1`.
  - For `i` from `1` to `p`:
    - `d := c · d`
    - `result := result · (c·X − b) + (d · aₚ₋ᵢ)`
  - Output `result = cᵖ · P((X − b) / c)`.

The intermediate polynomial sequence is captured by
`Polynomial.specialTrans`, defined (outside `Azurite.BPR`, extending
Mathlib's `Polynomial`) via the recurrence above. Over a field with
`c ≠ 0`, this satisfies `specialTrans P b c i = C(cⁱ) · Hor_i(P, X − b/c)`
where `Hor_i` is the Horner polynomial from Notation 8.7. The bitsize
bound on the coefficients of `specialTrans` over `ℤ` is recorded as
`Polynomial.bitsize_specialTrans_coeff_le`.
-/

section SpecialTranslation

open Polynomial Finset

variable {R : Type*} [CommRing R]

/-- **BPR Algorithm 8.10 (Special Translation).** Given `P ∈ R[X]`
    with `p = natDegree P`, and elements `b, c ∈ R`, the `i`-th
    intermediate polynomial is:
    - `specialTrans P b c 0 = C(aₚ)`
    - `specialTrans P b c (i+1) = (C c * X - C b) * specialTrans P b c i
                                    + C(c^{i+1} * aₚ₋ᵢ₋₁)`

    The output `specialTrans P b c p = cᵖ P((X − b)/c)`.-/
noncomputable def Polynomial.specialTrans (P : R[X]) (b c : R) : ℕ → R[X]
  | 0 => C (P.coeff P.natDegree)
  | i + 1 => (C c * X - C b) * P.specialTrans b c i +
      C (c ^ (i + 1) * P.coeff (P.natDegree - (i + 1)))

/-- The base case: `specialTrans P b c 0 = C(leadingCoeff P)`.
@isnad1 id=eq.0h4v.s6.f8e460837d67 from=translated src=- shape=47f22a51 vocab=53499db6
-/
theorem Polynomial.specialTrans_zero (P : R[X]) (b c : R) :
    P.specialTrans b c 0 = C P.leadingCoeff := by
  unfold Polynomial.specialTrans; rw [leadingCoeff]

/-- **Closed-form characterization.**
    `specialTrans P b c i = ∑ j ∈ range (i+1), C(aₚ₋ⱼ · cʲ) · (cX − b)^{i−j}`.
@isnad1 id=eq.0h5v.s9.1a128dad1132 from=translated src=- shape=f3c683f0 vocab=b62fed3f
-/
theorem Polynomial.specialTrans_eq_sum (P : R[X]) (b c : R) (i : ℕ) :
    P.specialTrans b c i = ∑ j ∈ range (i + 1),
      C (P.coeff (P.natDegree - j) * c ^ j) * (C c * X - C b) ^ (i - j) := by
  induction i with
  | zero => simp [Polynomial.specialTrans]
  | succ n ih =>
    rw [Polynomial.specialTrans, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show n + 1 - (n + 1) = 0 from Nat.sub_self _, pow_zero, mul_one,
        show c ^ (n + 1) * P.coeff (P.natDegree - (n + 1)) =
          P.coeff (P.natDegree - (n + 1)) * c ^ (n + 1) from by ring]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mul_comm (C c * X - C b), mul_assoc, ← pow_succ,
        show n - j + 1 = n + 1 - j from by omega]

private theorem cx_sub_b_eq {K : Type*} [Field K] (b c : K) (hc : c ≠ 0) :
    X - C (b * c⁻¹) = C c⁻¹ * (C c * X - C b) := by
  have h1 : C c⁻¹ * (C c * X) = X := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  have h2 : C c⁻¹ * C b = C (b * c⁻¹) := by
    rw [← map_mul, mul_comm]
  rw [mul_sub, h1, h2]

/-- **BPR Algorithm 8.10 (field characterization).**
    Over a field with `c ≠ 0`:

    `specialTrans P b c i = C(cⁱ) · Horᵢ(P, X − b·c⁻¹)`,

    i.e. `SpecialTransᵢ = cⁱ (aₚ(X − b/c)ⁱ + ⋯ + aₚ₋ᵢ)`.
@isnad1 id=eq.1h5v.s8.bebef64a2a63 from=translated src=- shape=797b0bce vocab=6478332c
-/
theorem Polynomial.specialTrans_eq_horner_comp {K : Type*} [Field K]
    (P : K[X]) (b c : K) (hc : c ≠ 0) (i : ℕ) :
    P.specialTrans b c i =
      C (c ^ i) * (P.horner i).comp (X - C (b * c⁻¹)) := by
  rw [Polynomial.horner_eq_sum, Polynomial.specialTrans_eq_sum]
  show _ = C (c ^ i) * eval₂ C (X - C (b * c⁻¹)) _
  rw [eval₂_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj; rw [Finset.mem_range] at hj
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  rw [cx_sub_b_eq b c hc, mul_pow]
  simp only [← C_pow, ← mul_assoc, ← map_mul]
  congr 1; congr 1
  rw [show c⁻¹ ^ (i - j) = (c ^ (i - j))⁻¹ from inv_pow c (i - j)]
  rw [show c ^ i * P.coeff (P.natDegree - j) * (c ^ (i - j))⁻¹ =
    P.coeff (P.natDegree - j) * (c ^ i * (c ^ (i - j))⁻¹) from by ring]
  rw [← pow_sub₀ c hc (by omega : i - j ≤ i),
      show i - (i - j) = j from by omega]

end SpecialTranslation

/-! ### Bitsize bound on SpecialTrans coefficients -/

section SpecialTransBitsize

open Polynomial Finset Azurite.BPR

end SpecialTransBitsize
