/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Kevin Lacker
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Tactic.Ring

/-!
# Identities

This file contains some "named" commutative ring identities.
-/

public section


variable {R : Type*} [CommRing R] {a b x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n : R}

/-- Brahmagupta-Fibonacci identity or Diophantus identity, see
<https://en.wikipedia.org/wiki/Brahmagupta%E2%80%93Fibonacci_identity>.

This sign choice here corresponds to the signs obtained by multiplying two complex numbers.
@isnad1 id=eq.0h5v.s8.8eb2894ca5dc from=seed src=0 shape=3bf51390 vocab=9c1cdc1d
-/
theorem sq_add_sq_mul_sq_add_sq :
    (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) = (x₁ * y₁ - x₂ * y₂) ^ 2 + (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  ring

/-- Brahmagupta's identity, see <https://en.wikipedia.org/wiki/Brahmagupta%27s_identity>
@isnad1 id=eq.0h6v.s8.6d500d3c1363 from=seed src=0 shape=66481669 vocab=9c1cdc1d
-/
theorem sq_add_mul_sq_mul_sq_add_mul_sq :
    (x₁ ^ 2 + n * x₂ ^ 2) * (y₁ ^ 2 + n * y₂ ^ 2) =
    (x₁ * y₁ - n * x₂ * y₂) ^ 2 + n * (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  ring

/-- Sophie Germain's identity, see <https://www.cut-the-knot.org/blue/SophieGermainIdentity.shtml>.
@isnad1 id=eq.0h3v.s8.0302e46821a4 from=seed src=0 shape=aa53c5b3 vocab=9c1cdc1d
-/
theorem pow_four_add_four_mul_pow_four :
    a ^ 4 + 4 * b ^ 4 = ((a - b) ^ 2 + b ^ 2) * ((a + b) ^ 2 + b ^ 2) := by
  ring

/-- Sophie Germain's identity, see <https://www.cut-the-knot.org/blue/SophieGermainIdentity.shtml>.
@isnad1 id=eq.0h3v.s8.96c04c858ea3 from=seed src=0 shape=ba975ff3 vocab=9c1cdc1d
-/
theorem pow_four_add_four_mul_pow_four' :
    a ^ 4 + 4 * b ^ 4 = (a ^ 2 - 2 * a * b + 2 * b ^ 2) * (a ^ 2 + 2 * a * b + 2 * b ^ 2) := by
  ring

/-- Euler's four-square identity, see <https://en.wikipedia.org/wiki/Euler%27s_four-square_identity>.

This sign choice here corresponds to the signs obtained by multiplying two quaternions.
@isnad1 id=eq.0h9v.s9.45d331d2f2a8 from=seed src=0 shape=7697f2b3 vocab=9c1cdc1d
-/
theorem sum_four_sq_mul_sum_four_sq :
    (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) * (y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2) =
      (x₁ * y₁ - x₂ * y₂ - x₃ * y₃ - x₄ * y₄) ^ 2 + (x₁ * y₂ + x₂ * y₁ + x₃ * y₄ - x₄ * y₃) ^ 2 +
          (x₁ * y₃ - x₂ * y₄ + x₃ * y₁ + x₄ * y₂) ^ 2 +
        (x₁ * y₄ + x₂ * y₃ - x₃ * y₂ + x₄ * y₁) ^ 2 := by
  ring

/-- Degen's eight squares identity, see <https://en.wikipedia.org/wiki/Degen%27s_eight-square_identity>.

This sign choice here corresponds to the signs obtained by multiplying two octonions.
@isnad1 id=eq.0h17v.s11.68b9b1f3bd22 from=seed src=0 shape=a4fe5f61 vocab=9c1cdc1d
-/
theorem sum_eight_sq_mul_sum_eight_sq :
    (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 + x₅ ^ 2 + x₆ ^ 2 + x₇ ^ 2 + x₈ ^ 2) *
      (y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 + y₅ ^ 2 + y₆ ^ 2 + y₇ ^ 2 + y₈ ^ 2) =
    (x₁ * y₁ - x₂ * y₂ - x₃ * y₃ - x₄ * y₄ - x₅ * y₅ - x₆ * y₆ - x₇ * y₇ - x₈ * y₈) ^ 2 +
      (x₁ * y₂ + x₂ * y₁ + x₃ * y₄ - x₄ * y₃ + x₅ * y₆ - x₆ * y₅ - x₇ * y₈ + x₈ * y₇) ^ 2 +
      (x₁ * y₃ - x₂ * y₄ + x₃ * y₁ + x₄ * y₂ + x₅ * y₇ + x₆ * y₈ - x₇ * y₅ - x₈ * y₆) ^ 2 +
      (x₁ * y₄ + x₂ * y₃ - x₃ * y₂ + x₄ * y₁ + x₅ * y₈ - x₆ * y₇ + x₇ * y₆ - x₈ * y₅) ^ 2 +
      (x₁ * y₅ - x₂ * y₆ - x₃ * y₇ - x₄ * y₈ + x₅ * y₁ + x₆ * y₂ + x₇ * y₃ + x₈ * y₄) ^ 2 +
      (x₁ * y₆ + x₂ * y₅ - x₃ * y₈ + x₄ * y₇ - x₅ * y₂ + x₆ * y₁ - x₇ * y₄ + x₈ * y₃) ^ 2 +
      (x₁ * y₇ + x₂ * y₈ + x₃ * y₅ - x₄ * y₆ - x₅ * y₃ + x₆ * y₄ + x₇ * y₁ - x₈ * y₂) ^ 2 +
      (x₁ * y₈ - x₂ * y₇ + x₃ * y₆ + x₄ * y₅ - x₅ * y₄ - x₆ * y₃ + x₇ * y₂ + x₈ * y₁) ^ 2 := by
  ring
