/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.PNat.Basic
public import Tengoku.Seed.Algebra.Notation.Prod

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `PNatPowAssoc`, where `PNat` means only strictly positive
powers are considered.

## Results

- `ppow_add` a defining property: `x ^ (k + n) = x ^ k * x ^ n`
- `ppow_one` a defining property: `x ^ 1 = x`
- `ppow_assoc` strictly positive powers of an element have associative multiplication.
- `ppow_comm` `x ^ m * x ^ n = x ^ n * x ^ m` for strictly positive `m` and `n`.
- `ppow_mul` `x ^ (m * n) = (x ^ m) ^ n` for strictly positive `m` and `n`.
- `ppow_eq_pow` monoid exponentiation coincides with semigroup exponentiation.

## Instances

- PNatPowAssoc for products and Pi types

## TODO

* `NatPowAssoc` for `MulOneClass` - more or less the same flow
* It seems unlikely that anyone will want `NatSMulAssoc` and `PNatSMulAssoc` as additive versions of
  power-associativity, but we have found that it is not hard to write.

-/

public section

-- TODO:
-- assert_not_exists MonoidWithZero

variable {M : Type*}

/-- A `Prop`-valued mixin for power-associative multiplication in the non-unital setting. -/
class PNatPowAssoc (M : Type*) [Mul M] [Pow M ℕ+] : Prop where
  /-- Multiplication is power-associative. -/
  protected ppow_add : ∀ (k n : ℕ+) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent one is identity. -/
  protected ppow_one : ∀ (x : M), x ^ (1 : ℕ+) = x

section Mul

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

/--
@isnad1 id=eq.0h4v.s6.de90487472e5 from=seed src=0 shape=a8c27be6 vocab=bbf23d31
-/
theorem ppow_add (k n : ℕ+) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  PNatPowAssoc.ppow_add k n x

/--
@isnad1 id=eq.0h2v.s5.c2e7cd9b7666 from=seed src=0 shape=b6ef50d8 vocab=c775bee5
-/
@[simp]
theorem ppow_one (x : M) : x ^ (1 : ℕ+) = x :=
  PNatPowAssoc.ppow_one x

/--
@isnad1 id=eq.0h5v.s6.21c9cab99071 from=seed src=0 shape=251b6dc7 vocab=aabf8933
-/
theorem ppow_mul_assoc (k m n : ℕ+) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← ppow_add, add_assoc]

/--
@isnad1 id=eq.0h4v.s6.e7c0738841f0 from=seed src=0 shape=167bad42 vocab=aabf8933
-/
theorem ppow_mul_comm (m n : ℕ+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]

/--
@isnad1 id=eq.0h4v.s5.c47f7fc8d105 from=seed src=0 shape=d155515b vocab=aabf8933
-/
theorem ppow_mul (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | one => rw [ppow_one, mul_one]
  | succ k hk => rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

/--
@isnad1 id=eq.0h4v.s5.4929b1b20c63 from=seed src=0 shape=01d3dfa3 vocab=aabf8933
-/
theorem ppow_mul' (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact ppow_mul x n m

end Mul

/--
@isnad1 id=pnatpowa.0h2v.s5.583d28b3441d from=seed src=0 shape=b366095d vocab=fa140702
-/
instance Pi.instPNatPowAssoc {ι : Type*} {α : ι → Type*} [∀ i, Mul <| α i] [∀ i, Pow (α i) ℕ+]
    [∀ i, PNatPowAssoc <| α i] : PNatPowAssoc (∀ i, α i) where
  ppow_add _ _ _ := by ext; simp [ppow_add]
  ppow_one _ := by ext; simp

/--
@isnad1 id=pnatpowa.0h2v.s5.0c2898c67344 from=seed src=0 shape=bdd418be vocab=469c8ee8
-/
instance Prod.instPNatPowAssoc {N : Type*} [Mul M] [Pow M ℕ+] [PNatPowAssoc M] [Mul N] [Pow N ℕ+]
    [PNatPowAssoc N] : PNatPowAssoc (M × N) where
  ppow_add _ _ _ := by ext <;> simp [ppow_add]
  ppow_one _ := by ext <;> simp

/--
@isnad1 id=eq.0h3v.s5.838359b97aa4 from=seed src=0 shape=68018325 vocab=a735fa7e
-/
theorem ppow_eq_pow [Monoid M] [Pow M ℕ+] [PNatPowAssoc M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => rw [ppow_one, PNat.one_coe, pow_one]
  | succ k hk => rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]
