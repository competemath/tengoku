/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitSum
public import Tengoku.Seed.Data.Nat.Choose.Multinomial
public import Tengoku.Seed.Data.Nat.Prime.Factorial
public import Tengoku.Seed.Algebra.BigOperators.Associated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multinomial coefficients modulo the residue characteristic (Layer 1, REF-18c2c4)

This file records the elementary prime-to-`ℓ` facts needed for the
digit-sum form of Stickelberger's congruence.

The coefficient that appears in the leading Stickelberger term is controlled
by the factorials of the base-`ℓ` digits. Since every digit is `< ℓ`, their
factorials are all prime to `ℓ`, and so is their product. We also include the
carry-free multinomial corollary: if the total degree is `< ℓ`, then the
corresponding multinomial coefficient is non-zero modulo `ℓ`.
-/

@[expose] public section

namespace BernoulliRegular

namespace Furtwaengler

/-- The `i`-th base-`ℓ` digit of `a`, extended by zero past the end of the
finite digit list.-/
def standardDigit (ℓ a i : ℕ) : ℕ :=
  (Nat.digits ℓ a).getD i 0

/-- In a base at least two, every extended standard digit is less than the
base.
@isnad1 id=lt.1h3v.s4.21a49132ed82 from=translated src=- shape=2958f4d1 vocab=33e336b0
-/
theorem standardDigit_lt_base {ℓ a i : ℕ} (hℓ : 2 ≤ ℓ) :
    standardDigit ℓ a i < ℓ := by
  simp only [standardDigit]
  rw [Nat.getD_digits a i hℓ]
  exact Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 2) hℓ)

/-- If `ℓ` is prime and `n < ℓ`, then `ℓ` does not divide `n!`.
@isnad1 id=not.1h2v.s4.9f7acf010daf from=translated src=- shape=4d8ab2c6 vocab=8cd76d9e
-/
theorem factorial_not_dvd_of_lt_prime {ℓ n : ℕ} [Fact (Nat.Prime ℓ)] (hn : n < ℓ) :
    ¬ ℓ ∣ Nat.factorial n := fun h =>
  Nat.not_lt.mpr ((Nat.Prime.dvd_factorial (Fact.out : Nat.Prime ℓ)).mp h) hn

/-- A product of factorials of numbers `< ℓ` is prime to `ℓ`.
@isnad1 id=not.1h4v.s5.30c27a89471b from=translated src=- shape=9062f6e2 vocab=b7b640bd
-/
theorem prod_factorial_not_dvd_of_lt_prime {α : Type*}
    {s : Finset α} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {d : α → ℕ}
    (hd : ∀ i ∈ s, d i < ℓ) :
    ¬ ℓ ∣ ∏ i ∈ s, Nat.factorial (d i) :=
  (Fact.out : Nat.Prime ℓ).prime.not_dvd_finsetProd
    (fun i hi => factorial_not_dvd_of_lt_prime (hd i hi))

/-- The product of factorials of the standard base-`ℓ` digits is prime to
`ℓ`. This is the unit-denominator fact used in the leading coefficient of
the digit-sum Stickelberger congruence.
@isnad1 id=not.0h3v.s4.77223e01a34c from=translated src=- shape=a6263b24 vocab=288f0222
-/
theorem standardDigit_factorial_prod_not_dvd {ℓ a f : ℕ} [Fact (Nat.Prime ℓ)] :
    ¬ ℓ ∣ ∏ i ∈ Finset.range f, Nat.factorial (standardDigit ℓ a i) := by
  refine prod_factorial_not_dvd_of_lt_prime ?_
  intro i _hi
  exact standardDigit_lt_base (Fact.out : Nat.Prime ℓ).two_le

/-- Carry-free multinomial non-vanishing modulo `ℓ`: if the total degree is
strictly less than the prime `ℓ`, then the multinomial coefficient is not
divisible by `ℓ`.
@isnad1 id=not.1h4v.s5.f1df68b90f98 from=translated src=- shape=649f1666 vocab=0d9f31a0
-/
theorem multinomial_not_dvd_of_sum_lt {α : Type*}
    {s : Finset α} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {d : α → ℕ}
    (hsum : (∑ i ∈ s, d i) < ℓ) :
    ¬ ℓ ∣ Nat.multinomial s d := by
  intro h
  have hprod :
      ℓ ∣ (∏ i ∈ s, Nat.factorial (d i)) * Nat.multinomial s d :=
    dvd_mul_of_dvd_right h _
  rw [Nat.multinomial_spec] at hprod
  exact factorial_not_dvd_of_lt_prime hsum hprod

/-- Standard-digit version of `multinomial_not_dvd_of_sum_lt`. The extra
hypothesis is exactly the carry-free condition for the ordinary sum of the
digits.
@isnad1 id=not.1h3v.s5.ceac3216f424 from=translated src=- shape=4624a2d4 vocab=8d532ce7
-/
theorem multinomial_digits_not_dvd {ℓ a f : ℕ} [Fact (Nat.Prime ℓ)]
    (hsum : (∑ i ∈ Finset.range f, standardDigit ℓ a i) < ℓ) :
    ¬ ℓ ∣ Nat.multinomial (Finset.range f) (standardDigit ℓ a) :=
  multinomial_not_dvd_of_sum_lt hsum

end Furtwaengler

end BernoulliRegular
