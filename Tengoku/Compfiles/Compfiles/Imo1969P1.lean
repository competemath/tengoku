/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1969, Problem 1

Prove that there are infinitely many natural numbers a with the following property:
the number z = n⁴ + a is not prime for any natural number n.
-/

open Int Nat

namespace Imo1969P1

/-- `goodNats` is the set of natural numbers satisfying the condition in the problem
statement, namely the `a : ℕ` such that `n^4 + a` is not prime for any `n : ℕ`. -/
def goodNats : Set ℕ :=
  {a : ℕ | ∀ n : ℕ, ¬Nat.Prime (n ^ 4 + a)}

/--
The key to the solution is that you can factor $z$ into the product of two polynomials,
if $a = 4*m^4$. This is Sophie Germain's identity, called `pow_four_add_four_mul_pow_four`
in mathlib.
@isnad1 id=eq.0h2v.s7.35003e227826 from=translated src=- shape=f901a2de vocab=fb2191f5
-/
theorem factorization {m n : ℤ} :
    ((n - m) ^ 2 + m ^ 2) * ((n + m) ^ 2 + m ^ 2) = n ^ 4 + 4 * m ^ 4 :=
  pow_four_add_four_mul_pow_four.symm

/-
To show that the product is not prime, we need to show each of the factors is at least 2,
which `nlinarith` can solve since they are each expressed as a sum of squares.
-/

/--
@isnad1 id=lt.1h2v.s6.ccd9c00fded2 from=translated src=- shape=033919a4 vocab=0434d31e
-/
theorem left_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < (n - m) ^ 2 + m ^ 2 := by nlinarith
/--
@isnad1 id=lt.1h2v.s6.36af0def6465 from=translated src=- shape=36305670 vocab=5dab6d08
-/
theorem right_factor_large {m : ℤ} (n : ℤ) (h : 1 < m) : 1 < (n + m) ^ 2 + m ^ 2 := by nlinarith

/-
The factorization is over the integers, but we need the nonprimality over the natural numbers.
-/

/--
@isnad1 id=lt.1h1v.s4.5447aee83031 from=translated src=- shape=7f2e781e vocab=13778d90
-/
theorem int_large {m : ℤ} (h : 1 < m) : 1 < m.natAbs := by
  exact_mod_cast lt_of_lt_of_le h le_natAbs

/--
@isnad1 id=not.3h3v.s5.a35d788e01c0 from=translated src=- shape=559606a0 vocab=19912e74
-/
theorem not_prime_of_int_mul' {m n : ℤ} {c : ℕ} (hm : 1 < m) (hn : 1 < n) (hc : m * n = (c : ℤ)) :
    ¬Nat.Prime c :=
  not_prime_of_int_mul (int_large hm).ne' (int_large hn).ne' hc

/-- Every natural number of the form `n^4 + 4*m^4` is not prime.
@isnad1 id=not.1h2v.s6.2d148218e1d9 from=translated src=- shape=2f396bb1 vocab=195c7936
-/
theorem polynomial_not_prime {m : ℕ} (h1 : 1 < m) (n : ℕ) : ¬Nat.Prime (n ^ 4 + 4 * m ^ 4) := by
  have h2 : 1 < (m : ℤ) := Int.ofNat_lt.mpr h1
  refine not_prime_of_int_mul' (left_factor_large (n : ℤ) h2) (right_factor_large (n : ℤ) h2) ?_
  apply factorization

/-- We define $a_{choice}(b) := 4*(2+b)^4$, so that we can take $m = 2+b$ in `polynomial_not_prime`.
-/
def aChoice (b : ℕ) : ℕ := 4 * (2 + b) ^ 4

/--
@isnad1 id=mem.0h1v.s3.7f5a86e58112 from=translated src=- shape=ca401064 vocab=0f4ef31c
-/
theorem aChoice_good (b : ℕ) : aChoice b ∈ goodNats :=
  polynomial_not_prime (show 1 < 2 + b by lia)

/-- `aChoice` is a strictly monotone function; this is easily proven by chaining together lemmas
in the `strictMono` namespace.
@isnad1 id=strictmo.0h0v.s2.ef73df7e18b9 from=translated src=- shape=e3d48bcb vocab=a04eb1cf
-/
theorem aChoice_strictMono : StrictMono aChoice :=
  ((strictMono_id.const_add 2).nat_pow (by decide)).const_mul (by decide)

/- We conclude by using the fact that `aChoice` is an injective function from the natural numbers
to the set `goodNats`. -/

end Imo1969P1
