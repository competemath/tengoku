/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Internal

/-!
# Irreducible binomial moduli from one noncube coefficient

Every noncube `a` gives the monic irreducible modulus `X^(3^s) - a` of exact
degree `3^s`, including `s = 0`. Such coefficients exist in every finite field
whose multiplicative-group order is divisible by three.

Irreducibility reuses Mathlib's
`X_pow_sub_C_irreducible_of_prime_pow_of_ne_two`, formalized by Andrew Yang and
Patrick Lutz in `Mathlib.FieldTheory.KummerExtension`:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/KummerExtension.html.
Noncube existence uses Cauchy's finite-group theorem, Mathlib's
`Fintype.card_units`, and equivalence of injectivity and surjectivity on a
finite type. This layer supplies no encoded selection algorithm or runtime
claim; the field, coefficient, and exponent remain parameters.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The leading coefficient is one for every coefficient and exponent.
@isnad1 id=monic.0h3v.s4.66b14189c414 from=translated src=- shape=4a5c8032 vocab=524dc6e5
-/
theorem binomialModulus_monic {F : Type*} [Ring F] (a : F) (s : Nat) :
    (binomialModulus a s).Monic :=
  Internal.binomialModulus_monic a s

/-- The degree is exactly `3^s`, including degree one at `s = 0`.
@isnad1 id=eq.0h3v.s5.2bc68316429e from=translated src=- shape=ec4268a7 vocab=8a91b161
-/
theorem binomialModulus_natDegree {F : Type*} [Ring F] [Nontrivial F] (a : F) (s : Nat) :
    (binomialModulus a s).natDegree = 3 ^ s :=
  Internal.binomialModulus_natDegree a s

/-- Divisibility of the multiplicative-group order guarantees a noncube.
@isnad1 id=ex.1h1v.s6.8b3c9df4de22 from=translated src=- shape=7fd03aab vocab=2a8d903b
-/
theorem exists_noncube {F : Type*} [Field F] [Fintype F]
    (divisible : 3 ∣ Fintype.card F - 1) : ∃ a : F, ∀ b : F, b ^ 3 ≠ a :=
  Internal.exists_noncube divisible

/-- A binary field cardinality with even exponent has unit-group order divisible
by three. Only the cardinality identity is needed for this arithmetic fact.
@isnad1 id=dvd.2h2v.s5.8ea1937329dd from=translated src=- shape=05b3e8d1 vocab=67eebe52
-/
theorem three_dvd_card_sub_one_of_even_exponent {F : Type*} [Fintype F] {b : Nat}
    (cardinality : Fintype.card F = 2 ^ b) (even : Even b) :
    3 ∣ Fintype.card F - 1 :=
  Internal.three_dvd_card_sub_one_of_even_exponent cardinality even

/-- Rounding a positive target degree up to a power of three increases it by
less than a factor of three.
@isnad1 id=and.1h3v.s6.415c08c7bbec from=translated src=- shape=81f55119 vocab=82d312bb
-/
theorem binomialModulus_natDegree_clog_bounds {F : Type*} [Ring F] [Nontrivial F]
    (a : F) {n : Nat} (positive : 0 < n) :
    n ≤ (binomialModulus a (Nat.clog 3 n)).natDegree ∧
      (binomialModulus a (Nat.clog 3 n)).natDegree < 3 * n :=
  Internal.binomialModulus_natDegree_clog_bounds a positive

end Algebraic.Cutwidth.Extractor
