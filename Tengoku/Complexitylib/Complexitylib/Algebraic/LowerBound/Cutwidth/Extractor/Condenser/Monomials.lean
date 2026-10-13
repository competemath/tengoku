/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Monomials.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Monomials.Internal

/-!
# Exact substitution for the first GUV interpolation monomials

For every `j < K ≤ h^m`, the first `m` base-`h` digits reconstruct `j`.
Their sum is at most `m * (h - 1)`. Consequently substituting `Z^(h^i)` into
the associated monomial gives exactly `Z^j`.

For a coefficient array indexed by `Fin K`, the substituted polynomial has
degree less than `K` and is nonzero precisely when some coefficient is nonzero.
The coefficient ring can be a quotient by the extension modulus, so this is
the nonvanishing step used after reduction of the interpolation coefficients.
No field or characteristic assumption is required by this layer.

This is the base-`h` monomial indexing in Guruswami, Umans, and Vadhan,
*Unbalanced Expanders and Randomness Extractors from Parvaresh--Vardy Codes*
(2009), Section 3.1, proof of Theorem 3.3:
https://salil.seas.harvard.edu/sites/g/files/omnuum4266/files/salil/files/acm2009.pdf.
The bounds retain the given `K`, including when `K < h^m`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Each digit is below a positive base.
@isnad1 id=lt.1h4v.s4.a4d31e8499c0 from=translated src=- shape=4703a92d vocab=1567a184
-/
theorem monomialDigit_lt {h j m : Nat} (positive : 0 < h) (i : Fin m) :
    monomialDigit h j i < h :=
  Internal.monomialDigit_lt positive i

/-- The first `m` digits reconstruct every integer below `h^m`.
@isnad1 id=eq.1h3v.s6.1e370773f205 from=translated src=- shape=5c4431b0 vocab=646e28e9
-/
theorem sum_monomialDigit_mul_pow {h j m : Nat} (bound : j < h ^ m) :
    (∑ i : Fin m, monomialDigit h j i * h ^ i.val) = j :=
  Internal.sum_monomialDigit_mul_pow bound

/-- The total exponent of every digit monomial is at most `m * (h - 1)`.
@isnad1 id=le.1h3v.s5.db2ebf9fbc12 from=translated src=- shape=dc07cfa4 vocab=2c5ae9a4
-/
theorem sum_monomialDigit_le {h j m : Nat} (positive : 0 < h) :
    (∑ i : Fin m, monomialDigit h j i) ≤ m * (h - 1) :=
  Internal.sum_monomialDigit_le positive

/-- Substituting powers with weights `h^i` recovers exactly the power indexed
by the encoded integer. This holds in any commutative monoid.
@isnad1 id=eq.1h5v.s6.6cf89fdfa97c from=translated src=- shape=be8083b9 vocab=35bbab04
-/
theorem digitMonomial_pow {R : Type*} [CommMonoid R] {h j m : Nat}
    (bound : j < h ^ m) (u : R) :
    digitMonomial h j (fun i : Fin m => u ^ (h ^ i.val)) = u ^ j :=
  Internal.digitMonomial_pow bound u

/-- Substitution in the first `K` monomials preserves their distinct indices
as univariate powers, without replacing `K` by `h^m`.
@isnad1 id=eq.1h5v.s8.1662ec451a86 from=translated src=- shape=1cd56f43 vocab=d00abc11
-/
theorem digitMonomial_substitution {R : Type*} [CommSemiring R] {h K m : Nat}
    (bound : K ≤ h ^ m) (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.C (a j) *
      digitMonomial h j.val (fun i : Fin m => Polynomial.X ^ (h ^ i.val))) =
        ∑ j : Fin K, Polynomial.monomial j.val (a j) :=
  Internal.digitMonomial_substitution bound a

/-- The resulting monomial sum is the polynomial with coefficient array `a`.
@isnad1 id=eq.0h3v.s8.4748cb3f14a6 from=translated src=- shape=497bd5f6 vocab=f1b9367b
-/
theorem fin_monomial_sum_eq_ofFn {R : Type*} [Semiring R] [DecidableEq R]
    {K : Nat} (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)) = Polynomial.ofFn K a :=
  Internal.fin_monomial_sum_eq_ofFn a

/-- The first `K` powers give degree strictly below `K`, including `K = 0`.
@isnad1 id=lt.0h3v.s7.58a7b5492179 from=translated src=- shape=3a52ea05 vocab=b07db5d6
-/
theorem fin_monomial_sum_degree_lt {R : Type*} [Semiring R] {K : Nat}
    (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)).degree < K :=
  Internal.fin_monomial_sum_degree_lt a

/-- A coefficient surviving reduction makes the substituted polynomial nonzero.
@isnad1 id=iff.0h3v.s7.671ca1436eb8 from=translated src=- shape=9dd53efc vocab=ef2ee63e
-/
theorem fin_monomial_sum_ne_zero_iff {R : Type*} [Semiring R] {K : Nat}
    (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)) ≠ 0 ↔ ∃ j, a j ≠ 0 :=
  Internal.fin_monomial_sum_ne_zero_iff a

end Algebraic.Cutwidth.Extractor
