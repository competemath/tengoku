/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Localization.Away.Basic
import Tengoku.Seed.RingTheory.Ideal.Quotient.Basic
import Tengoku.Seed.Algebra.CharP.Defs
import Tengoku.Seed.Algebra.CharZero.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unit descent from a boundary complement

The explicit Kummer calculation takes place after inverting a boundary
parameter `t`.  This file proves the descent step needed afterwards: an
element not divisible by the prime element `t` was already a unit before the
localization if its image is a unit after inverting `t`.
-/

namespace EtaleFundamentalGroups.Kummer

universe u v

/--
On a horizontal prime component of characteristic zero, its defining
parameter cannot divide a positive natural number.

This is the arithmetic input needed by unit descent.  It is produced directly
from the quotient characteristic rather than being exposed as a hypothesis of
the Kummer obstruction.
@isnad1 id=not.1h3v.s7.b60b784f6556 from=translated src=- shape=c8a8d4a1 vocab=b9473428
-/
theorem not_dvd_natCast_of_charZero_quotient
    {R : Type u} [CommRing R] {t : R}
    [CharZero (R ⧸ Ideal.span {t})] (n : ℕ) (hn : 0 < n) :
    ¬ t ∣ (n : R) := by
  intro htdvd
  have hmem : (n : R) ∈ Ideal.span {t} :=
    Ideal.mem_span_singleton.mpr htdvd
  have hz : (n : R ⧸ Ideal.span {t}) = 0 := by
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  exact (Nat.cast_ne_zero.mpr hn.ne') hz

/--
Let `S` be the localization of a domain `R` obtained by inverting a prime
element `t`.  If `t` does not divide `a`, then invertibility of `a` in `S`
already implies invertibility in `R`.

In the Kummer application, `a` is the exponent.  Its nondivisibility by the
horizontal boundary parameter comes from characteristic zero on that
component; invertibility after localization is produced by the derivative of
the Kummer polynomial.
@isnad1 id=isunit.3h4v.s7.6ad2a8ac6ca3 from=translated src=- shape=2b387f53 vocab=b73681c1
-/
theorem isUnit_of_isUnit_algebraMap_away_of_prime_of_not_dvd
    {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] {t a : R} [IsLocalization.Away t S]
    (ht : Prime t) (hta : ¬ t ∣ a)
    (ha : IsUnit (algebraMap R S a)) : IsUnit a := by
  obtain ⟨m, ham⟩ :=
    (IsLocalization.Away.algebraMap_isUnit_iff t).mp ha
  obtain ⟨i, -, hai⟩ := (dvd_prime_pow ht m).mp ham
  by_cases hi : i = 0
  · subst i
    exact associated_one_iff_isUnit.mp (by simpa using hai)
  · exact (hta ((dvd_pow_self t hi).trans hai.symm.dvd)).elim

/--
Wild Kummer exponents cannot become units on the complement of a horizontal
prime boundary.

The quotient `R ⧸ (t)` having characteristic zero says that the horizontal
parameter `t` cannot divide a positive natural number.  If a characteristic
`p` specialization of `R` exists and `p ∣ n`, then `n` cannot be a unit in
`R[1/t]`: otherwise unit descent would make `n` a unit in `R`, and hence in
the characteristic-`p` target, where it is zero.
@isnad1 id=not.3h7v.s8.5fc4d441ea5b from=translated src=- shape=49a82c70 vocab=01525f9c
-/
theorem natCast_not_isUnit_algebraMap_away_of_dvd_char
    {R : Type u} {S : Type v} {k : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [CommRing k] [Nontrivial k] {t : R} [IsLocalization.Away t S]
    (ht : Prime t) [CharZero (R ⧸ Ideal.span {t})]
    (φ : R →+* k) (p n : ℕ) [CharP k p]
    (hn : 0 < n) (hpn : p ∣ n) :
    ¬ IsUnit (algebraMap R S (n : R)) := by
  intro hnS
  have hnR :=
    isUnit_of_isUnit_algebraMap_away_of_prime_of_not_dvd
      ht (a := (n : R))
      (not_dvd_natCast_of_charZero_quotient n hn) hnS
  have hnk : IsUnit (n : k) := by
    simpa using hnR.map φ
  exact hnk.ne_zero ((CharP.cast_eq_zero_iff k p n).mpr hpn)

end EtaleFundamentalGroups.Kummer
