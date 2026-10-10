/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Christopher Schmidt
-/
import Tengoku
--set_option trace.simp_lemmas true

open Nat
open Finset
open BigOperators

/-!
# Binomial coefficients are (almost) never powers
## TODO
  - Lemmata
    - .. for Step 1: needs golfing
  - (1)
  - (2)
  - (3)
  - (4)
  There is a somewhat more detailed, but quite messy version of the lean3 version here:
  https://github.com/mo271/FormalBook/blob/92f57b44cbbc1cd02ca77994efe8d8e6de050a19/src/chapters/03_Binomial_coefficients_are_(almost)_never_powers.lean
  Let's not follow that, but keep the proof cleaner.
### Sylvester's Theorem
There is no proof given in the book, perhaps check out Erdős' for a proof to formalize.
-/
namespace chapter3

/-!
### Lemmata for Step 1 and Step 2
-/
example (a p : ℕ) (h : p ∣ a) (g : a < p): a = 0 := eq_zero_of_dvd_of_lt h g

theorem prime_div_descFactorial (n k m l p : ℕ) (h_klen : k ≤ n)
  (h_p : p.Prime) (h_p_div_binom : p ∣ choose n k) (H : choose n k = m^l) :
  p^l ∣ n.descFactorial k := by

  have h_p_div_ml : p ∣ m^l := by
    rw [← H]
    exact h_p_div_binom
  have h_pl_div_ml : p^l ∣ m^l := by
    exact pow_dvd_pow_of_dvd (Nat.Prime.dvd_of_dvd_pow (h_p) (h_p_div_ml)) l
  have h_pl_div_binom : p^l ∣ choose n k := by
    rw [H]
    exact h_pl_div_ml
  have h_pl_div_fac : p^l ∣  (n.factorial / (k.factorial * (n-k).factorial)) := by
    rw [← Nat.choose_eq_factorial_div_factorial h_klen]
    exact h_pl_div_binom

  -- here we start using qify to handle division
  have h_fac_div : ((↑k ! * ↑(n - k)!) : ℤ)  ∣ (n ! : ℤ) :=
    mod_cast factorial_mul_factorial_dvd_factorial h_klen
  have h_fac_div' : ↑(n - k)! ∣ (n ! : ℤ) := dvd_of_mul_left_dvd h_fac_div
  have h_fac_div'' : (k ! : ℤ) ∣ (↑n ! / ↑(n - k)!) := by
    refine' mod_cast (dvd_div_iff_mul_dvd ((Int.natCast_dvd_natCast).mp h_fac_div')).mpr _
    rw [mul_comm]
    exact mod_cast h_fac_div
  have h_kfac_ne_zero : (k ! : ℚ) ≠ 0 := cast_ne_zero.mpr (factorial_ne_zero k)
  have h_nkfac_ne_zero : ((n - k)! : ℚ) ≠ 0 := cast_ne_zero.mpr (n - k).factorial_ne_zero
  have : (k ! * (n - k)! : ℚ) ≠ 0 := mul_ne_zero h_kfac_ne_zero h_nkfac_ne_zero
  have h_fraction: (n.factorial / (k.factorial * (n - k).factorial)) =
    (n.factorial / (n - k).factorial) / k.factorial := by
    qify
    simp
    rw [mul_comm]
    norm_cast
    exact (Nat.div_div_eq_div_mul n ! (n - k)! k !).symm
  rw [h_fraction] at h_pl_div_fac
  have h_pl_div_fac_part: p^l ∣ (n.factorial / (n - k).factorial) := by
    have h_eq_pl_with_k := exists_eq_mul_right_of_dvd h_pl_div_fac
    have h_eq_pl : ∃ (r : ℕ), r * p^l = n.factorial / (n - k).factorial := by
      rcases h_eq_pl_with_k with ⟨j, h_eq⟩
      use (j * k.factorial)
      rw [(mul_rotate _ _ _).symm, ← h_eq]
      qify
      aesop
    rcases h_eq_pl with ⟨j, h_eq⟩
    refine' Dvd.intro j _
    rw [mul_comm]
    exact h_eq
  rw [descFactorial_eq_div h_klen]
  convert h_pl_div_fac_part

/- now in mathlib? -/

/-
### Erdős' Theorem
Using ℕ instead of ℤ here, because of the definition of `choose` and because of the inequalities.
-/

end chapter3
