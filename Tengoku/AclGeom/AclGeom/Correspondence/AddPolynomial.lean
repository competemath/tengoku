/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Algebra.Polynomial.Taylor
import Tengoku.Seed.Data.Nat.Choose.Lucas
import Tengoku.Seed.FieldTheory.Perfect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Additive polynomials

The additive-polynomial library (blueprint checklist C1), feeding the
classification of one-dimensional subgroups of `Ga²`
(blueprint Lemma `subgroup-classification` (a)):

* `IsAdditive P`: `P` takes sums to sums pointwise;
* closure under `0`, `X`, addition, left multiplication by constants,
  composition, and `p`-power monomials in characteristic `p`;
* `IsAdditive.natCast_choose_mul_coeff`: over an infinite field, additivity
  kills every coefficient weighted by an intermediate binomial coefficient
  (via Taylor expansion and Hasse derivatives);
* `IsAdditive.eq_C_mul_X` (characteristic zero: additive polynomials are
  linear) and `IsAdditive.coeff_eq_zero_of_ne_pow` (characteristic `p`:
  the support consists of `p`-power monomials, via Lucas' theorem).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C1).
-/

namespace AclGeom

open Polynomial

noncomputable section

/-- The arithmetic core of blueprint Lemma `subgroup-classification` (a): a
positive natural number all of whose intermediate binomial coefficients are
divisible by a prime `p` is a power of `p` (via Lucas' theorem).-/
theorem eq_pow_of_forall_dvd_choose (p : ℕ) (hp : p.Prime) :
    ∀ i : ℕ, 1 ≤ i → (∀ j, 0 < j → j < i → p ∣ i.choose j) → ∃ r, i = p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi h
    rcases eq_or_lt_of_le hi with h1 | h2
    · exact ⟨0, h1.symm⟩
    -- Now `2 ≤ i`.
    rcases lt_or_ge i p with hip | hpi
    · -- `i < p`: the binomial `C(i,1) = i` would be divisible by `p`.
      exfalso
      have hdvd := h 1 one_pos h2
      rw [Nat.choose_one_right] at hdvd
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
    -- `p ≤ i`. Split on the last base-`p` digit of `i`.
    rcases Nat.eq_zero_or_pos (i % p) with hd | hd
    · -- `i = p * (i / p)`; the divisibility hypothesis descends via Lucas.
      have hpm : p * (i / p) = i := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hd)
      have hm1 : 1 ≤ i / p := (Nat.one_le_div_iff hp.pos).2 hpi
      have hmlt : i / p < i := Nat.div_lt_self (by omega) hp.one_lt
      have hdesc : ∀ j, 0 < j → j < i / p → p ∣ (i / p).choose j := by
        intro j hj0 hjm
        have hlt : p * j < i := by
          calc p * j < p * (i / p) := (Nat.mul_lt_mul_left hp.pos).2 hjm
          _ = i := hpm
        have key := h (p * j) (Nat.mul_pos hp.pos hj0) hlt
        have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (n := i) (k := p * j) (p := p)
        rw [Nat.mul_mod_right, hd, Nat.choose_self, one_mul,
          Nat.mul_div_cancel_left j hp.pos] at hluc
        -- `p ∣ C(i, p*j)` and `C(i, p*j) ≡ C(i/p, j) [MOD p]`.
        exact (Nat.modEq_zero_iff_dvd).1
          (hluc.symm.trans ((Nat.modEq_zero_iff_dvd).2 key))
      obtain ⟨r, hr⟩ := ih (i / p) hmlt hm1 hdesc
      exact ⟨r + 1, by rw [pow_succ, ← hr, Nat.mul_comm]; exact hpm.symm⟩
    · -- `0 < i % p`: the binomial at `j = i % p` is a unit mod `p`.
      exfalso
      have key := h (i % p) hd (lt_of_lt_of_le (Nat.mod_lt i hp.pos) hpi)
      have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := i) (k := i % p) (p := p)
      rw [Nat.mod_mod_of_dvd _ dvd_rfl, Nat.choose_self,
        Nat.div_eq_of_lt (Nat.mod_lt i hp.pos), Nat.choose_zero_right, mul_one] at hluc
      -- `p ∣ C(i, i % p)` and `C(i, i % p) ≡ 1 [MOD p]`.
      have h1 : (0 : ℕ) ≡ 1 [MOD p] :=
        ((Nat.modEq_zero_iff_dvd).2 key).symm.trans hluc
      have := (Nat.modEq_zero_iff_dvd).1 h1.symm
      exact absurd (Nat.le_of_dvd one_pos this) (by have := hp.two_le; omega)

section IsAdditive

variable {K : Type*} [Field K]

/-- A polynomial is *additive* when it takes sums to sums pointwise
(blueprint §8.3). Over an infinite field this pins down the coefficient
support: linear in characteristic zero, `p`-power monomials in
characteristic `p`.-/
def IsAdditive (P : Polynomial K) : Prop :=
  ∀ x y : K, P.eval (x + y) = P.eval x + P.eval y

/--
@isnad1 id=isadditi.0h1v.s5.01b43d147e3e from=translated src=- shape=a72970d9 vocab=1c578a91
-/
theorem isAdditive_zero : IsAdditive (0 : Polynomial K) := by
  intro x y
  simp

/--
@isnad1 id=isadditi.0h1v.s4.70c2cd0501f5 from=translated src=- shape=84bfdc15 vocab=e957e5e8
-/
theorem isAdditive_X : IsAdditive (X : Polynomial K) := by
  intro x y
  simp

/--
@isnad1 id=isadditi.2h3v.s6.1d1cf3dbe1ad from=translated src=- shape=1333e5f0 vocab=fe07c0ce
-/
theorem IsAdditive.add {P Q : Polynomial K} (hP : IsAdditive P)
    (hQ : IsAdditive Q) : IsAdditive (P + Q) := by
  intro x y
  simp only [eval_add, hP x y, hQ x y]
  ring

/--
@isnad1 id=isadditi.1h3v.s7.50a2ed105b9f from=translated src=- shape=c504e831 vocab=4722a4df
-/
theorem IsAdditive.C_mul {P : Polynomial K} (hP : IsAdditive P) (c : K) :
    IsAdditive (C c * P) := by
  intro x y
  simp only [eval_mul, eval_C, hP x y]
  ring

/--
@isnad1 id=isadditi.2h3v.s5.ef30df1240f3 from=translated src=- shape=026a30af vocab=0b456a20
-/
theorem IsAdditive.comp {P Q : Polynomial K} (hP : IsAdditive P)
    (hQ : IsAdditive Q) : IsAdditive (P.comp Q) := by
  intro x y
  simp only [eval_comp, hQ x y]
  exact hP _ _

/-- In characteristic `p`, the `p^n`-th power monomial is additive.
@isnad1 id=isadditi.0h3v.s6.00efb94879a4 from=translated src=- shape=2b6fa051 vocab=23015d8b
-/
theorem isAdditive_X_pow_expChar_pow (p : ℕ) [ExpChar K p] (n : ℕ) :
    IsAdditive ((X : Polynomial K) ^ p ^ n) := by
  intro x y
  simp only [eval_pow, eval_X]
  exact add_pow_expChar_pow x y p n

/--
@isnad1 id=eq.1h2v.s6.de3249f33232 from=translated src=- shape=54bf819d vocab=986b5406
-/
theorem IsAdditive.eval_zero {P : Polynomial K} (hP : IsAdditive P) :
    P.eval 0 = 0 := by
  have h := hP 0 0
  rw [add_zero] at h
  have h2 : P.eval 0 + P.eval 0 = P.eval 0 + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

/--
@isnad1 id=eq.1h2v.s5.a570828c8953 from=translated src=- shape=ef1d67c6 vocab=9f96d861
-/
theorem IsAdditive.coeff_zero {P : Polynomial K} (hP : IsAdditive P) :
    P.coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  exact hP.eval_zero

/-- The engine of the support classification: over an infinite field, an
additive polynomial has `C(i,j) · pᵢ = 0` for every intermediate `j`
(via Taylor expansion and Hasse derivatives).
@isnad1 id=eq.3h4v.s6.4c08d6beceb6 from=translated src=- shape=aa0d0859 vocab=2436dec4
-/
theorem IsAdditive.natCast_choose_mul_coeff [Infinite K] {P : Polynomial K}
    (hP : IsAdditive P) {i j : ℕ} (hj0 : j ≠ 0) (hji : j < i) :
    (i.choose j : K) * P.coeff i = 0 := by
  -- Taylor expansion: for every `c`, `P(X + c) = P + C (P.eval c)`.
  have h1 : ∀ c : K, taylor c P = P + C (P.eval c) := by
    intro c
    refine Polynomial.funext fun x ↦ ?_
    rw [taylor_eval]
    simp [hP x c]
  -- Hence the `j`-th Hasse derivative is the constant `P.coeff j`.
  have h2 : hasseDeriv j P = C (P.coeff j) := by
    refine Polynomial.funext fun c ↦ ?_
    have h3 := congrArg (fun Q ↦ Polynomial.coeff Q j) (h1 c)
    simp only [taylor_coeff, coeff_add, coeff_C, ite_eq_right hj0, add_zero] at h3
    rw [h3, eval_C]
  -- Compare coefficients at `i - j`.
  have h4 := congrArg (fun Q ↦ Polynomial.coeff Q (i - j)) h2
  simp only [hasseDeriv_coeff, coeff_C, ite_eq_right (Nat.sub_ne_zero_of_lt hji)] at h4
  rwa [Nat.sub_add_cancel hji.le] at h4

/-- Characteristic zero: additive polynomials are linear
(blueprint Lemma `subgroup-classification` (a), characteristic-zero case).-/
theorem IsAdditive.eq_C_mul_X [CharZero K] {P : Polynomial K}
    (hP : IsAdditive P) : P = C (P.coeff 1) * X := by
  haveI : Infinite K := Infinite.of_injective _ (Nat.cast_injective (R := K))
  ext i
  rcases i with - | i
  · simpa using hP.coeff_zero
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · -- `i + 1 ≥ 2`: use `j = 1`.
    have h := hP.natCast_choose_mul_coeff (i := i + 1) (j := 1) one_ne_zero (by omega)
    rw [Nat.choose_one_right] at h
    have hne : ((i + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have : P.coeff (i + 1) = 0 := by
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hne
      · exact h'
    rw [this, coeff_C_mul, coeff_X]
    rw [ite_eq_right (by omega : ¬(1 = i + 1)), mul_zero]

/-- Characteristic `p`: the support of an additive polynomial consists of
`p`-power exponents (blueprint Lemma `subgroup-classification` (a),
characteristic-`p` case, via Lucas' theorem).
@isnad1 id=eq.3h4v.s6.c4072b1ce470 from=translated src=- shape=1b758080 vocab=5694aae3
-/
theorem IsAdditive.coeff_eq_zero_of_ne_pow (p : ℕ) [CharP K p] (hp : p.Prime)
    [Infinite K] {P : Polynomial K} (hP : IsAdditive P) {i : ℕ}
    (hi : ∀ r : ℕ, i ≠ p ^ r) : P.coeff i = 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact hP.coeff_zero
  by_contra hne
  -- Every intermediate binomial must vanish in `K`, i.e. be divisible by `p`.
  have hdvd : ∀ j, 0 < j → j < i → p ∣ i.choose j := by
    intro j hj0 hji
    have h := hP.natCast_choose_mul_coeff (i := i) (j := j) hj0.ne' hji
    rcases mul_eq_zero.1 h with h' | h'
    · exact (CharP.cast_eq_zero_iff K p _).1 h'
    · exact absurd h' hne
  obtain ⟨r, hr⟩ := eq_pow_of_forall_dvd_choose p hp i hi0 hdvd
  exact hi r hr

end IsAdditive

section Simultaneous

variable {K : Type*} [Field K]

open Polynomial in
/-- If an additive polynomial is a single nonzero monomial, its exponent is a
`p`-power (blueprint Lemma 8.9, final normalization step).
@isnad1 id=ex.4h5v.s8.5a6d7156d606 from=translated src=- shape=983c64d9 vocab=e2d50638
-/
theorem IsAdditive.pow_exponent_of_monomial (p : ℕ) [CharP K p] (hp : p.Prime)
    [Infinite K] {P : Polynomial K} (hP : IsAdditive P) {l : K} {m : ℕ}
    (hl : l ≠ 0) (hPm : P = C l * X ^ m) : ∃ r, m = p ^ r := by
  by_contra hcon
  push_neg at hcon
  have hz := hP.coeff_eq_zero_of_ne_pow p hp (i := m) hcon
  rw [hPm, coeff_C_mul, coeff_X_pow, ite_eq_left rfl, mul_one] at hz
  exact hl hz

end Simultaneous

end

end AclGeom
