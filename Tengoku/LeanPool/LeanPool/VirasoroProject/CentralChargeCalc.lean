/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Tengoku

/-!
# Central charge calculations for Sugawara constructions

This file contains the crucial auxiliary calculations leading to the values of the central charge
in various Sugawara constructions. The calculations make use of "discrete integration" on `ℤ`.

## Main definitions

* `zPrimitive`: A "discrete integral function" to a given function `f : ℤ → R`. The defining
  properties of `F = zPrimitive f` are `F(0) = 0` and `F(n+1) - F(n) = f(n)`.
* `zMonomialF`: The `d`th discrete monomial function is defined by `d`-fold discrete integration
  starting from the function `1`. (The continuum analogue is the monomial `1/d! • x^d`.)

## Main statements

* `zMonomialF_eq` The `d`th discrete monomial function is given by
  `n ↦ 1/d! • ∏ j (0 ≤ j < d), (n - j)`
* `bosonic_sugawara_cc_calc`: For any `n ∈ ℤ`, we have
   `zPrimitive (fun l ↦ (l : R) * (n - l)) n = (n^3 - n) / 6`.
* `bosonic_sugawara_cc_calc_nonneg`: For any `n ∈ ℕ`, we have
   `∑ l (0 ≤ l < n), (l : ℚ) * (n - l) = (n^3 - n) / 6`.

## TODO

* TODO: Add variants of the calculation for fermionic Sugawara constructions etc.

## Tags

central charge, Sugawara construction

-/

@[expose] public section

namespace VirasoroProject

section central_charge_calculation

open Finset

/-- A discrete integral of a function on `ℤ`. -/
def zPrimitive {R : Type*} [AddCommGroup R] (f : ℤ → R) (n : ℤ) : R :=
  if 0 ≤ n then ∑ j ∈ range (Int.toNat n), f j else -(∑ j ∈ range (Int.natAbs n), f (-j-1))

/--
@isnad1 id=eq.0h2v.s5.9786244d7d90 from=translated src=- shape=1e2e7eb4 vocab=ce467808
-/
@[simp] lemma zPrimitive_zero {R : Type*} [AddCommGroup R] (f : ℤ → R) :
    zPrimitive f 0 = 0 :=
  rfl

/--
@isnad1 id=eq.1h3v.s5.3d1255dd9af8 from=translated src=- shape=01377d48 vocab=2102f8e8
-/
@[simp] lemma zPrimitive_apply_of_nonneg {R : Type*} [AddCommGroup R] (f : ℤ → R)
    {n : ℤ} (hn : 0 ≤ n) :
    zPrimitive f n = ∑ j ∈ range (Int.toNat n), f j := by
  simp [zPrimitive, hn]

/--
@isnad1 id=eq.1h3v.s6.8fc7e89faf49 from=translated src=- shape=0c2a5320 vocab=f2c84336
-/
@[simp] lemma zPrimitive_apply_of_nonpos {R : Type*} [AddCommGroup R] (f : ℤ → R)
    {n : ℤ} (hn : n ≤ 0) :
    zPrimitive f n = -(∑ j ∈ range (Int.natAbs n), f (-j-1)) := by
  by_cases hn' : n = 0
  · simp [hn']
  · grind [zPrimitive]

/--
@isnad1 id=eq.0h3v.s5.cb0961a5ac9d from=translated src=- shape=95f3fc05 vocab=d5afeac0
-/
@[simp] lemma zPrimitive_succ {R : Type*} [AddCommGroup R] (f : ℤ → R) (n : ℤ) :
    zPrimitive f (n + 1) = zPrimitive f n + f n := by
  by_cases hn : 0 ≤ n
  · simp [zPrimitive, hn, Int.le_add_one hn, Int.toNat_add hn zero_le_one, sum_range_succ]
  · simp only [not_le] at hn
    have n_natAbs : n.natAbs = (n+1).natAbs + 1 := by grind
    simp only [zPrimitive_apply_of_nonpos _ hn, zPrimitive_apply_of_nonpos _ hn.le, n_natAbs,
               sum_range_succ, Int.natCast_natAbs, neg_add_rev]
    simp only [add_comm (-(f _)), add_assoc, left_eq_add]
    simp [show -|n + 1| - 1 = n by rw [abs_of_nonpos hn, neg_neg]; ring]

lemma eq_zPrimitive_of_eq_zero_of_forall_eq_add {R : Type*} [AddCommGroup R] {f F : ℤ → R}
    (h0 : F 0 = 0) (h1 : ∀ n, F (n + 1) = F n + f n) :
    F = zPrimitive f := by
  have obsP : ∀ (n : ℕ), F n = zPrimitive f n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => aesop
  have obsM : ∀ (n : ℕ), F (-n) = zPrimitive f (-n) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      have keyF := h1 (-(n + 1))
      have keyP := zPrimitive_succ f (-(n + 1))
      grind
  ext m
  by_cases hm : 0 ≤ m
  · rw [(Int.toNat_of_nonneg hm).symm]
    exact obsP m.toNat
  · have hm' : m < 0 := Int.lt_of_not_ge hm
    rw [show m = -m.natAbs from Int.eq_neg_comm.mp (by simpa [hm'] using hm'.le)]
    exact obsM m.natAbs

/--
@isnad1 id=eq.0h3v.s6.3b2a28bc9e12 from=translated src=- shape=bb737001 vocab=d5afeac0
-/
lemma zPrimitive_add {R : Type*} [AddCommGroup R] (f g : ℤ → R) :
    zPrimitive (f + g) = zPrimitive f + zPrimitive g  := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp only [Pi.add_apply, zPrimitive_succ]
    ac_rfl

/--
@isnad1 id=eq.0h4v.s7.f744dc008924 from=translated src=- shape=4f999ec9 vocab=1ebc870e
-/
lemma zPrimitive_smul {R S : Type*} [AddCommGroup R] [DistribSMul S R]
    (c : S) (f : ℤ → R) :
    zPrimitive (c • f) = c • (zPrimitive f) := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm <;> simp

/--
@isnad1 id=eq.0h3v.s6.a87b3df77a3c from=translated src=- shape=bb737001 vocab=c2cf9941
-/
lemma zPrimitive_sub {R : Type*} [AddCommGroup R] (f g : ℤ → R) :
    zPrimitive (f - g) = zPrimitive f - zPrimitive g  := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp only [Pi.sub_apply, zPrimitive_succ, sub_eq_add_neg, neg_add_rev, ← add_assoc]
    ac_rfl

/--
@isnad1 id=eq.0h3v.s5.bfce44fd8fed from=translated src=- shape=b065eb01 vocab=ebbb8a2b
-/
lemma zPrimitive_mul_left {R : Type*} [Ring R] (c : R) (f : ℤ → R) :
    zPrimitive (fun n ↦ c * f n) = fun n ↦ c * zPrimitive f n := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp [mul_add]

/--
@isnad1 id=eq.0h3v.s5.44773454b458 from=translated src=- shape=db938939 vocab=ebbb8a2b
-/
lemma zPrimitive_mul_right {R : Type*} [Ring R] (c : R) (f : ℤ → R) :
    zPrimitive (fun n ↦ f n * c) = fun n ↦ zPrimitive f n * c := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp [add_mul]

/-- A discrete monomial function of degree `d`, obtained recursively by starting from the
unit function `1` and taking the discrete primitive `d` times.
(Note: The resulting normalization is such that this monomial approximately `x ↦ 1/d! * x^d`.) -/
def zMonomialF (R : Type*) [AddCommGroup R] [One R] (d : ℕ) : ℤ → R := match d with
  | 0 => fun _ ↦ 1
  | d + 1 => zPrimitive (zMonomialF R d)

/--
@isnad1 id=eq.0h2v.s7.59953c425dd6 from=translated src=- shape=f3b8a584 vocab=0c808716
-/
lemma zMonomialF_eq (R : Type*) [Field R] [CharZero R] (d : ℕ) :
    (zMonomialF R d) = (fun (n : ℤ) ↦ ((∏ j ∈ range d, (n - j : R)) / (Nat.factorial d : R))) := by
  induction d with
  | zero =>
    funext n
    simp [zMonomialF]
  | succ d ihd =>
    rw [zMonomialF, Eq.comm]
    apply eq_zPrimitive_of_eq_zero_of_forall_eq_add
    · simpa using Or.inl <| prod_eq_zero_iff.mpr ⟨0, by simp, by simp⟩
    · intro n
      have aux₀ : (d.factorial : R) ≠ 0 := by simp [Nat.factorial_ne_zero _]
      have aux₁: ((d+1).factorial : R) ≠ 0 := by simp [Nat.factorial_ne_zero _]
      have aux' : ((d+1) : R) ≠ 0 := by norm_cast
      calc  (∏ j ∈ range (d + 1), ((↑(n + 1) : R) - j)) / (d + 1).factorial
        _ = (∏ x ∈ range (d + 1), (n + 1 - x)) / (d + 1).factorial                      := by simp
        _ = (∏ j ∈ range (d + 1), (n - j)) / ((d + 1) * d.factorial)
            + (∏ j ∈ range d, (n - j : R)) / d.factorial                                := ?_
        _ = (∏ j ∈ range (d + 1), (↑n - ↑j)) / ↑(d + 1).factorial + zMonomialF R d n    := ?_
      · simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        simp only [prod_range_succ (fun a ↦ (n : R) - a), Int.cast_prod, Int.cast_sub, Int.cast_add,
                   Int.cast_one, Int.cast_natCast]
        field_simp
        simp [sub_add, prod_range_succ']
      · simp [ihd, mul_comm _ (d.factorial : R), Nat.factorial_succ, mul_comm]

/--
@isnad1 id=eq.0h2v.s5.82b6fc03f94f from=translated src=- shape=af01e58b vocab=2d3b8a17
-/
lemma zMonomialF_zero_eq (R : Type*) [Field R] (n : ℤ) :
    zMonomialF R 0 n = 1 := by
  simp [zMonomialF]

/--
@isnad1 id=eq.0h2v.s5.59d2454e0544 from=translated src=- shape=482911d5 vocab=691e1765
-/
lemma zMonomialF_one_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 1 n = n := by
  simp [zMonomialF_eq]

/--
@isnad1 id=eq.0h2v.s7.9b127235ce06 from=translated src=- shape=b2663fbb vocab=5a87a30c
-/
lemma zMonomialF_two_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 2 n = n * (n - 1) / 2 := by
  simp [zMonomialF_eq, prod_range_succ]

/--
@isnad1 id=eq.0h2v.s7.6c29a5c7d1dc from=translated src=- shape=c7afa90c vocab=5a87a30c
-/
lemma zMonomialF_three_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 3 n = n * (n - 1) * (n - 2) / 6 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 3 = 6 from rfl]

/--
@isnad1 id=eq.0h2v.s8.a709926d8dde from=translated src=- shape=9a241229 vocab=5a87a30c
-/
lemma zMonomialF_four_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 4 n = n * (n - 1) * (n - 2) * (n - 3) / 24 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 4 = 24 from rfl]

/--
@isnad1 id=eq.0h2v.s8.b586102c74f8 from=translated src=- shape=d8419a51 vocab=5a87a30c
-/
lemma zMonomialF_five_eq (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 5 n = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 5 = 120 from rfl]

/--
@isnad1 id=eq.1h3v.s6.933f591c7d3e from=translated src=- shape=02ae443c vocab=41826c8a
-/
lemma zMonomialF_apply_eq_zero_of_of_nonneg_lt (R : Type*) [Field R] [CharZero R]
    (d : ℕ) {n : ℕ} (n_lt : n < d) :
    zMonomialF R d n = 0 := by
  simpa only [zMonomialF_eq R d, Int.cast_natCast, div_eq_zero_iff, Nat.cast_eq_zero]
    using Or.inl <| prod_eq_zero_iff.mpr ⟨n, ⟨mem_range.mpr n_lt, by simp⟩⟩

/--
@isnad1 id=eq.0h2v.s7.35ef6f7e4424 from=translated src=- shape=da3a3031 vocab=0f027c13
-/
lemma bosonic_sugawara_cc_calc (R : Type*) [Field R] [CharZero R] (n : ℤ) :
    zPrimitive (fun l ↦ (l : R) * (n - l)) n = (n^3 - n) / 6 := by
  have obs : (n^3 - n) / 6 = (n - 1 : R) * zMonomialF R 2 n - 2 * zMonomialF R 3 n := by
    rw [zMonomialF_two_eq, zMonomialF_three_eq]
    field_simp
    ring
  have key : (zPrimitive fun l ↦ (n - 1 : R) * l) - (zPrimitive fun l ↦ 2 * zMonomialF R 2 l)
              = zPrimitive ((fun (l : ℤ) ↦ (l : R) * (n - l))) := by
    rw [← zPrimitive_sub]
    apply congr_arg zPrimitive
    ext l
    simp [zMonomialF_two_eq]
    ring
  simp_rw [obs, ← key, zPrimitive_mul_left]
  dsimp
  congr
  ext m
  rw [zMonomialF_one_eq]

/--
@isnad1 id=eq.0h1v.s6.4bbba03023f3 from=translated src=- shape=2d04fcc1 vocab=f0540e80
-/
lemma bosonic_sugawara_cc_calc_nonneg (n : ℕ) :
    ∑ l ∈ range n, (l : ℚ) * (n - l) = (n^3 - n) / 6 := by
  have key := bosonic_sugawara_cc_calc ℚ n
  simp_all

end central_charge_calculation

end VirasoroProject -- namespace
