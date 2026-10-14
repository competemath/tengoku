/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku

/-!
# Poly Exp Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

noncomputable section

namespace CKN.Foundation.Heat

/-- For nonnegative `a` and `k : ℕ`, `a ^ k * exp(-a) ≤ k!`.
@isnad1 id=le.1h2v.s5.1aa17008fa12 from=translated src=- shape=c4aab589 vocab=0086b56c
-/
theorem exp_poly_bound {k : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    a ^ k * Real.exp (-a) ≤ (k.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp a ha k
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hmul : a ^ k ≤ Real.exp a * (k.factorial : ℝ) := (div_le_iff₀ hfac).mp h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos a)).2
  calc
    a ^ k ≤ Real.exp a * (k.factorial : ℝ) := hmul
    _ = (k.factorial : ℝ) * Real.exp a := by ring

/-- For nonnegative `a` and `n : ℕ`, `(1 + a)^n * exp(-a) ≤ 2^(n-1) * (1 + n!)`.
@isnad1 id=le.1h2v.s6.b690e2c7fda6 from=translated src=- shape=7f8f2592 vocab=b34db2c7
-/
theorem one_add_pow_exp_neg_le {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (1 + a) ^ n * Real.exp (-a) ≤ (2 : ℝ) ^ (n - 1) * (1 + (n.factorial : ℝ)) := by
  have hp := add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) ha n
  have h0 : Real.exp (-a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr ha
  have hn' := exp_poly_bound (k := n) ha
  have hsum : (1 + a ^ n) * Real.exp (-a) ≤ 1 + (n.factorial : ℝ) := by
    calc
      (1 + a ^ n) * Real.exp (-a) = Real.exp (-a) + a ^ n * Real.exp (-a) := by ring
      _ ≤ 1 + (n.factorial : ℝ) := add_le_add h0 hn'
  have hp' : (1 + a) ^ n ≤ 2 ^ (n - 1) * (1 + a ^ n) := by
    simpa only [one_pow] using hp
  calc
    (1 + a) ^ n * Real.exp (-a) ≤
        2 ^ (n - 1) * (1 + a ^ n) * Real.exp (-a) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_nonneg _)
    _ = 2 ^ (n - 1) * ((1 + a ^ n) * Real.exp (-a)) := by ring
    _ ≤ 2 ^ (n - 1) * (1 + (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

/-- For positive time `t`, the heat prefactor `(4πt)^(-3/2)` is bounded by `(√t)^(-3)`.
@isnad1 id=le.1h1v.s6.86102fbfe1ac from=translated src=- shape=f8e3ec34 vocab=464b95a6
-/
theorem heat_prefactor_le {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) ≤ (Real.sqrt t) ^ (-(3 : ℝ)) := by
  have hbase : t ≤ 4 * Real.pi * t := by
    have hpi : (1 : ℝ) ≤ 4 * Real.pi := by
      nlinarith only [Real.two_le_pi]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi ht.le
  have hpow : t ^ ((3 : ℝ) / 2) ≤ (4 * Real.pi * t) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow ht.le hbase (by positivity)
  have hsqrt : (Real.sqrt t) ^ (3 : ℕ) = t ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  calc
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) = ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ := by
      rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by positivity)]
    _ ≤ (t ^ ((3 : ℝ) / 2))⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
    _ = (Real.sqrt t) ^ (-(3 : ℝ)) := by
      rw [← hsqrt, Real.rpow_neg (by positivity)]
      exact congrArg Inv.inv (Real.rpow_natCast (Real.sqrt t) 3).symm

/-- For positive `z`, `z^(-3)` equals `(z^3)⁻¹`.
@isnad1 id=eq.1h1v.s5.ddb3ee816c4d from=translated src=- shape=577c1027 vocab=78ea50f5
-/
theorem heat_rpow_neg_three (z : ℝ) (hz : 0 < z) :
    z ^ (-(3 : ℝ)) = (z ^ (3 : ℕ))⁻¹ := by
  rw [Real.rpow_neg hz.le]
  exact congrArg Inv.inv (Real.rpow_natCast z 3)

end CKN.Foundation.Heat
