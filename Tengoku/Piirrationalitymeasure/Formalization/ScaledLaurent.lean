import Tengoku.Piirrationalitymeasure.Formalization.LaurentRationality
import Tengoku.Piirrationalitymeasure.Formalization.ReducedLcmIntegrality
import Tengoku.Piirrationalitymeasure.Formalization.Valuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Integral scaled Laurent coefficients via the change of variable `t = -5 + 10*x`.
The transformed numerator is an integer polynomial. Its normalized derivatives
and those of the remaining inverse power have integer values at zero.
-/

namespace PiIrrationality

/--
@isnad1 id=eq.0h3v.s6.bae6686c494a from=translated src=- shape=df1e6ad5 vocab=1fa6845b
-/
theorem iteratedDeriv_comp_mul_unrestricted (k : ℕ) (f : ℝ → ℝ) (a : ℝ) :
    iteratedDeriv k (fun x => f (a * x)) =
      fun x => a ^ k * iteratedDeriv k f (a * x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ]
      simp only [smul_eq_mul, pow_succ]
      ring

/--
@isnad1 id=eq.0h4v.s6.5826eca3a6f8 from=translated src=- shape=d27d5632 vocab=39f21ac4
-/
theorem normalizedDeriv_affine (k : ℕ) (f : ℝ → ℝ) (a b : ℝ) :
    normalizedDeriv k (fun x => f (b + a * x)) 0 =
      a ^ k * normalizedDeriv k f b := by
  unfold normalizedDeriv
  rw [iteratedDeriv_comp_mul_unrestricted k (fun x => f (b + x)) a,
    iteratedDeriv_comp_const_add]
  simp only [mul_zero, add_zero]
  ring

/--
@isnad1 id=eq.0h3v.s7.d590f7eb1e80 from=translated src=- shape=3446428d vocab=da4f674b
-/
theorem normalizedDeriv_int_polynomial (k : ℕ) (P : Polynomial ℤ) (x : ℤ) :
    normalizedDeriv k (fun t : ℝ => Polynomial.aeval t P) (x : ℝ) =
      (((Polynomial.hasseDeriv k P).eval x : ℤ) : ℝ) := by
  have hder : iteratedDeriv k (fun t : ℝ => Polynomial.aeval t P) =
      fun t : ℝ => Polynomial.aeval t ((Polynomial.derivative^[k]) P) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        simp only [Polynomial.deriv_aeval, Function.iterate_succ_apply']
  unfold normalizedDeriv
  have hfactor : (Polynomial.derivative^[k]) P =
      k.factorial • Polynomial.hasseDeriv k P :=
    (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℤ) (k := k)) P).symm
  rw [hder]
  dsimp only
  rw [hfactor, map_nsmul]
  have heval := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
    (A := ℝ) x (Polynomial.hasseDeriv k P)
  change Polynomial.aeval (x : ℝ) (Polynomial.hasseDeriv k P) = _ at heval
  rw [heval]
  simp [nsmul_eq_mul, Nat.factorial_ne_zero]

/--
@isnad1 id=eq.0h2v.s6.29a98f899077 from=translated src=- shape=5b998145 vocab=bc95f878
-/
theorem normalizedDeriv_one_sub_inv (M k : ℕ) :
    normalizedDeriv k (fun x : ℝ => (1 - x) ^ (-(M + 1 : ℕ) : ℤ)) 0 =
      ((M + k).choose k : ℝ) := by
  have hprod : (-1 : ℝ) ^ k *
      (∏ i ∈ Finset.range k, (-(M + 1 : ℝ) - i)) =
      ((M + 1).ascFactorial k : ℝ) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.prod_range_succ, pow_succ, Nat.ascFactorial_succ]
        push_cast
        rw [show (-1 : ℝ) ^ k * -1 *
          ((∏ i ∈ Finset.range k, (-(M + 1 : ℝ) - i)) * (-(M + 1) - k)) =
          ((-1 : ℝ) ^ k * (∏ i ∈ Finset.range k, (-(M + 1 : ℝ) - i))) *
            (M + 1 + k) by ring, ih]
        ring
  unfold normalizedDeriv
  rw [iteratedDeriv_comp_const_sub k (fun x : ℝ => x ^ (-(M + 1 : ℕ) : ℤ)) 1]
  simp only [sub_zero, smul_eq_mul, iteratedDeriv_eq_iterate, iter_deriv_zpow,
    one_zpow, mul_one, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Nat.cast_add, Nat.cast_one]
  rw [hprod, Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

noncomputable def scaledNumerator (n : ℕ) : Polynomial ℤ :=
  (2 * Polynomial.X - 1) ^ (2 * 1857 * n) *
    (5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) ^ (3714 * n) *
    (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2) ^ (3714 * n)

/--
@isnad1 id=eq.0h2v.s8.24440f2cfae3 from=translated src=- shape=d2bbe539 vocab=2c571520
-/
theorem scaledNumerator_aeval (n : ℕ) (x : ℝ) :
    Polynomial.aeval x (scaledNumerator n) =
      (2 * x - 1) ^ (2 * 1857 * n) *
        (5 * x ^ 2 - 4 * x + 1) ^ (3714 * n) *
        (5 * x ^ 2 - 6 * x + 2) ^ (3714 * n) := by
  simp [scaledNumerator, map_ofNat]

/--
@isnad1 id=eq.1h1v.s8.4babbea700db from=translated src=- shape=ee5f9e4f vocab=5df71cf7
-/
theorem scaledLaurent_constant (n : ℕ) (hn : 1 ≤ n) :
    (5 : ℝ) * 5 ^ (2 * 1857 * n) * 20 ^ (2 * (3714 * n)) /
        10 ^ (5570 * n + 1) =
      10 ^ (5570 * n) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) := by
  have h2 : 4 * (3714 * n) = (5570 * n + 1) + 5570 * n + (3716 * n - 1) := by
    omega
  have h5 : 1 + 2 * 1857 * n + 2 * (3714 * n) =
      (5570 * n + 1) + 5570 * n + 2 * n := by omega
  apply (div_eq_iff (by positivity : (10 : ℝ) ^ (5570 * n + 1) ≠ 0)).2
  calc
    (5 : ℝ) * 5 ^ (2 * 1857 * n) * 20 ^ (2 * (3714 * n)) =
        2 ^ (4 * (3714 * n)) * 5 ^ (1 + 2 * 1857 * n + 2 * (3714 * n)) := by
      rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num, mul_pow, ← pow_mul]
      simp only [pow_add, pow_one]
      ring
    _ = _ := by
      rw [h2, h5]
      simp only [pow_add, show (10 : ℝ) = 2 * 5 by norm_num, mul_pow]
      ring

/--
@isnad1 id=eq.1h2v.s8.c1bc30b16a16 from=translated src=- shape=5ca2f094 vocab=5725cc35
-/
theorem regularized_scaled_variable (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    regularized n (-5 + 10 * x) =
      (10 : ℝ) ^ (5570 * n) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) *
        Polynomial.aeval x (scaledNumerator n) *
        (1 - x) ^ (-(5570 * n + 1 : ℕ) : ℤ) := by
  rw [regularized_six_factor_shape, scaledNumerator_aeval]
  rw [show (-5 : ℝ) + 10 * x = 5 * (2 * x - 1) by ring,
    show ((5 : ℝ) * (2 * x - 1) + 1) ^ 2 + 4 =
      20 * (5 * x ^ 2 - 4 * x + 1) by ring,
    show ((5 : ℝ) * (2 * x - 1) - 1) ^ 2 + 4 =
      20 * (5 * x ^ 2 - 6 * x + 2) by ring,
    show (5 : ℝ) - 5 * (2 * x - 1) = 10 * (1 - x) by ring]
  simp only [mul_pow, div_eq_mul_inv, mul_inv, zpow_neg, zpow_natCast]
  have hc := scaledLaurent_constant n hn
  rw [show 2 * (3714 * n) = 3714 * n + 3714 * n by omega, pow_add] at hc
  simp only [div_eq_mul_inv] at hc
  calc
    _ = (5 * 5 ^ (2 * 1857 * n) *
        (20 ^ (3714 * n) * 20 ^ (3714 * n)) * (10 ^ (5570 * n + 1))⁻¹) *
        ((2 * x - 1) ^ (2 * 1857 * n) *
          (5 * x ^ 2 - 4 * x + 1) ^ (3714 * n) *
          (5 * x ^ 2 - 6 * x + 2) ^ (3714 * n)) *
        ((1 - x) ^ (5570 * n + 1))⁻¹ := by ring
    _ = _ := by rw [hc]

/--
@isnad1 id=ex.0h2v.s7.2de08136ffba from=translated src=- shape=864eda44 vocab=fce946be
-/
theorem normalizedDeriv_scaled_core_is_integer (n k : ℕ) :
    ∃ z : ℤ, normalizedDeriv k
      (fun x : ℝ => Polynomial.aeval x (scaledNumerator n) *
        (1 - x) ^ (-(5570 * n + 1 : ℕ) : ℤ)) 0 = (z : ℝ) := by
  have hpoly : ContDiffAt ℝ k
      (fun x : ℝ => Polynomial.aeval x (scaledNumerator n)) 0 :=
    ((scaledNumerator n).contDiff_aeval k).contDiffAt
  have hinv : ContDiffAt ℝ k
      (fun x : ℝ => (1 - x) ^ (-(5570 * n + 1 : ℕ) : ℤ)) 0 :=
    by
      simp only [zpow_neg, zpow_natCast]
      exact ((contDiffAt_const.sub contDiffAt_id).pow _).inv (by norm_num)
  rw [normalizedDeriv_mul hpoly hinv]
  refine ⟨∑ i ∈ Finset.range (k + 1),
    (Polynomial.hasseDeriv i (scaledNumerator n)).eval 0 *
      ((5570 * n + (k - i)).choose (k - i) : ℤ), ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  rw [normalizedDeriv_one_sub_inv]
  have h := normalizedDeriv_int_polynomial i (scaledNumerator n) 0
  norm_num only [Int.cast_zero] at h
  rw [h]

/--
@isnad1 id=eq.0h4v.s5.0bc733f84ef4 from=translated src=- shape=348de7cd vocab=d378e583
-/
theorem normalizedDeriv_const_mul (k : ℕ) (a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    normalizedDeriv k (fun y => a * f y) x = a * normalizedDeriv k f x := by
  unfold normalizedDeriv
  rw [iteratedDeriv_const_mul_field]
  ring

/--
@isnad1 id=ex.1h2v.s7.789c3c5ae531 from=translated src=- shape=0a8d82e1 vocab=5239e570
-/
theorem scaled_laurentCoeff_eq_integer_mul (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    ∃ z : ℤ, (10 : ℝ) ^ (-j) * laurentCoeff n j =
      (2 : ℝ) ^ (3716 * n - 1) * 5 ^ (2 * n) * (z : ℝ) := by
  by_cases hj : j ≤ 5570 * (n : ℤ)
  · let k := (5570 * (n : ℤ) - j).toNat
    have hk : (k : ℤ) = 5570 * (n : ℤ) - j := Int.toNat_of_nonneg (by omega)
    obtain ⟨z, hz⟩ := normalizedDeriv_scaled_core_is_integer n k
    refine ⟨z, ?_⟩
    have hf : (fun x : ℝ => regularized n (-5 + 10 * x)) =
        fun x : ℝ =>
          ((10 : ℝ) ^ (5570 * n) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n))) *
          (Polynomial.aeval x (scaledNumerator n) *
            (1 - x) ^ (-(5570 * n + 1 : ℕ) : ℤ)) := by
      funext x
      rw [regularized_scaled_variable n hn x]
      ring
    have hd := normalizedDeriv_affine k (regularized n) 10 (-5)
    rw [hf, normalizedDeriv_const_mul, hz] at hd
    have h10 : (10 : ℝ) ^ (-j) = (10 : ℝ) ^ k / (10 : ℝ) ^ (5570 * n) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num : (10 : ℝ) ≠ 0)]
      congr 1
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      omega
    rw [laurentCoeff_eq_normalizedDeriv n j hj, h10]
    change 10 ^ k / 10 ^ (5570 * n) * normalizedDeriv k (regularized n) (-5) = _
    rw [div_mul_eq_mul_div, ← hd]
    field_simp
  · exact ⟨0, by simp [laurentCoeff, hj]⟩

/--
@isnad1 id=ex.1h2v.s7.0b63deecb723 from=translated src=- shape=0a8d82e1 vocab=b7970b42
-/
theorem scaled_laurentCoeffRat_eq_integer_mul (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    ∃ z : ℤ, (10 : ℚ) ^ (-j) * laurentCoeffRat n j =
      (2 : ℚ) ^ (3716 * n - 1) * 5 ^ (2 * n) * (z : ℚ) := by
  obtain ⟨z, hz⟩ := scaled_laurentCoeff_eq_integer_mul n hn j
  refine ⟨z, ?_⟩
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [laurentCoeffRat_cast]
  exact hz

/--
@isnad1 id=ex.1h2v.s5.194f1a68b9d9 from=translated src=- shape=d3e4284c vocab=73fec59d
-/
theorem scaled_laurentCoeffRat_is_integer (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    ∃ z : ℤ, (10 : ℚ) ^ (-j) * laurentCoeffRat n j = (z : ℚ) := by
  obtain ⟨z, hz⟩ := scaled_laurentCoeffRat_eq_integer_mul n hn j
  refine ⟨(2 : ℤ) ^ (3716 * n - 1) * 5 ^ (2 * n) * z, ?_⟩
  push_cast
  exact hz

/--
@isnad1 id=le.1h3v.s6.20d7ce97b93b from=translated src=- shape=8e6ad4f6 vocab=b5177bcf
-/
theorem padicValRatTop_ge_of_integer_power_factor
    (p k : ℕ) [hp : Fact p.Prime] (q : ℚ)
    (h : ∃ z : ℤ, q = (p : ℚ) ^ k * (z : ℚ)) :
    ((k : ℤ) : WithTop ℤ) ≤ padicValRatTop p q := by
  obtain ⟨z, rfl⟩ := h
  by_cases hz : z = 0
  · simp [hz, padicValRatTop]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [padicValRatTop, ite_eq_right (mul_ne_zero (pow_ne_zero _ hp0) hz0)]
  simp only [WithTop.coe_le_coe]
  rw [padicValRat.mul (pow_ne_zero _ hp0) hz0, padicValRat.pow,
    padicValRat.self hp.out.one_lt, mul_one, padicValRat.of_int]
  exact le_add_of_nonneg_right (by exact_mod_cast (Nat.zero_le (padicValInt p z)))

/--
@isnad1 id=and.1h2v.s7.5fadf8b03d99 from=translated src=- shape=3275f858 vocab=1bb38a4f
-/
theorem scaled_laurentCoeffRat_valuations (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    ((3716 * (n : ℤ) - 1 : ℤ) : WithTop ℤ) ≤
        padicValRatTop 2 ((10 : ℚ) ^ (-j) * laurentCoeffRat n j) ∧
      ((2 * (n : ℤ) : ℤ) : WithTop ℤ) ≤
        padicValRatTop 5 ((10 : ℚ) ^ (-j) * laurentCoeffRat n j) := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := scaled_laurentCoeffRat_eq_integer_mul n hn j
  have h2 := padicValRatTop_ge_of_integer_power_factor 2 (3716 * n - 1)
    ((10 : ℚ) ^ (-j) * laurentCoeffRat n j)
    ⟨(5 : ℤ) ^ (2 * n) * z, by push_cast; rw [hz]; ring⟩
  have h5 := padicValRatTop_ge_of_integer_power_factor 5 (2 * n)
    ((10 : ℚ) ^ (-j) * laurentCoeffRat n j)
    ⟨(2 : ℤ) ^ (3716 * n - 1) * z, by push_cast; rw [hz]; ring⟩
  have he : ((3716 * n - 1 : ℕ) : ℤ) = 3716 * (n : ℤ) - 1 := by omega
  rw [he] at h2
  exact ⟨h2, by simpa only [Nat.cast_mul, Nat.cast_ofNat] using h5⟩

/--
@isnad1 id=and.2h1v.s8.6b363f62b95f from=translated src=- shape=dbced562 vocab=e1bc3226
-/
theorem reducedLcm_actual_laurent_integrality_of_local_divisibility
    (n : ℕ) (hn : 0 < n)
    (hlocal : ∀ j : ℤ, -(7430 * (n : ℤ)) + 1 ≤ j → j ≤ 5570 * (n : ℤ) →
      ∀ p : ℕ, removablePrime n p → (p : ℤ) ∣ j →
        (p : ℤ) ∣ ((10 : ℚ) ^ (-j) * laurentCoeffRat n j).num) :
    (∃ L : ℤ, reducedLcm n = (L : ℚ)) ∧
      (∀ j : ℤ, -(7430 * (n : ℤ)) + 1 ≤ j → j ≤ 5570 * (n : ℤ) → j ≠ 0 →
        ∃ z : ℤ, reducedLcm n * ((10 : ℚ) ^ (-j) * laurentCoeffRat n j) /
          (j : ℚ) = (z : ℚ)) ∧
      (∃ z : ℤ, laurentCoeffRat n 0 / (Phi n : ℚ) = (z : ℚ)) := by
  exact reducedLcm_laurent_integrality_of_coefficients n hn (laurentCoeffRat n)
    (fun j _ _ => scaled_laurentCoeffRat_is_integer n hn j) hlocal

end PiIrrationality
