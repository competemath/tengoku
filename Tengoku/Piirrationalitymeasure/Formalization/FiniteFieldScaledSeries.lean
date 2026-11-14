import Tengoku.Piirrationalitymeasure.Formalization.ScaledLaurent
import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldLaurent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The integer-coefficient power series obtained after the `t = -5 + 10*x`
change of variable, with its characteristic-zero derivative coefficients
and characteristic-`p` Laurent coefficients identified explicitly.
-/

namespace PiIrrationality

noncomputable def scaledCoreInt (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1),
    (Polynomial.hasseDeriv i (scaledNumerator n)).eval 0 *
      ((5570 * n + (k - i)).choose (k - i) : ℤ)

/--
@isnad1 id=eq.0h2v.s7.54985bb5aed8 from=translated src=- shape=021c07ed vocab=3502ec3d
-/
theorem scaledCoreInt_cast (n k : ℕ) :
    (scaledCoreInt n k : ℝ) =
      normalizedDeriv k
        (fun x : ℝ => Polynomial.aeval x (scaledNumerator n) *
          (1 - x) ^ (-(5570 * n + 1 : ℕ) : ℤ)) 0 := by
  unfold scaledCoreInt
  rw [normalizedDeriv_mul
    ((scaledNumerator n).contDiff_aeval k).contDiffAt
    (by
      simp only [zpow_neg, zpow_natCast]
      exact ((contDiffAt_const.sub contDiffAt_id).pow _).inv (by norm_num))]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  rw [normalizedDeriv_one_sub_inv]
  have h := normalizedDeriv_int_polynomial i (scaledNumerator n) 0
  norm_num only [Int.cast_zero] at h
  rw [h]

noncomputable def finiteScaledSeries (n p : ℕ) [Fact p.Prime] :
    PowerSeries (ZMod p) :=
  PowerSeries.map (Int.castRingHom (ZMod p)) (Polynomial.toPowerSeries (scaledNumerator n)) *
    (PowerSeries.invOneSubPow (ZMod p) (5570 * n + 1)).val

/--
@isnad1 id=eq.0h3v.s8.bb87d431610d from=translated src=- shape=d65bff8d vocab=5ad9e3b5
-/
theorem finiteScaledSeries_coeff (n p k : ℕ) [Fact p.Prime] :
    (finiteScaledSeries n p).coeff k = (scaledCoreInt n k : ZMod p) := by
  unfold finiteScaledSeries scaledCoreInt
  rw [PowerSeries.coeff_mul]
  have hsum := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j : ℕ =>
      (PowerSeries.coeff i)
          (PowerSeries.map (Int.castRingHom (ZMod p))
            (Polynomial.toPowerSeries (scaledNumerator n))) *
        (PowerSeries.coeff j)
          (PowerSeries.invOneSubPow (ZMod p) (5570 * n + 1)).val) k
  rw [hsum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [PowerSeries.coeff_map,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  rw [Polynomial.coeff_coe]
  simp only [PowerSeries.coeff_mk]
  rw [Nat.choose_symm_add]
  have heval : (Polynomial.hasseDeriv i (scaledNumerator n)).eval 0 =
      (scaledNumerator n).coeff i := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simp [Polynomial.hasseDeriv_coeff]
  rw [heval]
  rfl

noncomputable def scaledCoeffInt (n k : ℕ) : ℤ :=
  (2 : ℤ) ^ (3716 * n - 1) * 5 ^ (2 * n) * scaledCoreInt n k

/--
@isnad1 id=eq.2h2v.s6.234ac69b82bc from=translated src=- shape=d5dca837 vocab=6c7a4948
-/
theorem scaledCoeffInt_eq_actual (n : ℕ) (hn : 1 ≤ n) (j : ℤ)
    (hj : j ≤ 5570 * (n : ℤ)) :
    (scaledCoeffInt n (5570 * (n : ℤ) - j).toNat : ℚ) =
      (10 : ℚ) ^ (-j) * laurentCoeffRat n j := by
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [laurentCoeffRat_cast]
  let k := (5570 * (n : ℤ) - j).toNat
  have hk : (k : ℤ) = 5570 * (n : ℤ) - j := Int.toNat_of_nonneg (by omega)
  have hf : (fun x : ℝ => regularized n (-5 + 10 * x)) =
      fun x : ℝ =>
        ((10 : ℝ) ^ (5570 * n) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n))) *
        (Polynomial.aeval x (scaledNumerator n) *
          (1 - x) ^ (-(5570 * n + 1 : ℕ) : ℤ)) := by
    funext x
    rw [regularized_scaled_variable n hn x]
    ring
  have hd := normalizedDeriv_affine k (regularized n) 10 (-5)
  rw [hf, normalizedDeriv_const_mul, ← scaledCoreInt_cast] at hd
  have h10 : (10 : ℝ) ^ (-j) = (10 : ℝ) ^ k / (10 : ℝ) ^ (5570 * n) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num : (10 : ℝ) ≠ 0)]
    congr 1
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    omega
  rw [laurentCoeff_eq_normalizedDeriv n j hj, h10]
  change (scaledCoeffInt n k : ℝ) =
    10 ^ k / 10 ^ (5570 * n) * normalizedDeriv k (regularized n) (-5)
  rw [div_mul_eq_mul_div, ← hd]
  unfold scaledCoeffInt
  push_cast
  field_simp

/--
@isnad1 id=eq.2h2v.s6.19b9012ab04c from=translated src=- shape=0f2e50e0 vocab=24dd7080
-/
theorem scaledCoeffInt_eq_num (n : ℕ) (hn : 1 ≤ n) (j : ℤ)
    (hj : j ≤ 5570 * (n : ℤ)) :
    scaledCoeffInt n (5570 * (n : ℤ) - j).toNat =
      ((10 : ℚ) ^ (-j) * laurentCoeffRat n j).num := by
  rw [← scaledCoeffInt_eq_actual n hn j hj, Rat.num_intCast]

/--
@isnad1 id=eq.1h1v.s8.0681c4760ebd from=translated src=- shape=56b6a6e9 vocab=35ae5b9f
-/
theorem scaledLaurent_constant_int (n : ℕ) (hn : 1 ≤ n) :
    (5 : ℤ) * 5 ^ (2 * 1857 * n) * 20 ^ (2 * (3714 * n)) =
      10 ^ (2 * (5570 * n) + 1) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) := by
  have h := (div_eq_iff (by positivity : (10 : ℝ) ^ (5570 * n + 1) ≠ 0)).1
    (scaledLaurent_constant n hn)
  have h' : (5 : ℝ) * 5 ^ (2 * 1857 * n) * 20 ^ (2 * (3714 * n)) =
      10 ^ (2 * (5570 * n) + 1) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) := by
    rw [h, show 2 * (5570 * n) + 1 = 5570 * n + (5570 * n + 1) by omega, pow_add]
    ring
  exact_mod_cast h'

/--
@isnad1 id=eq.0h3v.s12.168c32e49491 from=translated src=- shape=9379fce9 vocab=7ec70061
-/
theorem finiteScaledSeries_rescale_laurent (n p : ℕ) [Fact p.Prime] (a : ZMod p) :
    HahnSeries.ofPowerSeries ℤ (ZMod p)
        (PowerSeries.rescale a (finiteScaledSeries n p)) =
      let x : LaurentSeries (ZMod p) := HahnSeries.single 1 a
      (2 * x - 1) ^ (2 * 1857 * n) *
        (5 * x ^ 2 - 4 * x + 1) ^ (3714 * n) *
        (5 * x ^ 2 - 6 * x + 2) ^ (3714 * n) *
        ((1 - x) ^ (5570 * n + 1))⁻¹ := by
  let f : PowerSeries (ZMod p) →+* LaurentSeries (ZMod p) :=
    (HahnSeries.ofPowerSeries ℤ (ZMod p)).comp (PowerSeries.rescale a)
  have hX : f PowerSeries.X = HahnSeries.single 1 a := by
    dsimp [f]
    rw [PowerSeries.rescale_X, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X]
    simp [HahnSeries.C_apply, HahnSeries.single_mul_single]
  have hinv : f (PowerSeries.invOneSubPow (ZMod p) (5570 * n + 1)).val =
      ((1 - HahnSeries.single 1 a) ^ (5570 * n + 1))⁻¹ := by
    have h := congrArg f (PowerSeries.invOneSubPow (ZMod p) (5570 * n + 1)).val_inv
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, map_mul, map_pow,
      map_sub, map_one, hX] at h
    exact eq_inv_of_mul_eq_one_left h
  change f (finiteScaledSeries n p) = _
  unfold finiteScaledSeries
  rw [map_mul, hinv]
  congr 1
  change f (PowerSeries.map (Int.castRingHom (ZMod p))
    (Polynomial.coeToPowerSeries.ringHom (scaledNumerator n))) = _
  simp only [scaledNumerator, Polynomial.coe_X,
    map_mul, map_pow, map_sub, map_add, map_one, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply,
    PowerSeries.map_X, hX]

/--
@isnad1 id=eq.1h3v.s10.d8f63f712ef1 from=translated src=- shape=2e7a4234 vocab=dde3f2c6
-/
theorem scaled_numerator_identity {K : Type*} [CommRing K]
    (n : ℕ) (hn : 1 ≤ n) (x : K) :
    5 * (5 * (2 * x - 1)) ^ (2 * 1857 * n) *
        ((5 * (2 * x - 1)) ^ 4 + 6 * (5 * (2 * x - 1)) ^ 2 + 25) ^ (3714 * n) =
      10 ^ (2 * (5570 * n) + 1) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) *
        ((2 * x - 1) ^ (2 * 1857 * n) *
          (5 * x ^ 2 - 4 * x + 1) ^ (3714 * n) *
          (5 * x ^ 2 - 6 * x + 2) ^ (3714 * n)) := by
  have hc := congrArg (Int.castRingHom K) (scaledLaurent_constant_int n hn)
  simp only [map_mul, map_pow, map_ofNat] at hc
  rw [show (5 * (2 * x - 1)) ^ 4 + 6 * (5 * (2 * x - 1)) ^ 2 + 25 =
      (20 * (5 * x ^ 2 - 4 * x + 1)) * (20 * (5 * x ^ 2 - 6 * x + 2)) by ring]
  simp only [mul_pow]
  calc
    _ = (5 * 5 ^ (2 * 1857 * n) * 20 ^ (2 * (3714 * n))) *
        ((2 * x - 1) ^ (2 * 1857 * n) *
          (5 * x ^ 2 - 4 * x + 1) ^ (3714 * n) *
          (5 * x ^ 2 - 6 * x + 2) ^ (3714 * n)) := by
      rw [show 2 * (3714 * n) = 3714 * n + 3714 * n by omega, pow_add]
      ring
    _ = _ := by rw [hc]

/--
@isnad1 id=ne.1h1v.s6.4b6503f27da6 from=translated src=- shape=2207af8f vocab=029ffb2b
-/
theorem zmod_ten_ne_zero {p : ℕ} [Fact p.Prime] (hp : 5 < p) :
    (10 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 * 5 := (ZMod.natCast_eq_zero_iff 10 p).1 h
  rcases (Fact.out : p.Prime).dvd_mul.1 hd with h2 | h5
  · have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have := Nat.le_of_dvd (by norm_num) h5
    omega

/--
@isnad1 id=eq.2h2v.s10.761a3439eea7 from=translated src=- shape=34f789ae vocab=0f81e811
-/
theorem finiteField_local_scaled_series (n p : ℕ) [Fact p.Prime]
    (hn : 1 ≤ n) (hp : 5 < p) :
    localLaurent (-5 : ZMod p) (finiteFieldRational n p) =
      HahnSeries.single (-(5570 * n + 1 : ℕ) : ℤ)
        ((10 : ZMod p) ^ (5570 * n) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n))) *
      HahnSeries.ofPowerSeries ℤ (ZMod p)
        (PowerSeries.rescale (10 : ZMod p)⁻¹ (finiteScaledSeries n p)) := by
  let X : LaurentSeries (ZMod p) := HahnSeries.single 1 1
  let x : LaurentSeries (ZMod p) := HahnSeries.single 1 (10 : ZMod p)⁻¹
  have h10 : (10 : LaurentSeries (ZMod p)) ≠ 0 := by
    have h := (algebraMap (ZMod p) (LaurentSeries (ZMod p))).injective.ne
      (zmod_ten_ne_zero hp)
    simpa only [map_ofNat, map_zero] using h
  have hx : X = 10 * x := by
    dsimp [X, x]
    have h10C : (10 : LaurentSeries (ZMod p)) = HahnSeries.single 0 (10 : ZMod p) := by
      simpa using (map_ofNat (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p)) 10).symm
    rw [h10C, HahnSeries.single_mul_single, zero_add, mul_inv_cancel₀ (zmod_ten_ne_zero hp)]
  have ht : X - 5 = 5 * (2 * x - 1) := by rw [hx]; ring
  have hden : 25 - (X - 5) ^ 2 = X * (10 * (1 - x)) := by rw [hx]; ring
  have hnum := scaled_numerator_identity n hn x
  rw [← ht] at hnum
  rw [finiteScaledSeries_rescale_laurent]
  unfold finiteFieldRational
  rw [localLaurent_div]
  simp only [localPolynomial, deletionNumerator, deletionDenominator, map_mul, map_pow,
    map_add, map_sub, Polynomial.aeval_X, map_ofNat, map_neg,
    ← sub_eq_add_neg, show 2 * (1857 * n) = 2 * 1857 * n by omega]
  change (5 * (X - 5) ^ (2 * 1857 * n) *
      ((X - 5) ^ 4 + 6 * (X - 5) ^ 2 + 25) ^ (3714 * n)) /
      (25 - (X - 5) ^ 2) ^ (5570 * n + 1) = _
  rw [hnum, hden]
  have hsingle : HahnSeries.single (-(5570 * n + 1 : ℕ) : ℤ)
      ((10 : ZMod p) ^ (5570 * n) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n))) =
      (10 : LaurentSeries (ZMod p)) ^ (5570 * n) *
        (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) * (X ^ (5570 * n + 1))⁻¹ := by
    rw [← zpow_natCast X (5570 * n + 1), ← zpow_neg]
    dsimp [X]
    rw [← RatFunc.single_zpow]
    have hC : (10 : LaurentSeries (ZMod p)) ^ (5570 * n) *
        (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) =
        HahnSeries.C ((10 : ZMod p) ^ (5570 * n) *
          (2 ^ (3716 * n - 1) * 5 ^ (2 * n))) := by
      simp only [map_mul, map_pow, map_ofNat]
    rw [hC, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hsingle]
  simp only [mul_pow, div_eq_mul_inv, mul_inv]
  rw [show 2 * (5570 * n) + 1 = 5570 * n + (5570 * n + 1) by omega, pow_add]
  have hcancel : (10 : LaurentSeries (ZMod p)) ^ (5570 * n + 1) *
      (10 ^ (5570 * n + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ h10)
  calc
    _ = (10 ^ (5570 * n + 1) * (10 ^ (5570 * n + 1))⁻¹) *
        (10 ^ (5570 * n) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) *
        (X ^ (5570 * n + 1))⁻¹ *
        ((2 * x - 1) ^ (2 * 1857 * n) *
          (5 * x ^ 2 - 4 * x + 1) ^ (3714 * n) *
          (5 * x ^ 2 - 6 * x + 2) ^ (3714 * n) *
          ((1 - x) ^ (5570 * n + 1))⁻¹)) := by ring
    _ = _ := by rw [hcancel, one_mul]

/--
@isnad1 id=eq.3h3v.s9.2ae22b737949 from=translated src=- shape=580e3bfa vocab=0e2f40f6
-/
theorem finiteField_local_coeff_eq_scaled_num (n p : ℕ) [Fact p.Prime]
    (hn : 1 ≤ n) (hp : 5 < p) (j : ℤ) (hj : j ≤ 5570 * (n : ℤ)) :
    (localLaurent (-5 : ZMod p) (finiteFieldRational n p)).coeff (-j - 1) =
      (((10 : ℚ) ^ (-j) * laurentCoeffRat n j).num : ZMod p) *
        (10 : ZMod p) ^ j := by
  let k := (5570 * (n : ℤ) - j).toNat
  have hk : (k : ℤ) = 5570 * (n : ℤ) - j := Int.toNat_of_nonneg (by omega)
  rw [finiteField_local_scaled_series n p hn hp, HahnSeries.coeff_single_mul]
  have hindex : -j - 1 - (-(5570 * n + 1 : ℕ) : ℤ) = (k : ℤ) := by omega
  rw [hindex, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_rescale,
    finiteScaledSeries_coeff, ← scaledCoeffInt_eq_num n hn j hj]
  change (10 : ZMod p) ^ (5570 * n) * (2 ^ (3716 * n - 1) * 5 ^ (2 * n)) *
      ((10⁻¹) ^ k * (scaledCoreInt n k : ZMod p)) =
        (scaledCoeffInt n k : ZMod p) * 10 ^ j
  have hpow : (10 : ZMod p) ^ (5570 * n) * (10⁻¹) ^ k = (10 : ZMod p) ^ j := by
    rw [inv_pow, ← zpow_natCast (10 : ZMod p) (5570 * n),
      ← zpow_natCast (10 : ZMod p) k, ← zpow_neg,
      ← zpow_add₀ (zmod_ten_ne_zero hp)]
    congr 1
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    omega
  unfold scaledCoeffInt
  push_cast
  calc
    _ = ((10 : ZMod p) ^ (5570 * n) * (10⁻¹) ^ k) *
        (2 ^ (3716 * n - 1) * 5 ^ (2 * n) * (scaledCoreInt n k : ZMod p)) := by ring
    _ = _ := by rw [hpow]; ring

end PiIrrationality
