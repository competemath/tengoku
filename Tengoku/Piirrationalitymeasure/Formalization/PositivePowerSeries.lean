import Tengoku.Piirrationalitymeasure.Formalization.CoefficientConvergence
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientCircle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Positive powers with arbitrary numerator exponents and a positive pole order. -/

namespace PiIrrationality.PositivePower

open PowerSeries

noncomputable def numeratorNat (u v : ℕ) : PowerSeries ℕ :=
  (1 + X) ^ u * PSeriesNat ^ v

noncomputable def numerator (u v : ℕ) : PowerSeries ℚ :=
  PowerSeries.map (Nat.castRingHom ℚ) (numeratorNat u v)

noncomputable def series (u v d : ℕ) : PowerSeries ℚ :=
  numerator u v * (invOneSubPow ℚ d).val

noncomputable def realValue (u v d : ℕ) (x : ℝ) : ℝ :=
  (1 + x) ^ u * PReal x ^ v / (1 - x) ^ d

noncomputable def complexValue (u v d : ℕ) (z : ℂ) : ℂ :=
  (1 + z) ^ u * PComplex z ^ v / (1 - z) ^ d

/--
@isnad1 id=eq.0h2v.s6.e7206e3dd031 from=translated src=- shape=5e2795fc vocab=6a01e5e2
-/
theorem numerator_eq (u v : ℕ) : numerator u v = (1 + X) ^ u * PSeries ^ v := by
  simp only [numerator, numeratorNat, PSeriesNat, PSeries, map_mul, map_pow,
    map_add, map_one, map_ofNat, PowerSeries.map_X]

/--
@isnad1 id=le.0h4v.s6.50df3f996d17 from=translated src=- shape=53afee87 vocab=480c8474
-/
theorem numerator_pow_coeff_nonneg (u v n k : ℕ) :
    0 ≤ coeff k (numerator u v ^ n) := by
  rw [numerator, ← map_pow, coeff_map]
  exact Nat.cast_nonneg _

/--
@isnad1 id=eq.0h2v.s5.1e4622fc8643 from=translated src=- shape=c0fe21b5 vocab=fdf0b9cf
-/
theorem numerator_constantCoeff (u v : ℕ) :
    constantCoeff (numerator u v) = (2 : ℚ) ^ v := by
  simp [numerator_eq, PSeries, map_ofNat]

/--
@isnad1 id=eq.0h4v.s6.396dda776af6 from=translated src=- shape=b1b071e0 vocab=4e549d7b
-/
theorem series_pow_eq (u v d n : ℕ) :
    series u v d ^ n = numerator u v ^ n * (invOneSubPow ℚ (d * n)).val := by
  rw [series, mul_pow, invOneSubPow_pow]

/--
@isnad1 id=lt.2h5v.s7.0dddf65c0cae from=translated src=- shape=b7a915fb vocab=eaff4393
-/
theorem series_pow_coeff_pos (u v : ℕ) {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (k : ℕ) :
    0 < coeff k (series u v d ^ n) := by
  rw [series_pow_eq, coeff_mul]
  apply Finset.sum_pos'
  · intro p hp
    exact mul_nonneg (numerator_pow_coeff_nonneg u v n p.1)
      (inversePower_coeff_pos (Nat.mul_pos hd hn) p.2).le
  · refine ⟨(0, k), by simp, ?_⟩
    have h0 : 0 < coeff 0 (numerator u v ^ n) := by
      rw [coeff_zero_eq_constantCoeff, map_pow, numerator_constantCoeff]
      positivity
    exact mul_pos h0 (inversePower_coeff_pos (Nat.mul_pos hd hn) k)

/--
@isnad1 id=le.1h5v.s7.c181fa382518 from=translated src=- shape=4feba181 vocab=32f14a7a
-/
theorem series_pow_coeff_nonneg (u v : ℕ) {d : ℕ} (hd : 0 < d) (n k : ℕ) :
    0 ≤ coeff k (series u v d ^ n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [pow_zero, coeff_one]
    split <;> norm_num
  · exact (series_pow_coeff_pos u v hd hn k).le

/--
@isnad1 id=lt.1h5v.s7.f3c160596aa2 from=translated src=- shape=647f9bba vocab=046b159a
-/
theorem series_diagonal_coeff_pos (u v : ℕ) {d : ℕ} (hd : 0 < d) (q n : ℕ) :
    0 < coeff (q * n) (series u v d ^ n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact series_pow_coeff_pos u v hd hn _

/--
@isnad1 id=eq.0h3v.s7.4100cce91f50 from=translated src=- shape=0c41b730 vocab=96f8b236
-/
theorem series_clearing_identity (u v d : ℕ) :
    series u v d * (1 - X) ^ d = (1 + X) ^ u * PSeries ^ v := by
  rw [series, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow ℚ d,
    (invOneSubPow ℚ d).val_inv, mul_one, numerator_eq]

/--
@isnad1 id=eq.0h0v.s4.3f85d80b2cdb from=translated src=- shape=b26754d2 vocab=7baea6b9
-/
theorem series_candidate : series 3714 3714 7430 = Sseries := rfl

/--
@isnad1 id=lt.2h4v.s5.4f3fc6035ee7 from=translated src=- shape=007e3682 vocab=109cd087
-/
theorem realValue_pos (u v d : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 < realValue u v d x := by
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  have hP := PReal_strictPositive x hx0
  unfold realValue
  positivity

section Sums

variable {K : Type*} [RCLike K]

/--
@isnad1 id=hassum.0h4v.s9.b19d0fd0ae81 from=translated src=- shape=623dc3ea vocab=1067b11d
-/
theorem numerator_hasSum (u v : ℕ) (z : K) :
    HasSum (fun k => (↑(coeff k (numerator u v)) : K) * z ^ k)
      ((1 + z) ^ u * (2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3 + 2 * z ^ 4) ^ v) := by
  rw [numerator_eq]
  have h1 : HasSum (fun k => (↑(coeff k (1 : PowerSeries ℚ)) : K) * z ^ k) 1 := by
    simpa only [Nat.cast_one] using ratSeries_hasSum_natCast 1 z
  exact ratSeries_hasSum_mul
    (ratSeries_hasSum_pow (ratSeries_hasSum_add h1 (ratSeries_hasSum_X z)) u)
    (ratSeries_hasSum_pow (PSeries_hasSum z) v)

/--
@isnad1 id=hassum.2h5v.s9.f1d0b1350926 from=translated src=- shape=bd9d7fe5 vocab=defb2e93
-/
theorem series_hasSum (u v : ℕ) {d : ℕ} (hd : 0 < d) {z : K} (hz : ‖z‖ < 1) :
    HasSum (fun k => (↑(coeff k (series u v d)) : K) * z ^ k)
      ((1 + z) ^ u * (2 + 6 * z + 9 * z ^ 2 + 6 * z ^ 3 + 2 * z ^ 4) ^ v /
        (1 - z) ^ d) := by
  simpa only [series, div_eq_mul_inv, one_mul] using
    ratSeries_hasSum_mul (numerator_hasSum u v z) (inversePower_hasSum hz hd)

end Sums

/--
@isnad1 id=hassum.3h4v.s7.7ea43731645a from=translated src=- shape=928a5f5d vocab=7073c401
-/
theorem series_hasSum_real (u v : ℕ) {d : ℕ} (hd : 0 < d)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k => (↑(coeff k (series u v d)) : ℝ) * x ^ k) (realValue u v d x) := by
  have hx : ‖x‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  exact series_hasSum u v hd hx

/--
@isnad1 id=hassum.3h5v.s7.98189b1956f4 from=translated src=- shape=e87e864f vocab=7073c401
-/
theorem series_pow_hasSum_real (u v : ℕ) {d : ℕ} (hd : 0 < d)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    HasSum (fun k => (↑(coeff k (series u v d ^ n)) : ℝ) * x ^ k)
      (realValue u v d x ^ n) :=
  ratSeries_hasSum_pow (series_hasSum_real u v hd hx0 hx1) n

/--
@isnad1 id=eq.0h4v.s4.3264002402f5 from=translated src=- shape=e5a02007 vocab=de5dd805
-/
theorem complexValue_ofReal (u v d : ℕ) (x : ℝ) :
    complexValue u v d (x : ℂ) = (realValue u v d x : ℂ) := by
  unfold complexValue realValue PComplex PReal
  push_cast
  rfl

/--
@isnad1 id=lt.3h4v.s5.7ce0b008cdab from=translated src=- shape=c9668e6f vocab=c053b57c
-/
theorem complexValue_norm_strict (u v : ℕ) {d : ℕ} (hd : 0 < d)
    {z : ℂ} (hz1 : ‖z‖ < 1) (hz : z ≠ (‖z‖ : ℂ)) :
    ‖complexValue u v d z‖ < realValue u v d ‖z‖ := by
  have hplus : ‖1 + z‖ ≤ 1 + ‖z‖ := by simpa using norm_add_le (1 : ℂ) z
  have hden := one_sub_complex_norm_strict hz1 hz
  have hdenpos : 0 < 1 - ‖z‖ := by linarith
  have hP := PReal_strictPositive ‖z‖ (norm_nonneg z)
  have hnum : 0 < (1 + ‖z‖) ^ u * PReal ‖z‖ ^ v := by positivity
  have hpow : (1 - ‖z‖) ^ d < ‖1 - z‖ ^ d :=
    pow_lt_pow_left₀ hden hdenpos.le hd.ne'
  unfold complexValue realValue
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow]
  calc
    _ ≤ (1 + ‖z‖) ^ u * PReal ‖z‖ ^ v / ‖1 - z‖ ^ d := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hplus u)
        (pow_le_pow_left₀ (norm_nonneg _) (PComplex_norm_le z) v)
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ < _ := div_lt_div_of_pos_left hnum (pow_pos hdenpos _) hpow

/--
@isnad1 id=continuo.1h4v.s5.e6ab1c0aabcd from=translated src=- shape=bb0bc4ed vocab=9786c326
-/
theorem complexValue_continuousAt (u v d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ContinuousAt (complexValue u v d) z := by
  unfold complexValue PComplex
  fun_prop (disch := exact pow_ne_zero _ (one_sub_complex_ne_zero hz))

end PiIrrationality.PositivePower
