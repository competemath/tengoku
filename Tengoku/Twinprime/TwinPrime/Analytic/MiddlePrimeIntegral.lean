import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The rational integral in the middle-prime sieve bound

The integrand is treated as an actual rational function.  Its primitive,
smoothness, and uniform bounds on compact subintervals of `(0,a)` are
elementary and do not use any prime-distribution hypothesis.
-/

noncomputable section

open Set MeasureTheory

namespace TwinPrime.Analytic

def middlePrimeIntegrand (a t : ℝ) : ℝ := (1 - t) / (t * (a - t))

def middlePrimeIntegrandDerivative (a t : ℝ) : ℝ :=
  -(1 / a) / t ^ 2 + ((1 - a) / a) / (a - t) ^ 2

def middlePrimeIntegralPrimitive (a t : ℝ) : ℝ :=
  (1 / a) * Real.log t - ((1 - a) / a) * Real.log (a - t)

/--
@isnad1 id=eq.3h2v.s6.229a6c2bbd7a from=translated src=- shape=c26c3489 vocab=7e9b1764
-/
theorem middlePrimeIntegrand_eq_partial_fractions (a t : ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) (hat : a - t ≠ 0) :
    middlePrimeIntegrand a t = (1 / a) / t + ((1 - a) / a) / (a - t) := by
  unfold middlePrimeIntegrand
  field_simp
  ring

/--
@isnad1 id=contdiff.0h1v.s5.5c950304c338 from=translated src=- shape=d9dc5480 vocab=05d9cc67
-/
theorem contDiffOn_middlePrimeIntegrand (a : ℝ) :
    ContDiffOn ℝ ⊤ (middlePrimeIntegrand a) (Ioo 0 a) := by
  exact (contDiffOn_const.sub contDiffOn_id).div
    (contDiffOn_id.mul (contDiffOn_const.sub contDiffOn_id))
    (fun t ht => mul_ne_zero (ne_of_gt ht.1) (ne_of_gt (sub_pos.mpr ht.2)))

/--
@isnad1 id=hasderiv.3h2v.s6.4d411e9b58f8 from=translated src=- shape=70bb4bae vocab=1bcb9fdb
-/
theorem hasDerivAt_middlePrimeIntegrand (a t : ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) (hat : a - t ≠ 0) :
    HasDerivAt (middlePrimeIntegrand a) (middlePrimeIntegrandDerivative a t) t := by
  have h := ((hasDerivAt_id t).const_sub 1).div
    ((hasDerivAt_id t).mul ((hasDerivAt_id t).const_sub a)) (mul_ne_zero ht hat)
  convert! h using 1
  unfold middlePrimeIntegrandDerivative
  dsimp
  field_simp
  ring

/--
@isnad1 id=eq.3h2v.s6.d4069404e202 from=translated src=- shape=0b4e7760 vocab=27007add
-/
theorem deriv_middlePrimeIntegrand (a t : ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) (hat : a - t ≠ 0) :
    deriv (middlePrimeIntegrand a) t = middlePrimeIntegrandDerivative a t :=
  (hasDerivAt_middlePrimeIntegrand a t ha ht hat).deriv

/--
@isnad1 id=hasderiv.3h2v.s6.5ea711463288 from=translated src=- shape=70bb4bae vocab=2148d050
-/
theorem hasDerivAt_middlePrimeIntegralPrimitive (a t : ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) (hat : a - t ≠ 0) :
    HasDerivAt (middlePrimeIntegralPrimitive a) (middlePrimeIntegrand a t) t := by
  have h := ((Real.hasDerivAt_log ht).const_mul (1 / a)).sub
    ((((hasDerivAt_id t).const_sub a).log hat).const_mul ((1 - a) / a))
  convert! h using 1
  unfold middlePrimeIntegrand
  dsimp
  field_simp
  ring

/--
@isnad1 id=continuo.2h3v.s5.01cab17bd1ba from=translated src=- shape=ea816a7a vocab=40133307
-/
theorem continuousOn_middlePrimeIntegrand (a u v : ℝ)
    (hu : 0 < u) (hva : v < a) :
    ContinuousOn (middlePrimeIntegrand a) (Icc u v) := by
  exact (contDiffOn_middlePrimeIntegrand a).continuousOn.mono
    (fun _ ht => ⟨lt_of_lt_of_le hu ht.1, lt_of_le_of_lt ht.2 hva⟩)

/--
@isnad1 id=interval.3h3v.s5.208713a7dd26 from=translated src=- shape=3bc0656b vocab=1a408095
-/
theorem intervalIntegrable_middlePrimeIntegrand (a u v : ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hva : v < a) :
    IntervalIntegrable (middlePrimeIntegrand a) volume u v :=
  (continuousOn_middlePrimeIntegrand a u v hu hva).intervalIntegrable_of_Icc huv

/--
@isnad1 id=eq.3h3v.s7.12b09dc60bfe from=translated src=- shape=17d5b375 vocab=91f698cb
-/
theorem integral_middlePrimeIntegrand (a u v : ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hva : v < a) :
    (∫ t in u..v, middlePrimeIntegrand a t) =
      (1 / a) * Real.log (v / u) +
        ((1 - a) / a) * Real.log ((a - u) / (a - v)) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have ha : 0 < a := lt_trans hv hva
  have hau : 0 < a - u := sub_pos.mpr (lt_of_le_of_lt huv hva)
  have hav : 0 < a - v := sub_pos.mpr hva
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := middlePrimeIntegralPrimitive a) (f' := middlePrimeIntegrand a)
    (a := u) (b := v) (fun t ht => by
      rw [uIcc_of_le huv] at ht
      exact hasDerivAt_middlePrimeIntegralPrimitive a t ha.ne'
        (ne_of_gt (lt_of_lt_of_le hu ht.1))
        (ne_of_gt (sub_pos.mpr (lt_of_le_of_lt ht.2 hva))))
    (intervalIntegrable_middlePrimeIntegrand a u v hu huv hva)
  rw [hcalc, middlePrimeIntegralPrimitive, middlePrimeIntegralPrimitive,
    Real.log_div hv.ne' hu.ne', Real.log_div hau.ne' hav.ne']
  ring

/--
@isnad1 id=le.3h2v.s5.ca92eab77b1e from=translated src=- shape=96016c98 vocab=df03485f
-/
theorem middlePrimeIntegrand_nonneg (a t : ℝ)
    (ht : 0 < t) (hta : t < a) (ha : a ≤ 1) :
    0 ≤ middlePrimeIntegrand a t := by
  exact div_nonneg (by linarith) (mul_nonneg ht.le (sub_nonneg.mpr hta.le))

/--
@isnad1 id=le.4h4v.s6.2793443c0ec6 from=translated src=- shape=dbc90dbd vocab=c99fc20d
-/
theorem abs_middlePrimeIntegrand_le (a u v t : ℝ)
    (hu : 0 < u) (hva : v < a) (ha : a ≤ 1) (ht : t ∈ Icc u v) :
    |middlePrimeIntegrand a t| ≤ 1 / (u * (a - v)) := by
  have ht0 : 0 < t := lt_of_lt_of_le hu ht.1
  have hta : t < a := lt_of_le_of_lt ht.2 hva
  have hav : 0 < a - v := sub_pos.mpr hva
  have hden : u * (a - v) ≤ t * (a - t) :=
    mul_le_mul ht.1 (sub_le_sub_left ht.2 a) hav.le ht0.le
  rw [abs_of_nonneg (middlePrimeIntegrand_nonneg a t ht0 hta ha)]
  calc
    middlePrimeIntegrand a t ≤ 1 / (t * (a - t)) := by
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ 1 / (u * (a - v)) := one_div_le_one_div_of_le (mul_pos hu hav) hden

/--
@isnad1 id=le.4h4v.s7.88dee711da09 from=translated src=- shape=8849352c vocab=3903049d
-/
theorem abs_middlePrimeIntegrandDerivative_le (a u v t : ℝ)
    (hu : 0 < u) (hva : v < a) (ha : a ≤ 1) (ht : t ∈ Icc u v) :
    |middlePrimeIntegrandDerivative a t| ≤
      1 / (a * u ^ 2) + (1 - a) / (a * (a - v) ^ 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le hu ht.1
  have hta : t < a := lt_of_le_of_lt ht.2 hva
  have ha0 : 0 < a := lt_trans ht0 hta
  have hav : 0 < a - v := sub_pos.mpr hva
  have hsq1 : u ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hu.le ht.1 2
  have hsq2 : (a - v) ^ 2 ≤ (a - t) ^ 2 :=
    pow_le_pow_left₀ hav.le (sub_le_sub_left ht.2 a) 2
  have h1 : 0 ≤ (1 / a) / t ^ 2 := by positivity
  have h2 : 0 ≤ ((1 - a) / a) / (a - t) ^ 2 := by positivity
  calc
    |middlePrimeIntegrandDerivative a t| ≤
        (1 / a) / t ^ 2 + ((1 - a) / a) / (a - t) ^ 2 := by
      unfold middlePrimeIntegrandDerivative
      rw [neg_div]
      calc
        _ ≤ |-(1 / a / t ^ 2)| + |(1 - a) / a / (a - t) ^ 2| := abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_of_nonneg h1, abs_of_nonneg h2]
    _ ≤ (1 / a) / u ^ 2 + ((1 - a) / a) / (a - v) ^ 2 := by
      exact add_le_add
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq1)
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq2)
    _ = _ := by rw [div_div, div_div]

/--
@isnad1 id=le.4h4v.s7.32bdbd84bc90 from=translated src=- shape=dcce74be vocab=291b1abf
-/
theorem abs_deriv_middlePrimeIntegrand_le (a u v t : ℝ)
    (hu : 0 < u) (hva : v < a) (ha : a ≤ 1) (ht : t ∈ Icc u v) :
    |deriv (middlePrimeIntegrand a) t| ≤
      1 / (a * u ^ 2) + (1 - a) / (a * (a - v) ^ 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le hu ht.1
  have hta : t < a := lt_of_le_of_lt ht.2 hva
  rw [deriv_middlePrimeIntegrand a t (ne_of_gt (lt_trans ht0 hta)) ht0.ne'
    (ne_of_gt (sub_pos.mpr hta))]
  exact abs_middlePrimeIntegrandDerivative_le a u v t hu hva ha ht

/--
@isnad1 id=continuo.2h3v.s6.e402891bfe1f from=translated src=- shape=a32bf529 vocab=a5728000
-/
theorem continuousOn_deriv_middlePrimeIntegrand (a u v : ℝ)
    (hu : 0 < u) (hva : v < a) :
    ContinuousOn (deriv (middlePrimeIntegrand a)) (Icc u v) := by
  have h : ContinuousOn (middlePrimeIntegrandDerivative a) (Icc u v) := by
    apply ContinuousOn.add
    · exact continuousOn_const.div (continuousOn_id.pow 2)
        (fun t ht => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hu ht.1)))
    · exact continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
        (fun t ht => pow_ne_zero 2 (ne_of_gt (sub_pos.mpr (lt_of_le_of_lt ht.2 hva))))
  apply h.congr
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le hu ht.1
  have hta : t < a := lt_of_le_of_lt ht.2 hva
  exact deriv_middlePrimeIntegrand a t (ne_of_gt (lt_trans ht0 hta)) ht0.ne'
    (ne_of_gt (sub_pos.mpr hta))

end TwinPrime.Analytic
