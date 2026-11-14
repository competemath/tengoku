import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveThreshold
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocalReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform logarithmic weights for the middle-prime sieve

Both floor errors are retained in the actual threshold. A fixed bound on
their logarithmic error gives a uniform O(1/log X) comparison with the
ideal weight on every active outer interval.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

def middlePrimeLogCoordinate (X q : ℕ) : ℝ := Real.log q / Real.log X

def middlePrimeActualWeight (a : ℝ) (X q : ℕ) : ℝ :=
  Real.log ((2 * X : ℝ) / q) / Real.log (middlePrimeSieveThreshold a X q : ℝ)

def middlePrimeIdealWeight (a : ℝ) (X q : ℕ) : ℝ :=
  2 * (1 - middlePrimeLogCoordinate X q) / (a - middlePrimeLogCoordinate X q)

/--
@isnad1 id=and.2h3v.s6.94aab0b53e4c from=translated src=- shape=b6677f51 vocab=47ad6ad4
-/
theorem middlePrimeLogCoordinate_bounds (v : ℝ) (X q : ℕ) (hX : 2 ≤ X)
    (hq : q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)) :
    1 / 5 < middlePrimeLogCoordinate X q ∧ middlePrimeLogCoordinate X q ≤ v := by
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hL : 0 < Real.log X := Real.log_pos hx
  have hq0 : (0 : ℝ) < q := by
    exact_mod_cast lt_of_lt_of_le (primaryCutoff_pos (by omega)) (mem_Ioc.mp hq).1.le
  have hroot : (X : ℝ) ^ (1 / 5 : ℝ) < q := by
    apply (Nat.lt_floor_add_one ((X : ℝ) ^ (1 / 5 : ℝ))).trans_le
    exact_mod_cast (mem_Ioc.mp hq).1
  have hupper : (q : ℝ) ≤ (X : ℝ) ^ v :=
    (show (q : ℝ) ≤ middlePrimePowerCutoff v X by exact_mod_cast (mem_Ioc.mp hq).2).trans
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) v))
  constructor
  · apply (lt_div_iff₀ hL).mpr
    have h := Real.log_lt_log (Real.rpow_pos_of_pos (by linarith) _) hroot
    simpa only [Real.log_rpow (by linarith : (0 : ℝ) < X)] using h
  · apply (div_le_iff₀ hL).mpr
    have h := Real.log_le_log hq0 hupper
    simpa only [Real.log_rpow (by linarith : (0 : ℝ) < X)] using h

/-- The ideal weight is uniformly positive and bounded on the active interval.
@isnad1 id=and.4h4v.s6.79ce29130e93 from=translated src=- shape=90ebc427 vocab=50ea58ef
-/
theorem middlePrimeIdealWeight_bounds (a v : ℝ) (hva : v < a) (ha : a < 1)
    (X q : ℕ) (hX : 2 ≤ X)
    (hq : q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X)) :
    2 ≤ middlePrimeIdealWeight a X q ∧ middlePrimeIdealWeight a X q ≤ 2 / (a - v) := by
  obtain ⟨ht0, htv⟩ := middlePrimeLogCoordinate_bounds v X q hX hq
  have hs : 0 < a - middlePrimeLogCoordinate X q := by linarith
  have hδ : 0 < a - v := sub_pos.mpr hva
  constructor
  · apply (le_div_iff₀ hs).mpr
    linarith
  · calc
      _ ≤ 2 / (a - middlePrimeLogCoordinate X q) := by
        apply div_le_div_of_nonneg_right _ hs.le
        linarith
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hδ (by linarith)

private theorem ratio_perturbation_le (L z t a δ c : ℝ)
    (hL0 : 0 < L) (hδ : 0 < δ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : δ ≤ a - t) (hs1 : a - t ≤ 1) (hc : |c| ≤ 1)
    (he : |z - (a - t) * L / 2| ≤ 2) (hL : 8 / δ ≤ L) :
    |(L * (1 - t) + c) / z - 2 * (1 - t) / (a - t)| ≤ 20 / (δ ^ 2 * L) := by
  have hδL : 8 ≤ δ * L := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hL
  have hs0 : 0 < a - t := hδ.trans_le hs
  have he' := (abs_le.mp he).1
  have hsL := mul_le_mul_of_nonneg_right hs hL0.le
  have hzlow : δ * L / 4 ≤ z := by linarith
  have hz : 0 < z := (by positivity : (0 : ℝ) < δ * L / 4).trans_le hzlow
  have hden : δ ^ 2 * L / 4 ≤ z * (a - t) := by
    have h := mul_le_mul hzlow hs (by positivity : 0 ≤ δ) hz.le
    nlinarith only [h]
  have heq : (L * (1 - t) + c) / z - 2 * (1 - t) / (a - t) =
      (c * (a - t) - 2 * (1 - t) * (z - (a - t) * L / 2)) / (z * (a - t)) := by
    field_simp
    ring
  have hnum : |c * (a - t) - 2 * (1 - t) * (z - (a - t) * L / 2)| ≤ 5 := by
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_pos hs0, abs_of_nonneg (by linarith : 0 ≤ 2 * (1 - t))]
    have hfirst := mul_le_mul_of_nonneg_right hc hs0.le
    have hsecond := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ 2 * (1 - t))
    nlinarith
  rw [heq, abs_div, abs_of_pos (mul_pos hz hs0)]
  calc
    _ ≤ 5 / (z * (a - t)) := div_le_div_of_nonneg_right hnum (mul_nonneg hz.le hs0.le)
    _ ≤ 5 / (δ ^ 2 * L / 4) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = _ := by field_simp; norm_num

/-- Combining the full threshold rounding with the modulus floor gives
a bounded logarithmic error before normalization by log X.
@isnad1 id=le.4h3v.s7.fd90152e2e19 from=translated src=- shape=4445772e vocab=35a41419
-/
theorem abs_log_middlePrimeSieveThreshold_sub_power_half_le_two (a : ℝ) (X q : ℕ)
    (hX : 2 ≤ X) (hpow : 4 ≤ (X : ℝ) ^ a) (hq : 1 ≤ q)
    (hqD : q ≤ middlePrimePowerCutoff a X) :
    |Real.log (middlePrimeSieveThreshold a X q : ℝ) -
      (a * Real.log X - Real.log q) / 2| ≤ 2 := by
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hfloor := abs_log_sub_log_natFloor_le hpow
  rw [Real.log_rpow hx] at hfloor
  have hfloor2 : |Real.log (middlePrimePowerCutoff a X : ℝ) - a * Real.log X| ≤ 2 := by
    rw [abs_sub_comm]
    exact hfloor.trans (div_le_self (by norm_num) (by linarith))
  have hround := abs_log_middlePrimeSieveThreshold_sub_half_log_le a X q hq hqD
  have hz1 : (1 : ℝ) ≤ middlePrimeSieveThreshold a X q := by
    exact_mod_cast middlePrimeSieveThreshold_pos a X q
  have hround1 := hround.trans (one_div_le_one_div_of_le (by norm_num) hz1)
  simp only [div_one] at hround1
  have heq : Real.log (middlePrimeSieveThreshold a X q : ℝ) -
      (a * Real.log X - Real.log q) / 2 =
    (Real.log (middlePrimeSieveThreshold a X q : ℝ) -
      (Real.log (middlePrimePowerCutoff a X : ℝ) - Real.log q) / 2) +
      (Real.log (middlePrimePowerCutoff a X : ℝ) - a * Real.log X) / 2 := by ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Explicit uniform rate for the actual sieve weight.
@isnad1 id=eventual.3h2v.s7.211510618a2a from=translated src=- shape=bd351791 vocab=c2ea2702
-/
theorem eventually_middlePrimeActualWeight_sub_ideal_le (a v : ℝ)
    (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      |middlePrimeActualWeight a X q - middlePrimeIdealWeight a X q| ≤
        20 / ((a - v) ^ 2 * Real.log X) := by
  have ha0 : 0 < a := by linarith
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (8 / (a - v)))
  have hpower := ((tendsto_rpow_atTop ha0).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hlog, hpower, eventually_mul_middlePrimePowerCutoff_le a v ha0.le hva 1,
    eventually_ge_atTop 2] with X hL hpow hD hX q hq
  dsimp only [Function.comp_def] at hL hpow
  have hL0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hq1 : 1 ≤ q := lt_of_lt_of_le (primaryCutoff_pos (by omega)) (mem_Ioc.mp hq).1.le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hqD : q ≤ middlePrimePowerCutoff a X :=
    (mem_Ioc.mp hq).2.trans (by simpa only [one_mul] using hD)
  obtain ⟨ht0, htv⟩ := middlePrimeLogCoordinate_bounds v X q hX hq
  have hcenter := abs_log_middlePrimeSieveThreshold_sub_power_half_le_two a X q hX hpow hq1 hqD
  have hcoord : (a - middlePrimeLogCoordinate X q) * Real.log X =
      a * Real.log X - Real.log q := by
    dsimp only [middlePrimeLogCoordinate]
    field_simp
  have hc : |Real.log (2 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hb := ratio_perturbation_le (Real.log X)
    (Real.log (middlePrimeSieveThreshold a X q : ℝ)) (middlePrimeLogCoordinate X q)
    a (a - v) (Real.log 2) hL0 (sub_pos.mpr hva) (by linarith) (by linarith)
    (by linarith) (by linarith) hc (by simpa only [hcoord] using hcenter) hL
  have hnum : Real.log ((2 * X : ℝ) / q) =
      Real.log X * (1 - middlePrimeLogCoordinate X q) + Real.log 2 := by
    rw [Real.log_div (mul_ne_zero (by norm_num) hx.ne') hq0.ne',
      Real.log_mul (by norm_num) hx.ne']
    dsimp only [middlePrimeLogCoordinate]
    field_simp
    ring
  simpa only [middlePrimeActualWeight, middlePrimeIdealWeight, hnum] using hb

/-- The actual weight approaches its ideal expression uniformly over all
active integers q, with the lower endpoint and every rounding retained.
@isnad1 id=eventual.4h3v.s7.57eb1e11ad18 from=translated src=- shape=40ec6d5a vocab=5ffd16d2
-/
theorem eventually_middlePrimeActualWeight_sub_ideal_le_epsilon (a v : ℝ)
    (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      |middlePrimeActualWeight a X q - middlePrimeIdealWeight a X q| ≤ ε := by
  have hinv := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  have hlim : Tendsto (fun X : ℕ => 20 / ((a - v) ^ 2 * Real.log X)) atTop (nhds 0) := by
    have h := hinv.const_mul (20 / (a - v) ^ 2)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards with X
    simp only [Function.comp_def, Pi.inv_apply, div_eq_mul_inv, mul_inv, mul_assoc]
  filter_upwards [eventually_middlePrimeActualWeight_sub_ideal_le a v hv hva ha,
    hlim.eventually (gt_mem_nhds hε)] with X hbound hsmall q hq
  exact (hbound q hq).trans hsmall.le

/-- A positive lower bound and one fixed upper bound hold simultaneously
throughout the growing family.
@isnad1 id=eventual.3h2v.s7.fea17d4f9f0d from=translated src=- shape=9e8c9fea vocab=4600cb6b
-/
theorem eventually_middlePrimeActualWeight_bounds (a v : ℝ)
    (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      1 ≤ middlePrimeActualWeight a X q ∧
        middlePrimeActualWeight a X q ≤ 1 + 2 / (a - v) := by
  filter_upwards [eventually_middlePrimeActualWeight_sub_ideal_le_epsilon
    a v hv hva ha 1 (by norm_num), eventually_ge_atTop 2] with X hdiff hX q hq
  obtain ⟨hid0, hid1⟩ := middlePrimeIdealWeight_bounds a v hva (by linarith) X q hX hq
  obtain ⟨hd0, hd1⟩ := abs_le.mp (hdiff q hq)
  constructor <;> linarith

/--
@isnad1 id=eventual.3h2v.s7.0259bb5890b7 from=translated src=- shape=b7040b3b vocab=4831f38a
-/
theorem eventually_abs_middlePrimeActualWeight_le (a v : ℝ)
    (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      |middlePrimeActualWeight a X q| ≤ 1 + 2 / (a - v) := by
  filter_upwards [eventually_middlePrimeActualWeight_bounds a v hv hva ha] with X hX q hq
  obtain ⟨hlo, hhi⟩ := hX q hq
  rwa [abs_of_nonneg (by linarith)]

end TwinPrime.Analytic
