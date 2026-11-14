import Tengoku.Twinprime.TwinPrime.Analytic.Cutoff
import Tengoku.Seed.Data.Nat.Sqrt
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics
import Tengoku.Seed.Algebra.Order.Floor.Semifield

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Power thresholds for the middle-prime sieve

The threshold is globally positive. On the actual outer interval its
support and level conditions follow from strict inequalities between the
fixed powers; its minimum tends to infinity uniformly over that interval.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

def middlePrimePowerCutoff (b : ℝ) (X : ℕ) : ℕ := ⌊(X : ℝ) ^ b⌋₊

def middlePrimeSieveThreshold (a : ℝ) (X q : ℕ) : ℕ :=
  max 1 (Nat.sqrt (middlePrimePowerCutoff a X / q))

/--
@isnad1 id=le.0h3v.s4.51bc53cf768c from=translated src=- shape=877de13a vocab=b6364819
-/
theorem middlePrimeSieveThreshold_pos (a : ℝ) (X q : ℕ) :
    1 ≤ middlePrimeSieveThreshold a X q := le_max_left _ _

/--
@isnad1 id=and.2h2v.s6.b8486e7aec98 from=translated src=- shape=374e9d41 vocab=608486c7
-/
theorem middlePrimePowerCutoff_bounds (b : ℝ) (hb : 0 ≤ b) (X : ℕ) (hX : 1 ≤ X) :
    (X : ℝ) ^ b / 2 ≤ (middlePrimePowerCutoff b X : ℝ) ∧
      (middlePrimePowerCutoff b X : ℝ) ≤ (X : ℝ) ^ b := by
  have hx : 1 ≤ (X : ℝ) ^ b := Real.one_le_rpow (by exact_mod_cast hX) hb
  exact ⟨(Nat.div_two_lt_floor hx).le, Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) b)⟩

/-- Any fixed multiple of the lower power cutoff is eventually below the
higher power cutoff. This supplies the uniform growing lower threshold.
@isnad1 id=eventual.2h3v.s5.5581fc859c21 from=translated src=- shape=f2baae78 vocab=1cd6ec1a
-/
theorem eventually_mul_middlePrimePowerCutoff_le (a v : ℝ) (ha : 0 ≤ a)
    (hva : v < a) (C : ℕ) :
    ∀ᶠ X : ℕ in atTop, C * middlePrimePowerCutoff v X ≤ middlePrimePowerCutoff a X := by
  have hg := ((tendsto_rpow_atTop (sub_pos.mpr hva)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (2 * (C : ℝ)))
  filter_upwards [hg, eventually_ge_atTop 1] with X hpow hX
  dsimp only [Function.comp_def] at hpow
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hfactor : (X : ℝ) ^ v * (X : ℝ) ^ (a - v) = (X : ℝ) ^ a := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hlower := (middlePrimePowerCutoff_bounds a ha X hX).1
  have hupper : (middlePrimePowerCutoff v X : ℝ) ≤ (X : ℝ) ^ v :=
    Nat.floor_le (Real.rpow_nonneg hx.le v)
  have hm := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx.le v)
  rw [hfactor] at hm
  have hfinal : (C : ℝ) * (middlePrimePowerCutoff v X : ℝ) ≤
      (middlePrimePowerCutoff a X : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg (α := ℝ) C)
    nlinarith
  exact_mod_cast hfinal

/-- Above the primary cutoff, the cubic threshold is larger than any
power at most three fifths. No primality hypothesis is needed.
@isnad1 id=lt.3h3v.s6.db79f1e62e73 from=translated src=- shape=5db94567 vocab=0e5c0fa4
-/
theorem middlePrimePowerCutoff_lt_cube (a : ℝ) (ha : a ≤ 3 / 5) (X q : ℕ)
    (hX : 1 ≤ X) (hq : primaryCutoff X < q) :
    middlePrimePowerCutoff a X < q ^ 3 := by
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hqroot : (X : ℝ) ^ (1 / 5 : ℝ) < q := by
    have hf := Nat.lt_floor_add_one ((X : ℝ) ^ (1 / 5 : ℝ))
    have hq' : (primaryCutoff X : ℝ) + 1 ≤ q := by exact_mod_cast hq
    exact hf.trans_le hq'
  have hpow : ((X : ℝ) ^ (1 / 5 : ℝ)) ^ 3 = (X : ℝ) ^ (3 / 5 : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X)]
    norm_num
  have hD : (middlePrimePowerCutoff a X : ℝ) < (q : ℝ) ^ 3 := by
    calc
      _ ≤ (X : ℝ) ^ a := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) a)
      _ ≤ (X : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 ha
      _ < _ := by
        rw [← hpow]
        exact pow_lt_pow_left₀ hqroot (Real.rpow_nonneg (Nat.cast_nonneg X) _) (by norm_num)
  exact_mod_cast hD

/--
@isnad1 id=lt.3h3v.s5.789f338b022c from=translated src=- shape=0c20b2ee vocab=c1925562
-/
theorem middlePrimeSieveThreshold_lt (a : ℝ) (ha : a ≤ 3 / 5) (X q : ℕ)
    (hX : 1 ≤ X) (hq : primaryCutoff X < q) :
    middlePrimeSieveThreshold a X q < q := by
  have hq1 : 1 < q := lt_of_le_of_lt (primaryCutoff_pos hX) hq
  have hc := middlePrimePowerCutoff_lt_cube a ha X q hX hq
  apply max_lt (by exact hq1)
  apply Nat.sqrt_lt'.mpr
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < q)).mpr
  simpa only [pow_succ, pow_two, mul_assoc] using hc

/--
@isnad1 id=le.2h3v.s5.5796ab6a12da from=translated src=- shape=92abf9d7 vocab=8d2a7986
-/
theorem middlePrimeSieveThreshold_level (a : ℝ) (X q : ℕ) (hq : 1 ≤ q)
    (hqD : q ≤ middlePrimePowerCutoff a X) :
    q * middlePrimeSieveThreshold a X q ^ 2 ≤ middlePrimePowerCutoff a X := by
  have hpos : 1 ≤ Nat.sqrt (middlePrimePowerCutoff a X / q) :=
    Nat.sqrt_pos.mpr (Nat.div_pos hqD hq)
  rw [middlePrimeSieveThreshold, max_eq_right hpos]
  exact (Nat.mul_le_mul_left q (Nat.sqrt_le' _)).trans
    (by simpa only [mul_comm] using Nat.div_mul_le_self (middlePrimePowerCutoff a X) q)

/-- Every prescribed lower threshold eventually works simultaneously for
all positive q through the upper outer cutoff.
@isnad1 id=eventual.2h3v.s6.5de33cc3cb06 from=translated src=- shape=a98e20c1 vocab=d9beb829
-/
theorem eventually_middlePrimeSieveThreshold_ge (a v : ℝ) (ha : 0 ≤ a)
    (hva : v < a) (Z : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ q ∈ Icc 1 (middlePrimePowerCutoff v X),
      Z ≤ middlePrimeSieveThreshold a X q := by
  filter_upwards [eventually_mul_middlePrimePowerCutoff_le a v ha hva (Z ^ 2)] with X hX q hq
  obtain ⟨hq1, hqW⟩ := mem_Icc.mp hq
  apply le_trans _ (le_max_right _ _)
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_div_iff_mul_le hq1).mpr
  exact (Nat.mul_le_mul_left (Z ^ 2) hqW).trans hX

/-- Simultaneous support and level conditions on the actual middle-prime
interval. The later cutoff restriction v<3/10 is not needed here.
@isnad1 id=eventual.3h2v.s7.a173d148503e from=translated src=- shape=59adc5ca vocab=538b6b7c
-/
theorem eventually_middlePrimeSieveThreshold_support (a v : ℝ)
    (hv : (1 / 5 : ℝ) < v) (hva : v < a) (ha : a < 1 / 2) :
    ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      middlePrimeSieveThreshold a X q < q ∧
      middlePrimeSieveThreshold a X q ≤ middlePrimePowerCutoff v X ∧
      q * middlePrimeSieveThreshold a X q ^ 2 ≤ middlePrimePowerCutoff a X := by
  have ha0 : 0 ≤ a := by linarith
  filter_upwards [eventually_mul_middlePrimePowerCutoff_le a v ha0 hva 1,
    eventually_ge_atTop 1] with X hD hX q hq
  obtain ⟨hUq, hqW⟩ := mem_Ioc.mp hq
  have hzq := middlePrimeSieveThreshold_lt a (by linarith) X q hX hUq
  refine ⟨hzq, hzq.le.trans hqW, middlePrimeSieveThreshold_level a X q ?_ ?_⟩
  · exact lt_of_lt_of_le (primaryCutoff_pos hX) hUq.le
  · simpa only [one_mul] using hqW.trans (by simpa only [one_mul] using hD)

/--
@isnad1 id=eventual.2h3v.s6.0a87dd0aeb94 from=translated src=- shape=2f5510c0 vocab=bde895dc
-/
theorem eventually_middlePrimeSieveThreshold_active_ge (a v : ℝ)
    (hv : (1 / 5 : ℝ) < v) (hva : v < a) (Z : ℕ) :
    ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      Z ≤ middlePrimeSieveThreshold a X q := by
  filter_upwards [eventually_middlePrimeSieveThreshold_ge a v (by linarith) hva Z,
    eventually_ge_atTop 1] with X hZ hX q hq
  exact hZ q (mem_Icc.mpr ⟨lt_of_lt_of_le (primaryCutoff_pos hX) (mem_Ioc.mp hq).1.le,
    (mem_Ioc.mp hq).2⟩)

/-- The two integer roundings still place the real quotient strictly
between z squared and (z+1) squared. Thus the logarithmic rounding error
is at most 1/z.
@isnad1 id=le.2h3v.s6.1bf08de8a052 from=translated src=- shape=f68123d9 vocab=88e49ca6
-/
theorem abs_log_middlePrimeSieveThreshold_sub_half_log_le (a : ℝ) (X q : ℕ)
    (hq : 1 ≤ q) (hqD : q ≤ middlePrimePowerCutoff a X) :
    |Real.log (middlePrimeSieveThreshold a X q : ℝ) -
      (Real.log (middlePrimePowerCutoff a X : ℝ) - Real.log q) / 2| ≤
        1 / (middlePrimeSieveThreshold a X q : ℝ) := by
  let D := middlePrimePowerCutoff a X
  let z := middlePrimeSieveThreshold a X q
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hq.trans hqD
  have hz1 : 1 ≤ z := middlePrimeSieveThreshold_pos a X q
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hz1
  have hz_eq : z = Nat.sqrt (D / q) :=
    max_eq_right (Nat.sqrt_pos.mpr (Nat.div_pos hqD hq))
  have hlo : (z : ℝ) ^ 2 ≤ (D : ℝ) / q := by
    apply (le_div_iff₀ hq0).mpr
    have h := middlePrimeSieveThreshold_level a X q hq hqD
    simpa only [mul_comm, Nat.cast_mul, Nat.cast_pow] using
      (show ((q * z ^ 2 : ℕ) : ℝ) ≤ D by exact_mod_cast h)
  have hhi : (D : ℝ) / q < ((z : ℝ) + 1) ^ 2 := by
    have hnat : D / q < (z + 1) ^ 2 := by
      simpa only [hz_eq, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' (D / q)
    have hmul := (Nat.div_lt_iff_lt_mul hq).mp hnat
    apply (div_lt_iff₀ hq0).mpr
    exact_mod_cast hmul
  have hloglo := Real.log_le_log (pow_pos hz0 2) hlo
  have hloghi := Real.log_le_log (div_pos hD0 hq0) hhi.le
  rw [Real.log_pow, Real.log_div hD0.ne' hq0.ne'] at hloglo hloghi
  norm_num only [Nat.cast_ofNat] at hloglo hloghi
  have hinc : Real.log ((z : ℝ) + 1) - Real.log z ≤ 1 / (z : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (show (0 : ℝ) < z + 1 by linarith) hz0)
    rw [Real.log_div (by positivity : (z : ℝ) + 1 ≠ 0) hz0.ne'] at h
    calc
      _ ≤ ((z : ℝ) + 1) / z - 1 := h
      _ = _ := by field_simp; ring
  change |Real.log (z : ℝ) - (Real.log (D : ℝ) - Real.log q) / 2| ≤ 1 / (z : ℝ)
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- The logarithmic approximation tends to zero uniformly throughout the
growing outer interval. The full modulus floor and quotient floor remain
in the threshold definition.
@isnad1 id=eventual.3h3v.s7.8ee2b826da78 from=translated src=- shape=ef42deee vocab=33dfbd0d
-/
theorem eventually_abs_log_middlePrimeSieveThreshold_sub_half_log_le
    (a v : ℝ) (hv : (1 / 5 : ℝ) < v) (hva : v < a)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ q ∈ Ioc (primaryCutoff X) (middlePrimePowerCutoff v X),
      |Real.log (middlePrimeSieveThreshold a X q : ℝ) -
        (Real.log (middlePrimePowerCutoff a X : ℝ) - Real.log q) / 2| ≤ ε := by
  obtain ⟨Z, hZ⟩ := exists_nat_gt (1 / ε)
  have hZ0 : (0 : ℝ) < Z := lt_trans (one_div_pos.mpr hε) hZ
  have hZbound : (1 : ℝ) / Z ≤ ε := by
    apply (div_le_iff₀ hZ0).mpr
    have h := (div_lt_iff₀ hε).mp hZ
    linarith
  filter_upwards [eventually_middlePrimeSieveThreshold_active_ge a v hv hva Z,
    eventually_mul_middlePrimePowerCutoff_le a v (by linarith) hva 1,
    eventually_ge_atTop 1] with X hz hD hX q hq
  have hq1 : 1 ≤ q := lt_of_lt_of_le (primaryCutoff_pos hX) (mem_Ioc.mp hq).1.le
  have hqD : q ≤ middlePrimePowerCutoff a X :=
    (mem_Ioc.mp hq).2.trans (by simpa only [one_mul] using hD)
  apply (abs_log_middlePrimeSieveThreshold_sub_half_log_le a X q hq1 hqD).trans
  apply le_trans _ hZbound
  exact div_le_div_of_nonneg_left (by norm_num) hZ0 (by exact_mod_cast hz q hq)

end TwinPrime.Analytic
