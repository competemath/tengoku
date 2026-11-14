import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocalReal
import Tengoku.Seed.NumberTheory.AbelSummation
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Centered Abel summation for the reciprocal Mangoldt sum

Real endpoints retain the exact natural floors. The centering constant
cancels by integration by parts, leaving an error controlled by the two
endpoint values and the full variation of the test function.
-/

noncomputable section

open Finset MeasureTheory ArithmeticFunction

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.0h1v.s5.fb0e9e9d1612 from=translated src=- shape=730454ab vocab=39ef1d28
-/
theorem realPrimeReciprocalSum_eq_sum_Icc (y : ℝ) :
    realPrimeReciprocalSum y =
      ∑ n ∈ Icc 0 ⌊y⌋₊, vonMangoldt n / (n : ℝ) := by
  unfold realPrimeReciprocalSum primeReciprocalSum
  apply sum_subset
  · intro n hn
    exact mem_Icc.mpr ⟨Nat.zero_le n, (mem_Ioc.mp hn).2⟩
  · intro n hn hn'
    have hn0 : n = 0 := by
      have hnle := (mem_Icc.mp hn).2
      by_contra hne
      exact hn' (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hne, hnle⟩)
    simp [hn0]

private theorem intervalIntegrable_deriv_mul_reciprocal_error
    {a b : ℝ} {f : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) (c : ℝ) :
    IntervalIntegrable
      (fun y => deriv f y * (realPrimeReciprocalSum y - Real.log y - c))
      volume a b := by
  have hdf : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf_int
  have hA : IntervalIntegrable (fun y => deriv f y * realPrimeReciprocalSum y)
      volume a b := by
    simp_rw [realPrimeReciprocalSum_eq_sum_Icc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_mul_sum_Icc (fun n => vonMangoldt n / (n : ℝ)) ha.le hf_int)
  have hg : ContinuousOn (fun y => Real.log y + c) (Set.uIcc a b) := by
    intro y hy
    have hy0 : 0 < y := ha.trans_le ((Set.uIcc_of_le hab ▸ hy).1)
    exact ((Real.continuousAt_log hy0.ne').add_const c).continuousWithinAt
  have hsub := hA.sub (hdf.mul_continuousOn hg)
  convert hsub using 1
  ext y
  ring

/-- Exact centered Abel summation, with no asymptotic hypothesis.
@isnad1 id=eq.4h4v.s8.50749eac3afa from=translated src=- shape=3df74e74 vocab=21ef98cd
-/
theorem primeReciprocal_abel_centered_identity
    {a b : ℝ} {f : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf_diff : ∀ y ∈ Set.Icc a b, DifferentiableAt ℝ f y)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) (c : ℝ) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n / (n : ℝ) * f n) -
        (∫ y in a..b, f y / y) =
      f b * (realPrimeReciprocalSum b - Real.log b - c) -
        f a * (realPrimeReciprocalSum a - Real.log a - c) -
          ∫ y in a..b,
            deriv f y * (realPrimeReciprocalSum y - Real.log y - c) := by
  have habel := sum_mul_eq_sub_sub_integral_mul
    (fun n => vonMangoldt n / (n : ℝ)) ha.le hab hf_diff hf_int
  simp_rw [← realPrimeReciprocalSum_eq_sum_Icc] at habel
  rw [← intervalIntegral.integral_of_le hab] at habel
  have hdf : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf_int
  have hg : ∀ y ∈ Set.uIcc a b,
      HasDerivAt (fun y => Real.log y + c) (1 / y) y := by
    intro y hy
    have hy0 : 0 < y := ha.trans_le ((Set.uIcc_of_le hab ▸ hy).1)
    simpa only [one_div] using (Real.hasDerivAt_log hy0.ne').add_const c
  have hginv : IntervalIntegrable (fun y : ℝ => 1 / y) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro y hy
    exact (ha.trans_le ((Set.uIcc_of_le hab ▸ hy).1)).ne'
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun y hy => (hf_diff y (Set.uIcc_of_le hab ▸ hy)).hasDerivAt)
    hg hdf hginv
  have hgcont : ContinuousOn (fun y => Real.log y + c) (Set.uIcc a b) :=
    fun y hy => (hg y hy).continuousAt.continuousWithinAt
  have hA : IntervalIntegrable (fun y => deriv f y * realPrimeReciprocalSum y)
      volume a b := by
    simp_rw [realPrimeReciprocalSum_eq_sum_Icc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_mul_sum_Icc (fun n => vonMangoldt n / (n : ℝ)) ha.le hf_int)
  have herror : (∫ y in a..b,
      deriv f y * (realPrimeReciprocalSum y - Real.log y - c)) =
      (∫ y in a..b, deriv f y * realPrimeReciprocalSum y) -
        ∫ y in a..b, deriv f y * (Real.log y + c) := by
    rw [← intervalIntegral.integral_sub hA (hdf.mul_continuousOn hgcont)]
    congr 1
    ext y
    ring
  simp only [← div_eq_mul_one_div] at hparts
  rw [herror]
  have hsum : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n / (n : ℝ) * f n) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * (vonMangoldt n / (n : ℝ)) := by
    apply sum_congr rfl
    intro n hn
    ring
  rw [hsum, habel, hparts]
  ring

/-- A uniform centered reciprocal error controls Abel summation by total
variation. Differentiability and an integrable derivative suffice.
@isnad1 id=le.5h5v.s8.151443643635 from=translated src=- shape=e6492749 vocab=566c5227
-/
theorem abs_primeReciprocal_abel_error_le
    {a b : ℝ} {f : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf_diff : ∀ y ∈ Set.Icc a b, DifferentiableAt ℝ f y)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) (c M : ℝ)
    (herror : ∀ y ∈ Set.Icc a b,
      |realPrimeReciprocalSum y - Real.log y - c| ≤ M) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n / (n : ℝ) * f n) -
        (∫ y in a..b, f y / y)| ≤
      M * (|f a| + |f b| + ∫ y in a..b, |deriv f y|) := by
  have hdf : IntervalIntegrable (deriv f) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf_int
  have hE := intervalIntegrable_deriv_mul_reciprocal_error ha hab hf_int c
  have hint : |∫ y in a..b,
      deriv f y * (realPrimeReciprocalSum y - Real.log y - c)| ≤
      M * ∫ y in a..b, |deriv f y| := by
    calc
      _ ≤ ∫ y in a..b,
          |deriv f y * (realPrimeReciprocalSum y - Real.log y - c)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ y in a..b, M * |deriv f y| := by
        apply intervalIntegral.integral_mono_on hab hE.abs (hdf.abs.const_mul M)
        intro y hy
        rw [abs_mul, mul_comm M]
        exact mul_le_mul_of_nonneg_left (herror y hy) (abs_nonneg _)
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [primeReciprocal_abel_centered_identity ha hab hf_diff hf_int c]
  calc
    _ ≤ |f b * (realPrimeReciprocalSum b - Real.log b - c)| +
        |f a * (realPrimeReciprocalSum a - Real.log a - c)| +
          |∫ y in a..b, deriv f y *
            (realPrimeReciprocalSum y - Real.log y - c)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ |f b| * M + |f a| * M + M * ∫ y in a..b, |deriv f y| := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (herror b ⟨hab, le_rfl⟩) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (herror a ⟨le_rfl, hab⟩) (abs_nonneg _))) hint
    _ = _ := by ring

/-- The continuously differentiable version of the centered Abel bound.
@isnad1 id=le.5h5v.s8.df84b4d5a72a from=translated src=- shape=54c79839 vocab=12a24574
-/
theorem abs_primeReciprocal_abel_error_le_of_continuous_deriv
    {a b : ℝ} {f : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf_diff : ∀ y ∈ Set.Icc a b, DifferentiableAt ℝ f y)
    (hf_deriv : ContinuousOn (deriv f) (Set.Icc a b)) (c M : ℝ)
    (herror : ∀ y ∈ Set.Icc a b,
      |realPrimeReciprocalSum y - Real.log y - c| ≤ M) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, vonMangoldt n / (n : ℝ) * f n) -
        (∫ y in a..b, f y / y)| ≤
      M * (|f a| + |f b| + ∫ y in a..b, |deriv f y|) :=
  abs_primeReciprocal_abel_error_le ha hab hf_diff
    (hf_deriv.integrableOn_Icc) c M herror

end TwinPrime.Analytic
