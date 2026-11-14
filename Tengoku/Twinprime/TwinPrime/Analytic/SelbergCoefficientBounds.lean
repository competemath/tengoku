import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocal
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusSelberg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absolute reciprocal mass of the centered Selberg coefficient

These finite bounds use only Chebyshev's elementary upper bound. They do not
assume the prime error or any Möbius cancellation. The quadratic logarithmic
growth is the input that makes a sufficiently short hyperbola head contract.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

namespace TwinPrime.Analytic

def chebyshevLinearConstant : ℝ := Real.log 4 + 4

/--
@isnad1 id=le.0h0v.s3.8163992f960c from=translated src=- shape=ff3a10fc vocab=fdeeacf7
-/
theorem chebyshevLinearConstant_nonneg : 0 ≤ chebyshevLinearConstant := by
  unfold chebyshevLinearConstant
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  linarith

/--
@isnad1 id=le.0h1v.s3.bcca0dcdfabc from=translated src=- shape=b9369acb vocab=8a60ff64
-/
theorem primeReciprocalSum_nonneg (N : ℕ) : 0 ≤ primeReciprocalSum N :=
  sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

/--
@isnad1 id=monotone.0h0v.s2.431c4cc763be from=translated src=- shape=54c8eceb vocab=8cabccdb
-/
theorem primeReciprocalSum_mono : Monotone primeReciprocalSum := by
  intro a b hab
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans hab⟩
  · intro n _ _
    exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

/--
@isnad1 id=eq.0h1v.s5.54d1b45558ef from=translated src=- shape=8acf36f4 vocab=c553b502
-/
theorem sum_one_div_Ioc_eq_harmonic (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (1 : ℝ) / n) = harmonic N := by
  have hI : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  simp [hI, harmonic_eq_sum_Icc, one_div]

/-- The elementary prime reciprocal bound has a constant independent of N.
@isnad1 id=le.1h1v.s5.0f86edb10059 from=translated src=- shape=374c2742 vocab=dac77636
-/
theorem primeReciprocalSum_le_log (N : ℕ) (hN : 1 ≤ N) :
    primeReciprocalSum N ≤ chebyshevLinearConstant * (2 + Real.log N) := by
  have habel := reciprocalCoefficientSum_sub_eq (fun n => vonMangoldt n) 1 N
    (by omega) hN
  have hcum : ∀ t : ℕ, coefficientSum (fun n => vonMangoldt n) t = Chebyshev.psi t := by
    intro t
    simp [coefficientSum, Chebyshev.psi]
  simp only [hcum] at habel
  have hid : primeReciprocalSum N = Chebyshev.psi N / N +
      ∑ t ∈ Ico 1 N, Chebyshev.psi t / ((t : ℝ) * (t + 1)) := by
    simpa [reciprocalCoefficientSum, primeReciprocalSum, Chebyshev.psi] using habel
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfirst : Chebyshev.psi N / N ≤ chebyshevLinearConstant :=
    (div_le_iff₀ hNr).mpr (Chebyshev.psi_le_const_mul_self hNr.le)
  have htail : (∑ t ∈ Ico 1 N, Chebyshev.psi t / ((t : ℝ) * (t + 1))) ≤
      chebyshevLinearConstant * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ t ∈ Ico 1 N, chebyshevLinearConstant * (1 / (t : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Ico.mp ht).1
        calc
          _ ≤ (chebyshevLinearConstant * t) / ((t : ℝ) * (t + 1)) :=
            div_le_div_of_nonneg_right (Chebyshev.psi_le_const_mul_self ht0.le) (by positivity)
          _ = chebyshevLinearConstant / (t + 1) := by field_simp
          _ ≤ chebyshevLinearConstant / t :=
            div_le_div_of_nonneg_left chebyshevLinearConstant_nonneg ht0 (by linarith)
          _ = _ := by ring
      _ ≤ ∑ t ∈ Ioc 0 N, chebyshevLinearConstant * (1 / (t : ℝ)) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro t ht
          exact mem_Ioc.mpr ⟨(mem_Ico.mp ht).1, (mem_Ico.mp ht).2.le⟩
        · intro t _ _
          exact mul_nonneg chebyshevLinearConstant_nonneg (by positivity)
      _ = _ := by rw [← mul_sum, sum_one_div_Ioc_eq_harmonic]
  rw [hid]
  have hH := harmonic_le_one_add_log N
  have hmul := mul_le_mul_of_nonneg_left hH chebyshevLinearConstant_nonneg
  nlinarith

/--
@isnad1 id=le.0h1v.s5.a3d48fac6605 from=translated src=- shape=3d12c4eb vocab=0f2ae6ee
-/
theorem vonMangoldt_convolution_nonneg (n : ℕ) : 0 ≤ (vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

/--
@isnad1 id=le.1h2v.s6.662320c5d93b from=translated src=- shape=d5bda31c vocab=14220a78
-/
theorem abs_centeredSelbergCoefficient_le (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |centeredSelbergCoefficient c n| ≤
      (vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n +
        vonMangoldt n * Real.log n + 2 * |c| := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hn0 : n ≠ 0 := by omega
  have heq : centeredSelbergCoefficient c n =
      (vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n -
        vonMangoldt n * Real.log n - 2 * c := by
    simp [centeredSelbergCoefficient, sub_eq_add_neg, ArithmeticFunction.zeta_apply, hn0]
  rw [heq]
  calc
    _ ≤ |(vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n -
        vonMangoldt n * Real.log n| + |2 * c| := abs_sub _ _
    _ ≤ _ := by
      have h := abs_sub ((vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n)
        (vonMangoldt n * Real.log n)
      rw [abs_of_nonneg (vonMangoldt_convolution_nonneg n),
        abs_of_nonneg (mul_nonneg vonMangoldt_nonneg hlog)] at h
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      linarith

/--
@isnad1 id=le.0h1v.s6.513b5b5f82c3 from=translated src=- shape=5b1b1b3f vocab=58a0585d
-/
theorem reciprocal_vonMangoldt_convolution_le (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n / n) ≤
      (primeReciprocalSum N) ^ 2 := by
  have hid := sum_Ioc_convolution_weight vonMangoldt vonMangoldt (fun n => 1 / (n : ℝ)) N
  have heq : (∑ n ∈ Ioc 0 N, (vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n / n) =
      ∑ d ∈ Ioc 0 N, (vonMangoldt d / d) * primeReciprocalSum (N / d) := by
    convert hid using 1
    · apply sum_congr rfl
      intro n _
      ring
    · apply sum_congr rfl
      intro d hd
      unfold primeReciprocalSum
      rw [mul_sum, mul_sum]
      apply sum_congr rfl
      intro m hm
      push_cast
      ring
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, (vonMangoldt d / d) * primeReciprocalSum N := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left (primeReciprocalSum_mono (Nat.div_le_self N d))
        (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg d))
    _ = _ := by rw [← sum_mul]; unfold primeReciprocalSum; ring

def centeredSelbergReciprocalMass (c : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, |centeredSelbergCoefficient c n| / n

/--
@isnad1 id=le.0h2v.s6.6d671143ae58 from=translated src=- shape=988876b5 vocab=a9b633a2
-/
theorem centeredSelbergReciprocalMass_le (c : ℝ) (N : ℕ) :
    centeredSelbergReciprocalMass c N ≤
      (primeReciprocalSum N) ^ 2 + Real.log N * primeReciprocalSum N +
        2 * |c| * (harmonic N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N,
        ((vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n / n +
          Real.log N * (vonMangoldt n / n) + 2 * |c| * (1 / (n : ℝ))) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
      have hlog := Real.log_le_log hn0
        (show (n : ℝ) ≤ (N : ℝ) by exact_mod_cast (mem_Ioc.mp hn).2)
      have h := div_le_div_of_nonneg_right
        (abs_centeredSelbergCoefficient_le c n (mem_Ioc.mp hn).1) hn0.le
      have hlogmul := mul_le_mul_of_nonneg_left hlog
        (div_nonneg (vonMangoldt_nonneg (n := n)) hn0.le)
      calc
        _ ≤ ((vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n +
            vonMangoldt n * Real.log n + 2 * |c|) / n := h
        _ ≤ _ := by
          calc
            _ = (vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n / n +
                (vonMangoldt n / n) * Real.log n + 2 * |c| * (1 / (n : ℝ)) := by ring
            _ ≤ _ := by nlinarith [hlogmul]
    _ = (∑ n ∈ Ioc 0 N, (vonMangoldt * vonMangoldt : ArithmeticFunction ℝ) n / n) +
        Real.log N * primeReciprocalSum N + 2 * |c| * (harmonic N : ℝ) := by
      simp only [sum_add_distrib, ← mul_sum, sum_one_div_Ioc_eq_harmonic, primeReciprocalSum]
    _ ≤ _ := by linarith [reciprocal_vonMangoldt_convolution_le N]

def selbergReciprocalMassConstant (c : ℝ) : ℝ :=
  chebyshevLinearConstant ^ 2 + chebyshevLinearConstant + 2 * |c|

/--
@isnad1 id=le.0h1v.s3.95cddeb7df4f from=translated src=- shape=8a62b088 vocab=923521c2
-/
theorem selbergReciprocalMassConstant_nonneg (c : ℝ) : 0 ≤ selbergReciprocalMassConstant c :=
  add_nonneg (add_nonneg (sq_nonneg _) chebyshevLinearConstant_nonneg) (by positivity)

/-- The complete absolute coefficient mass grows at most quadratically in
the logarithm. No cancellation assumption is used in this estimate.
@isnad1 id=le.1h2v.s6.afdd05a02cde from=translated src=- shape=dbd76b7e vocab=c566f365
-/
theorem centeredSelbergReciprocalMass_le_log_sq (c : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    centeredSelbergReciprocalMass c N ≤
      selbergReciprocalMassConstant c * (2 + Real.log N) ^ 2 := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hL := primeReciprocalSum_le_log N hN
  have hL0 := primeReciprocalSum_nonneg N
  have hH : (harmonic N : ℝ) ≤ (2 + Real.log (N : ℝ)) ^ 2 := by
    have h := harmonic_le_one_add_log N
    nlinarith [sq_nonneg (Real.log (N : ℝ))]
  calc
    _ ≤ (primeReciprocalSum N) ^ 2 + Real.log N * primeReciprocalSum N +
        2 * |c| * (harmonic N : ℝ) := centeredSelbergReciprocalMass_le c N
    _ ≤ (chebyshevLinearConstant * (2 + Real.log N)) ^ 2 +
        (2 + Real.log N) * (chebyshevLinearConstant * (2 + Real.log N)) +
          2 * |c| * (2 + Real.log N) ^ 2 := by
      gcongr
      linarith
    _ = _ := by unfold selbergReciprocalMassConstant; ring

/--
@isnad1 id=le.1h2v.s6.614c4d065534 from=translated src=- shape=d516aa69 vocab=87cdda04
-/
theorem centeredSelbergReciprocalMass_floor_le (c x : ℝ) (hx : 1 ≤ x) :
    centeredSelbergReciprocalMass c ⌊x⌋₊ ≤
      selbergReciprocalMassConstant c * (2 + Real.log x) ^ 2 := by
  have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hlog0 : 0 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast hn) (Nat.floor_le (by linarith))
  exact (centeredSelbergReciprocalMass_le_log_sq c ⌊x⌋₊ hn).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) 2) (selbergReciprocalMassConstant_nonneg c))

end TwinPrime.Analytic
