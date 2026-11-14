import Tengoku.Seed.NumberTheory.ArithmeticFunction.VonMangoldt
import Tengoku.Seed.Tactic
import Tengoku.Twinprime.TwinPrime.Analytic.Vaughan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Truncated divisor sums for the fixed-shift correlation

All ratios inside logarithms are real ratios. These finite identities use no distribution
estimate and do not assert a pointwise comparison with the von Mangoldt function.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- The signed truncated von Mangoldt divisor sum `Λ_U(n)`.-/
def truncatedMangoldt (U n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors with d ≤ U, (μ d : ℝ) * Real.log ((U : ℝ) / d)

/-- The truncated Möbius divisor sum `m_U(n)`.-/
def truncatedMoebiusSum (U n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors with d ≤ U, (μ d : ℝ)

/-- The first term of Vaughan's identity, written as a finite divisor sum.-/
def truncatedMoebiusLog (U n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors with d ≤ U, (μ d : ℝ) * Real.log ((n : ℝ) / d)

/--
@isnad1 id=eq.1h2v.s6.7b9d9032e511 from=translated src=- shape=08470fd8 vocab=acc9bec0
-/
theorem truncatedMangoldt_eq (U n : ℕ) (hU : 0 < U) :
    truncatedMangoldt U n = Real.log U * truncatedMoebiusSum U n -
      ∑ d ∈ n.divisors with d ≤ U, (μ d : ℝ) * Real.log d := by
  unfold truncatedMangoldt truncatedMoebiusSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
  rw [Real.log_div (by exact_mod_cast hU.ne') (by exact_mod_cast hdpos.ne')]
  ring

/-- The exact correction from the first Vaughan term to `Λ_U`.
@isnad1 id=eq.2h2v.s6.aa6c575dee1e from=translated src=- shape=5df979ea vocab=3b7251e4
-/
theorem truncatedMoebiusLog_eq (U n : ℕ) (hU : 0 < U) (hn : 0 < n) :
    truncatedMoebiusLog U n = truncatedMangoldt U n +
      Real.log ((n : ℝ) / U) * truncatedMoebiusSum U n := by
  unfold truncatedMoebiusLog truncatedMangoldt truncatedMoebiusSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
  rw [Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hdpos.ne'),
    Real.log_div (by exact_mod_cast hU.ne') (by exact_mod_cast hdpos.ne'),
    Real.log_div (by exact_mod_cast hn.ne') (by exact_mod_cast hU.ne')]
  ring

/--
@isnad1 id=eq.0h2v.s5.3f4fe0d36860 from=translated src=- shape=b634669c vocab=37f37884
-/
theorem moebiusLow_mul_log_apply (U n : ℕ) :
    (moebiusLow U * ArithmeticFunction.log) n = truncatedMoebiusLog U n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d r => moebiusLow U d * ArithmeticFunction.log r)]
  unfold truncatedMoebiusLog
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hdvd := (Nat.mem_divisors.mp hd).1
  rw [moebiusLow, cutoffLow_apply, log_apply, Nat.cast_div hdvd]
  · by_cases h : d ≤ U <;> simp [h]
  · exact_mod_cast hdpos.ne'

/-- A fixed modulus range for the truncated sum, including its divisibility filter.
@isnad1 id=eq.1h2v.s6.76159bd44a7e from=translated src=- shape=9386c769 vocab=07388b1d
-/
theorem truncatedMangoldt_eq_moduli (U n : ℕ) (hn : 0 < n) :
    truncatedMangoldt U n = ∑ d ∈ range (U + 1) with d ∣ n,
      (μ d : ℝ) * Real.log ((U : ℝ) / d) := by
  unfold truncatedMangoldt
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_range]
  omega

/-- A uniform coefficient bound on the full truncated modulus range.
@isnad1 id=le.1h2v.s6.649043967db2 from=translated src=- shape=187b8f8e vocab=79d547f8
-/
theorem abs_moebius_log_div_le (U d : ℕ) (hd : d ≤ U) :
    |(μ d : ℝ) * Real.log ((U : ℝ) / d)| ≤ Real.log (U + 1) := by
  by_cases hd0 : d = 0
  · simp only [hd0, Nat.cast_zero, div_zero, Real.log_zero, mul_zero, abs_zero]
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) U
    linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
  have hdU : (d : ℝ) ≤ U := by exact_mod_cast hd
  have hratio : 1 ≤ (U : ℝ) / d := by rw [le_div_iff₀ hdpos]; linarith
  have hlog := Real.log_nonneg hratio
  have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
  rw [abs_mul, abs_of_nonneg hlog]
  calc
    _ ≤ 1 * Real.log ((U : ℝ) / d) := mul_le_mul_of_nonneg_right hmu hlog
    _ ≤ Real.log (U + 1) := by
      rw [one_mul]
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hdpos]
      have hU0 := Nat.cast_nonneg (α := ℝ) U
      nlinarith

end TwinPrime.Analytic
