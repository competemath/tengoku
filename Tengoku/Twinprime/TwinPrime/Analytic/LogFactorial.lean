import Tengoku.Seed.NumberTheory.Harmonic.Bounds
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An elementary factorial-logarithm error bound

The error between the sum of logarithms and `N log N - N` is nonnegative
and at most the harmonic sum. Each successive error increment lies between
zero and the next harmonic summand, so no asymptotic integration is needed.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The error increment is bounded by one harmonic summand.
@isnad1 id=and.1h1v.s7.b3ecc6bfad4f from=translated src=- shape=e841298b vocab=58955ff2
-/
theorem logFactorial_increment_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 - x * (Real.log (x + 1) - Real.log x) ∧
      1 - x * (Real.log (x + 1) - Real.log x) ≤ 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have hlogUpper := Real.log_le_sub_one_of_pos (div_pos hx1 hx)
  have hlogLower := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx)
  rw [Real.log_div hx1.ne' hx.ne'] at hlogUpper hlogLower
  have hupper := mul_le_mul_of_nonneg_left hlogUpper hx.le
  have hlower := mul_le_mul_of_nonneg_left hlogLower hx.le
  have hU : x * ((x + 1) / x - 1) = 1 := by field_simp; ring
  have hL : x * (1 - ((x + 1) / x)⁻¹) = 1 - 1 / (x + 1) := by field_simp; ring
  rw [hU] at hupper
  rw [hL] at hlower
  constructor <;> linarith

/-- Exact increment formula for the finite sum of logarithms.
@isnad1 id=eq.0h1v.s7.fbbd9f6c1ec0 from=translated src=- shape=c21ed1e2 vocab=2fd386b9
-/
theorem sum_log_sub_main_succ (N : ℕ) :
    (∑ n ∈ Ioc 0 (N + 1), Real.log (n : ℝ)) -
        (((N + 1 : ℕ) : ℝ) * Real.log (N + 1 : ℕ) - (N + 1 : ℕ)) =
      ((∑ n ∈ Ioc 0 N, Real.log (n : ℝ)) -
        ((N : ℝ) * Real.log N - N)) +
      (1 - (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log N)) := by
  rw [sum_Ioc_succ_top (Nat.zero_le N)]
  push_cast
  ring

/-- The factorial-logarithm error lies between zero and the harmonic sum.
@isnad1 id=and.0h1v.s7.d98ba43c02ab from=translated src=- shape=1d982562 vocab=0173be23
-/
theorem sum_log_sub_main_bounds (N : ℕ) :
    0 ≤ (∑ n ∈ Ioc 0 N, Real.log (n : ℝ)) - ((N : ℝ) * Real.log N - N) ∧
      (∑ n ∈ Ioc 0 N, Real.log (n : ℝ)) - ((N : ℝ) * Real.log N - N) ≤
        (harmonic N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    by_cases hN : N = 0
    · subst N
      norm_num
    · have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hstep := logFactorial_increment_bounds hNr
      have hH : (harmonic (N + 1) : ℝ) = (harmonic N : ℝ) + 1 / ((N : ℝ) + 1) := by
        rw [harmonic_succ]
        push_cast
        rw [one_div]
      rw [sum_log_sub_main_succ, hH]
      constructor <;> linarith [ih.1, ih.2, hstep.1, hstep.2]

/-- A concise absolute factorial-logarithm error bound.
@isnad1 id=le.0h1v.s6.8686d47c8618 from=translated src=- shape=4c51a453 vocab=9d7ffda6
-/
theorem abs_sum_log_sub_main_le_harmonic (N : ℕ) :
    |(∑ n ∈ Ioc 0 N, Real.log (n : ℝ)) - ((N : ℝ) * Real.log N - N)| ≤
      (harmonic N : ℝ) := by
  rw [abs_of_nonneg (sum_log_sub_main_bounds N).1]
  exact (sum_log_sub_main_bounds N).2

/--
@isnad1 id=le.0h1v.s6.ea8cf28a205e from=translated src=- shape=fafdc543 vocab=5cff2ba6
-/
theorem abs_sum_log_sub_main_le_one_add_log (N : ℕ) :
    |(∑ n ∈ Ioc 0 N, Real.log (n : ℝ)) - ((N : ℝ) * Real.log N - N)| ≤
      1 + Real.log N :=
  (abs_sum_log_sub_main_le_harmonic N).trans (harmonic_le_one_add_log N)

end TwinPrime.Analytic
