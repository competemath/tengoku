import Tengoku.Twinprime.TwinPrime.Analytic.ClassicalDistribution
import Tengoku.Twinprime.TwinPrime.Analytic.PrimeReciprocalReal
import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveThreshold
import Tengoku.Twinprime.TwinPrime.Analytic.CutoffLogarithms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A bounded reciprocal mass on a fixed middle-prime power interval

The finite comparison keeps the actual prime interval.  The eventual
constant follows from the proved reciprocal Mangoldt estimate at the real
endpoint `X^v`, with its natural floor retained exactly.
-/

noncomputable section

open Finset Filter ArithmeticFunction

namespace TwinPrime.Analytic

theorem sum_middlePrime_reciprocal_le_primeReciprocalSum (U W : ℕ)
    (hU : 1 ≤ U) :
    (∑ p ∈ (Ioc U W).filter Nat.Prime, (1 : ℝ) / p) ≤
      primeReciprocalSum W / Real.log ((U : ℝ) + 1) := by
  have hlog : 0 < Real.log ((U : ℝ) + 1) := Real.log_pos (by exact_mod_cast (by omega : 1 < U + 1))
  apply (le_div_iff₀ hlog).mpr
  calc
    (∑ p ∈ (Ioc U W).filter Nat.Prime, (1 : ℝ) / p) * Real.log ((U : ℝ) + 1) =
        ∑ p ∈ (Ioc U W).filter Nat.Prime, Real.log ((U : ℝ) + 1) / p := by
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p ∈ (Ioc U W).filter Nat.Prime, vonMangoldt p / (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
      rw [vonMangoldt_apply_prime hpprime]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
      apply Real.log_le_log (by positivity)
      exact_mod_cast (mem_Ioc.mp hpI).1
    _ ≤ primeReciprocalSum W := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpI := mem_Ioc.mp (mem_filter.mp hp).1
        exact mem_Ioc.mpr ⟨lt_of_lt_of_le (by omega : 0 < U + 1) hpI.1, hpI.2⟩
      · intro p hp hp'
        exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg p)

end TwinPrime.Analytic
