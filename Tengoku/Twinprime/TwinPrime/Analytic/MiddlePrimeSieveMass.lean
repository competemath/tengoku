import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveCorrection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The mass of the middle-prime sieve correction

The correction's local factors are inverse to those of the existing
smoothing correction, including the factor at two. Absolute convergence
therefore identifies its total mass with the reciprocal of `2 C₂`.
-/

noncomputable section

open Finset ArithmeticFunction Filter Topology

namespace TwinPrime.Analytic

/-- The two correction Euler factors multiply to one at every prime,
and both prime indicators equal one away from primes.-/
theorem middlePrimeSelbergCorrection_eulerFactor_mul_smoothing (p : ℕ) :
    ({q : ℕ | q.Prime}.mulIndicator
      (fun q => ∑' k : ℕ, middlePrimeSelbergCorrection (q ^ k))) p *
      ({q : ℕ | q.Prime}.mulIndicator
        (fun q => ∑' k : ℕ, smoothingCorrection (q ^ k))) p = 1 := by
  by_cases hp : p.Prime
  · rw [Set.mulIndicator_of_mem (show p ∈ {q : ℕ | q.Prime} from hp),
      Set.mulIndicator_of_mem (show p ∈ {q : ℕ | q.Prime} from hp)]
    by_cases hp2 : p = 2
    · subst p
      rw [hasSum_middlePrimeSelbergCorrection_two_pow.tsum_eq,
        hasSum_smoothingCorrection_two_pow.tsum_eq]
      norm_num
    · have hodd : Odd p := hp.odd_of_ne_two hp2
      rw [(hasSum_middlePrimeSelbergCorrection_odd_prime_pow p hp hodd).tsum_eq,
        (hasSum_smoothingCorrection_odd_prime_pow p hp hodd).tsum_eq]
      have hp3 : (3 : ℝ) ≤ p := by
        exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp2' : (p : ℝ) - 2 ≠ 0 := by linarith
      field_simp
      ring
  · rw [Set.mulIndicator_of_notMem (show p ∉ {q : ℕ | q.Prime} from hp),
      Set.mulIndicator_of_notMem (show p ∉ {q : ℕ | q.Prime} from hp)]
    norm_num

/-- The absolutely convergent correction series has mass `1 / (2 C₂)`.-/
theorem tsum_middlePrimeSelbergCorrection :
    (∑' n : ℕ, middlePrimeSelbergCorrection n) = 1 / (2 * twinPrimeConstant) := by
  have hmid := EulerProduct.eulerProduct_hasProd_mulIndicator
    isMultiplicative_middlePrimeSelbergCorrection.map_one
    isMultiplicative_middlePrimeSelbergCorrection.map_mul_of_coprime
    summable_norm_middlePrimeSelbergCorrection
    (ArithmeticFunction.map_zero (f := middlePrimeSelbergCorrection))
  have hsmooth := EulerProduct.eulerProduct_hasProd_mulIndicator
    isMultiplicative_smoothingCorrection.map_one
    isMultiplicative_smoothingCorrection.map_mul_of_coprime
    summable_norm_smoothingCorrection
    (ArithmeticFunction.map_zero (f := smoothingCorrection))
  have hprod := (hmid.mul hsmooth).congr_fun
    (fun p => (middlePrimeSelbergCorrection_eulerFactor_mul_smoothing p).symm)
  have hone : (∑' n : ℕ, middlePrimeSelbergCorrection n) *
      (∑' n : ℕ, smoothingCorrection n) = 1 := hprod.unique hasProd_one
  rw [tsum_smoothingCorrection] at hone
  exact (eq_div_iff (ne_of_gt (mul_pos (by norm_num) twinPrimeConstant_pos))).mpr hone

end TwinPrime.Analytic
