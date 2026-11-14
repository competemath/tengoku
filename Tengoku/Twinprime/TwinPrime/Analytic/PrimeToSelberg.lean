import Tengoku.Twinprime.TwinPrime.Analytic.PrimeLog
import Tengoku.Twinprime.TwinPrime.Analytic.SelbergCenteredError

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The centered Selberg error from the named BV hypothesis

Every analytic premise of the centered-error calculation is discharged by
the prime estimates already derived from BV. The center is constructed by
the reciprocal prime sum; no value for that center is postulated.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=ex.1h0v.s6.48459599ca76 from=translated src=- shape=e4550ae5 vocab=cf26d107
-/
theorem MaximalBombieriVinogradov.centeredSelberg_error
    (hBV : MaximalBombieriVinogradov) :
    ∃ c K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      |centeredSelbergSummatory c x| ≤ K * x / (Real.log x) ^ 5 := by
  obtain ⟨Kψ, hKψ, hψ⟩ := hBV.psi_real_log_six
  obtain ⟨c, KL, hKL, hL⟩ := hBV.real_primeReciprocal_center
  obtain ⟨KP, hKP, hP⟩ := hBV.primeLog_real_error
  obtain ⟨K, hK, hA⟩ := exists_centeredSelbergSummatory_bound_of_prime_errors
    c Kψ KL KP hKψ hKL hKP hψ hL hP
  exact ⟨c, K, hK, hA⟩

end TwinPrime.Analytic
