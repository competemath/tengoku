import Tengoku.Twinprime.TwinPrime.Analytic.GrowthBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ordinary Chebyshev error supplied by modulus one

The named maximal Bombieri--Vinogradov hypothesis includes modulus one and
therefore implies an ordinary prime-number estimate with every fixed power
of logarithmic saving. This is a consequence of the existing distribution
hypothesis, not an unconditional prime-number theorem.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

/-- Modulus one retains every positive summation index.
@isnad1 id=eq.0h2v.s4.faf7fe044dfd from=translated src=- shape=ee1754be vocab=d0512510
-/
theorem progressionPsi_modulus_one (N a : ℕ) :
    progressionPsi N 1 a = Chebyshev.psi (N : ℝ) := by
  simp [progressionPsi, Chebyshev.psi, Nat.modEq_one]

/--
@isnad1 id=eq.0h2v.s4.8549f96b3bb6 from=translated src=- shape=8687564a vocab=a4f06357
-/
theorem progressionError_modulus_one (N a : ℕ) :
    progressionError N 1 a = Chebyshev.psi (N : ℝ) - (N : ℝ) := by
  simp [progressionError, progressionPsi_modulus_one]

/-- The finite maximum at modulus one controls the ordinary Chebyshev error
at every included integer endpoint.
@isnad1 id=le.1h2v.s5.81cd99a3471e from=translated src=- shape=1112a335 vocab=9bd939a0
-/
theorem abs_psi_sub_nat_le_progressionMaxError (N T : ℕ) (hNT : N ≤ T) :
    |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤ progressionMaxError T 1 := by
  simpa only [progressionError_modulus_one] using
    (abs_progressionError_le_max (t := N) (T := T) (q := 1) (a := 0)
      hNT (by norm_num) (by norm_num))

/-- The maximal ordinary prime-number estimate inherits the uniform constant
from the distribution hypothesis.
@isnad1 id=ex.2h1v.s6.c294d97447b0 from=translated src=- shape=c9a74b17 vocab=577dc187
-/
theorem MaximalBombieriVinogradov.maximal_psi_error
    (hBV : MaximalBombieriVinogradov) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ t : ℕ, t ≤ 2 * N + 2 →
      |Chebyshev.psi (t : ℝ) - (t : ℝ)| ≤ K * N / (Real.log N) ^ A := by
  obtain ⟨B, _hB, K, hK, N₀, hN₀, hdist⟩ := hBV A hA
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_primaryCutoff_sq_le_BV_range B,
    eventually_ge_atTop N₀] with N hcutoff hN
  have hN1 : 1 ≤ N := by omega
  have hU : 1 ≤ primaryCutoff N := primaryCutoff_pos hN1
  have hUsq : (1 : ℝ) ≤ ((primaryCutoff N ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ primaryCutoff N ^ 2 by nlinarith)
  have hQ : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B :=
    hUsq.trans hcutoff
  have hmax : progressionMaxError (2 * N + 2) 1 ≤ K * N / (Real.log N) ^ A := by
    simpa only [Icc_self, sum_singleton] using hdist N hN 1 (by simpa only [Nat.cast_one] using hQ)
  intro t ht
  exact (abs_psi_sub_nat_le_progressionMaxError t (2 * N + 2) ht).trans hmax

/-- Every fixed logarithmic saving in the ordinary Chebyshev error follows
from modulus one of the existing maximal Bombieri--Vinogradov hypothesis.
@isnad1 id=ex.2h1v.s6.3339f4cef29a from=translated src=- shape=68d3f6a0 vocab=651a66ec
-/
theorem MaximalBombieriVinogradov.psi_error
    (hBV : MaximalBombieriVinogradov) (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤ K * N / (Real.log N) ^ A := by
  obtain ⟨K, hK, herror⟩ := hBV.maximal_psi_error A hA
  exact ⟨K, hK, herror.mono (fun N hN => hN N (by omega))⟩

end TwinPrime.Analytic
