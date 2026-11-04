import Tengoku.Pi2Lean.Row12.BetaMoments
import Tengoku.Seed.Algebra.BigOperators.Intervals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.betaNormalizer_one_sub` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaNormalizer_one_sixth` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaNormalizer_one_third_sq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaNormalizer_one_half` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.fiveBetaNormalizer_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.fiveBetaNormalizer_pos` (it only prints; the queue checks the axioms of every declaration). -/

namespace Row12

noncomputable def betaNormalizer (a : ℝ) : ℝ :=
  Real.Gamma a * Real.Gamma (1 - a)

noncomputable def fiveBetaNormalizer : ℝ :=
  ∏ j ∈ Finset.Icc (1 : ℕ) 5, betaNormalizer ((j : ℝ) / 6)

/--
@isnad1 id=eq.0h1v.s4.f60b179e839b from=translated src=- shape=0d0922af vocab=4e013b59
-/
theorem betaNormalizer_one_sub (a : ℝ) :
    betaNormalizer (1 - a) = betaNormalizer a := by
  unfold betaNormalizer
  rw [show 1 - (1 - a) = a by ring]
  exact mul_comm _ _

/--
@isnad1 id=eq.0h0v.s5.a6a2cb951f17 from=translated src=- shape=e3ed033b vocab=743ade5b
-/
theorem betaNormalizer_one_sixth : betaNormalizer (1 / 6) = 2 * Real.pi := by
  rw [betaNormalizer, Real.Gamma_mul_Gamma_one_sub,
    show Real.pi * (1 / 6) = Real.pi / 6 by ring, Real.sin_pi_div_six]
  ring

/--
@isnad1 id=eq.0h0v.s6.0055b344333f from=translated src=- shape=421b6d99 vocab=40e6e9a5
-/
theorem betaNormalizer_one_third_sq :
    betaNormalizer (1 / 3) ^ 2 = 4 * Real.pi ^ 2 / 3 := by
  rw [betaNormalizer, Real.Gamma_mul_Gamma_one_sub,
    show Real.pi * (1 / 3) = Real.pi / 3 by ring, Real.sin_pi_div_three,
    div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

/--
@isnad1 id=eq.0h0v.s4.46bd0fc927ef from=translated src=- shape=fd0fe780 vocab=b1a13925
-/
theorem betaNormalizer_one_half : betaNormalizer (1 / 2) = Real.pi := by
  rw [betaNormalizer, Real.Gamma_mul_Gamma_one_sub,
    show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two, div_one]

/--
@isnad1 id=eq.0h0v.s5.df094f7d67e0 from=translated src=- shape=75574061 vocab=fc62ebd9
-/
theorem fiveBetaNormalizer_eq : fiveBetaNormalizer = 16 * Real.pi ^ 5 / 3 := by
  have h4 : betaNormalizer (2 / 3) = betaNormalizer (1 / 3) := by
    rw [show (2 / 3 : ℝ) = 1 - 1 / 3 by norm_num, betaNormalizer_one_sub]
  have h5 : betaNormalizer (5 / 6) = betaNormalizer (1 / 6) := by
    rw [show (5 / 6 : ℝ) = 1 - 1 / 6 by norm_num, betaNormalizer_one_sub]
  calc
    fiveBetaNormalizer =
        betaNormalizer (1 / 6) * betaNormalizer (1 / 3) * betaNormalizer (1 / 2) *
          betaNormalizer (1 / 3) * betaNormalizer (1 / 6) := by
      norm_num [fiveBetaNormalizer, Finset.prod_Icc_succ_top]
      rw [h4, h5]
    _ = betaNormalizer (1 / 6) ^ 2 * betaNormalizer (1 / 3) ^ 2 *
        betaNormalizer (1 / 2) := by ring
    _ = 16 * Real.pi ^ 5 / 3 := by
      rw [betaNormalizer_one_sixth, betaNormalizer_one_third_sq, betaNormalizer_one_half]
      ring

/--
@isnad1 id=lt.0h0v.s3.d949ac51a0ff from=translated src=- shape=ff3a10fc vocab=8bc1b39e
-/
theorem fiveBetaNormalizer_pos : 0 < fiveBetaNormalizer := by
  rw [fiveBetaNormalizer_eq]
  positivity

end Row12

