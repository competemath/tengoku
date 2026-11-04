import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Probability
import Tengoku.Seed.Analysis.Calculus.Deriv.Pow
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Scalar continuity, differentiation, and the strict atom-splitting inequality
for the missing-mass objective. -/

namespace EntropyConstrainedMissingMass

/-- Each single-atom contribution is a polynomial, hence globally continuous.-/
theorem continuous_missingMassTerm (t : ℕ) : Continuous (missingMassTerm t) := by
  unfold missingMassTerm
  fun_prop

/-- Splitting a positive atom into two positive atoms strictly increases
missing mass whenever at least one sample is taken.-/
theorem missingMassTerm_split_strict (t : ℕ) (ht : 1 ≤ t) (a ε : ℝ)
    (hε : 0 < ε) (hεa : ε < a) (ha : a ≤ 1) :
    missingMassTerm t a < missingMassTerm t (a - ε) + missingMassTerm t ε := by
  have hbase : 0 ≤ 1 - a := by linarith
  have habase : 1 - a < 1 - (a - ε) := by linarith
  have hεbase : 1 - a < 1 - ε := by linarith
  have hp1 := pow_lt_pow_left₀ habase hbase (by omega : t ≠ 0)
  have hp2 := pow_lt_pow_left₀ hεbase hbase (by omega : t ≠ 0)
  have h1 := mul_lt_mul_of_pos_left hp1 (by linarith : 0 < a - ε)
  have h2 := mul_lt_mul_of_pos_left hp2 hε
  unfold missingMassTerm
  nlinarith

end EntropyConstrainedMissingMass
