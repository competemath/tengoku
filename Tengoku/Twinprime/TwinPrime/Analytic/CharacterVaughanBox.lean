import Tengoku.Twinprime.TwinPrime.Analytic.CharacterMaximalBilinear
import Tengoku.Twinprime.TwinPrime.Analytic.VaughanBoxCoefficients
import Tengoku.Twinprime.TwinPrime.Analytic.BilinearBoxPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A maximal primitive-character estimate for one Vaughan box

The masked Möbius and divisor coefficients are inserted into the proved
maximal bilinear theorem. Their energies give the box polynomial, which
can then be bounded using real lower bounds on the two side lengths.
The natural masking cutoffs and these real comparison bounds are separate.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The logarithmic factor in the proved primitive-character large sieve.-/
def characterLargeSieveLogFactor (Q : ℕ) : ℝ := 1 + 2 * Real.log ((Q : ℝ) + 1)

/-- The part of the large-sieve constant independent of interval length.-/
def characterLargeSieveOffset (Q : ℕ) : ℝ := (Q : ℝ) ^ 2 * characterLargeSieveLogFactor Q

/--
@isnad1 id=le.0h1v.s3.875b25d28484 from=translated src=- shape=b9369acb vocab=0da1479f
-/
theorem one_le_characterLargeSieveLogFactor (Q : ℕ) : 1 ≤ characterLargeSieveLogFactor Q := by
  have hlog : 0 ≤ Real.log ((Q : ℝ) + 1) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q; linarith)
  unfold characterLargeSieveLogFactor
  linarith

/--
@isnad1 id=le.0h1v.s3.16b825b18eb9 from=translated src=- shape=b9369acb vocab=9c99bf10
-/
theorem characterLargeSieveOffset_nonneg (Q : ℕ) : 0 ≤ characterLargeSieveOffset Q :=
  mul_nonneg (sq_nonneg _) (zero_le_one.trans (one_le_characterLargeSieveLogFactor Q))

/--
@isnad1 id=eq.0h3v.s6.26ce7078acba from=translated src=- shape=c6cbb9f6 vocab=449ac84c
-/
theorem characterLargeSieveConstant_dyadic (Q M k : ℕ) :
    characterLargeSieveConstant Q M (M + 2 ^ k) = (2 : ℝ) ^ k + characterLargeSieveOffset Q := by
  simp [characterLargeSieveConstant, characterLargeSieveOffset, characterLargeSieveLogFactor]

/-- Extract the nonnegative logarithmic coefficient from the two square roots.
@isnad1 id=eq.3h4v.s7.b534cc1d8afb from=translated src=- shape=0cccb474 vocab=1c908215
-/
theorem sqrt_box_energy_mul_eq (M N C L : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hL : 0 ≤ L) :
    Real.sqrt ((M + C) * M) * Real.sqrt ((N + C) * (N * L ^ 2)) =
      L * Real.sqrt (M * N * (M + C) * (N + C)) := by
  rw [← Real.sqrt_mul (mul_nonneg (add_nonneg hM hC) hM)]
  have heq : ((M + C) * M) * ((N + C) * (N * L ^ 2)) =
      L ^ 2 * (M * N * (M + C) * (N + C)) := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]

end TwinPrime.Analytic
