import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.AsymptoticInversion
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.HeavyInterpolation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual entropy root at the integer multiplicity ceil(h t). -/

open Filter Set
open scoped Topology Asymptotics
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The integer multiplicity used for the asymptotic lower candidate.-/
def roundedMultiplicity (h t : ℝ) : ℕ := ⌈h * t⌉₊

def roundedTailMass (h t : ℝ) : ℝ := 1 - heavyRoot h (roundedMultiplicity h t)

def roundedEntropyScale (h t : ℝ) : ℝ := h / roundedTailMass h t

/-- Entropy dominates the total light mass times the logarithm of its multiplicity.
@isnad1 id=le.3h2v.s6.a9843bb7b7a5 from=translated src=- shape=366b59d1 vocab=f6266461
-/
theorem heavy_tail_entropy_ge (m L : ℝ) (hm : 0 < m) (hL : 0 < L) (hL1 : L < 1) :
    L * Real.log m ≤ branchEntropy m (1 - L) := by
  have h0 := Real.negMulLog_nonneg hL.le hL1.le
  have h1 := Real.negMulLog_nonneg (show 0 ≤ 1 - L by linarith) (show 1 - L ≤ 1 by linarith)
  rw [heavy_tail_entropy, Real.log_div (ne_of_gt hL) (ne_of_gt hm)]
  simp only [Real.negMulLog] at h0 h1
  nlinarith only [h0, h1]

/-- A uniform first-order bound following from the actual quadratic remainder.
@isnad1 id=le.2h1v.s5.382842daca46 from=translated src=- shape=dafd4951 vocab=1df993e1
-/
theorem entropyTailCorrection_sub_one_bound (L : ℝ) (hL : 0 < L) (hL1 : L < 1) :
    |entropyTailCorrection L - 1| ≤ 2 * L := by
  have h := entropyTailCorrection_remainder_bound L hL hL1
  have ht := abs_sub_le (entropyTailCorrection L) (1 - L / 2) 1
  have he : |(1 - L / 2) - 1| = L / 2 := by
    rw [show (1 - L / 2) - 1 = -(L / 2) by ring, abs_neg, abs_of_pos (by positivity)]
  rw [he] at ht
  nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hL1.le)]

end
end EntropyConstrainedMissingMass
