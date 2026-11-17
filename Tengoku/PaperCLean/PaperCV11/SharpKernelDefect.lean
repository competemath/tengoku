import Tengoku.PaperCLean.PaperCV11.PrimeHarmonic
import Tengoku.PaperCLean.PaperCV11.RankinEnvelope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Paper C v1.1: paper-shaped sharp kernel-defect contract

This file fixes the exact finite counting function `A(X,T)` from Proposition
3.3, rewrites the Rankin envelope in the literal exponential form of equation
(3.4), and supplies its prime-harmonic input from `PrimeHarmonic`.  The full
Proposition 3.3 endpoint name remains reserved until the compact-uniform
consequence (3.5) is also proved.
-/

namespace PaperC
namespace V11
namespace SharpKernelDefect

open scoped BigOperators

open DefectCounting
open LargeOddKernel
open TerminalKernelCount

/-- The exact finite counting function denoted `A(X,T)` in Section 3.2.-/
noncomputable def rankinDefectCount (X T : ℕ) : ℕ :=
  (boundedLargeKernelValues T 1 X).card

/--
@isnad1 id=eq.0h2v.s4.d5d0a54ac078 from=translated src=- shape=136f7181 vocab=2cceecec
-/
@[simp]
theorem rankinDefectCount_eq_card (X T : ℕ) :
    rankinDefectCount X T =
      (boundedLargeKernelValues T 1 X).card :=
  rfl

/-- The explicit correction term in the exponent on the right of (3.4).-/
noncomputable def equationThreeFourEnvelope
    (T : ℕ) (σ C : ℝ) : ℝ :=
  C * (T : ℝ) ^ σ * Real.log (Real.log (3 * (T : ℝ)))

/--
Literal finite form of (3.4), conditional only on the reciprocal-prime bound
that will be supplied by the elementary dyadic-shell argument.
@isnad1 id=le.5h4v.s7.6893d031eb04 from=translated src=- shape=c30c437f vocab=372d4d4e
-/
theorem finite_equation_three_four_of_reciprocal_bound
    (X T : ℕ) {σ C : ℝ}
    (hT : 3 ≤ T) (hTX : T ≤ X)
    (hσpos : 0 < σ) (hσ : σ < 1 / 2)
    (hrecip :
      (∑ p ∈ smallPrimesUpTo T, ((p : ℝ)⁻¹)) ≤
        C * Real.log (Real.log (3 * (T : ℝ)))) :
    (rankinDefectCount X T : ℝ) ≤
      (X : ℝ) * Real.exp
        (-σ * Real.log (X : ℝ) +
          equationThreeFourEnvelope T σ C) := by
  have hXnat : 0 < X :=
    lt_of_lt_of_le (by omega : 0 < 3) (hT.trans hTX)
  have hX : 0 < (X : ℝ) := by
    exact_mod_cast hXnat
  have hfinite :=
    RankinEnvelope.card_kernel_one_cast_le_rankin_exp
      T X hσpos.le hσ.le hrecip
  rw [rankinDefectCount_eq_card]
  refine hfinite.trans_eq ?_
  calc
    (X : ℝ) ^ (1 - σ) *
          Real.exp
            ((T : ℝ) ^ σ *
              (C * Real.log (Real.log (3 * (T : ℝ))))) =
        Real.exp
          (Real.log (X : ℝ) * (1 - σ) +
            equationThreeFourEnvelope T σ C) := by
      rw [Real.rpow_def_of_pos hX, Real.exp_add]
      congr 2
      simp only [equationThreeFourEnvelope]
      ring
    _ = Real.exp
          (Real.log (X : ℝ) +
            (-σ * Real.log (X : ℝ) +
              equationThreeFourEnvelope T σ C)) := by
      congr 1
      ring
    _ = (X : ℝ) * Real.exp
          (-σ * Real.log (X : ℝ) +
            equationThreeFourEnvelope T σ C) := by
      rw [Real.exp_add, Real.exp_log hX]

/-- Equation (3.4) with the explicit absolute constant supplied above.
@isnad1 id=le.4h3v.s6.d291788b79cb from=translated src=- shape=8d850d6b vocab=20407267
-/
theorem finite_equation_three_four
    (X T : ℕ) {σ : ℝ}
    (hT : 3 ≤ T) (hTX : T ≤ X)
    (hσpos : 0 < σ) (hσ : σ < 1 / 2) :
    (rankinDefectCount X T : ℝ) ≤
      (X : ℝ) * Real.exp
        (-σ * Real.log (X : ℝ) +
          equationThreeFourEnvelope T σ 120) := by
  apply finite_equation_three_four_of_reciprocal_bound
    X T hT hTX hσpos hσ
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    PrimeHarmonic.sum_inv_smallPrimesUpTo_real_le_loglog T hT

end SharpKernelDefect
end V11

end PaperC
