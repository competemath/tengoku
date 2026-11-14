import Tengoku.Twinprime.TwinPrime.Analytic.LogarithmicCorrection
import Tengoku.Twinprime.TwinPrime.Analytic.BilinearCutoffShift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Keeping the finite classical main terms in the correlation

The center retains the actual finite Möbius/totient coefficients. Its error
therefore involves only the three progression errors, without replacing those
coefficients by their limits. The same convention cancels the main coefficient
of a right-cutoff change exactly.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The finite mixed, logarithmic, and Type I main terms, with their exact signs.-/
def classicalCorrelationCenter (U V X : ℕ) : ℝ :=
  (X : ℝ) * smoothedTotientSum U +
    oddMoebiusTotientSum U * logarithmicMass U X - (X : ℝ) * totientTypeIMain U V

/-- The discrepancy from the centered bilinear expression is exactly the sum
of the three classical progression remainders.-/
theorem correlation_sub_bilinear_add_classicalCenter_eq (U V X : ℕ)
    (hU : 0 < U) (hV : V ≤ X) :
    W2 X - (bilinearTerm U V X + classicalCorrelationCenter U V X) =
      (mixedCorrelation U X - (X : ℝ) * smoothedTotientSum U) +
      (logarithmicCorrection U X -
        oddMoebiusTotientSum U * logarithmicMass U X) -
      (typeITerm U V X - (X : ℝ) * totientTypeIMain U V) := by
  rw [correlation_decomposition U V X hU hV]
  unfold classicalCorrelationCenter typeICorrection
  ring

/-- Centering retains the precise Type I remainder under a right-cutoff change.-/
theorem centered_bilinear_cutoff_shift_eq (U V W X : ℕ)
    (hV : V ≤ X) (hW : W ≤ X) :
    (bilinearTerm U V X + classicalCorrelationCenter U V X) -
        (bilinearTerm U W X + classicalCorrelationCenter U W X) =
      (typeITerm U V X - (X : ℝ) * totientTypeIMain U V) -
        (typeITerm U W X - (X : ℝ) * totientTypeIMain U W) := by
  have h := bilinearTerm_sub_eq_typeITerm_sub U V W X hV hW
  unfold classicalCorrelationCenter
  linarith

end TwinPrime.Analytic
