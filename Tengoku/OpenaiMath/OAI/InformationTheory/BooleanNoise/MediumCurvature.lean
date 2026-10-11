import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.EntropyBounds
import Tengoku.OpenaiMath.OAI.InformationTheory.BooleanNoise.CurvatureCertificates

namespace OAI

noncomputable section

open Finset Set
open scoped BigOperators

namespace LeanBlast.CourtadeKumar

def curvatureNumeratorCoeff (k : ℕ) : ℝ :=
  1 / (2 * (k : ℝ) + 1) + 1 / (2 * (k : ℝ) + 3)

theorem curvatureNumeratorCoeff_nonneg (k : ℕ) : 0 ≤ curvatureNumeratorCoeff k := by
  unfold curvatureNumeratorCoeff
  positivity

theorem curvatureNumeratorCoeff_antitone : Antitone curvatureNumeratorCoeff := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold curvatureNumeratorCoeff
  exact add_le_add (one_div_le_one_div_of_le (by positivity) (by linarith))
    (one_div_le_one_div_of_le (by positivity) (by linarith))

end LeanBlast.CourtadeKumar

end

end OAI
