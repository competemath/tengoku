import Tengoku.Twinprime.TwinPrime.Analytic.ContourBudgetAbsorption
import Tengoku.Twinprime.TwinPrime.Analytic.PrincipalStripParameters

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform centered smoothed Siegel--Walfisz

The actual primitive-character contours and the regularized principal contour
share an eventual threshold. All value, nonvanishing, and contour hypotheses
are discharged. The remaining weight is `1 - n / x`.
-/

noncomputable section

open Filter Classical

namespace TwinPrime.Analytic

def centeredWeightedCharacterSum {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  weightedPartialSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x -
    if χ = 1 then (x : ℂ) / 2 else 0

/--
@isnad1 id=le.3h3v.s5.51189461a698 from=translated src=- shape=21487621 vocab=231e6a27
-/
theorem primitiveStripLogDerivativeBudget_nonneg (q : ℕ) (H δ : ℝ)
    (hq : 1 ≤ q) (hH : 0 ≤ H) (hδ : 0 ≤ δ) :
    0 ≤ primitiveStripLogDerivativeBudget q H δ := by
  have hqlog := Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)
  have hHlog := Real.log_nonneg (show 1 ≤ H + 4 by linarith)
  have h16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
  have h5 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
  have h65 := Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)
  unfold primitiveStripLogDerivativeBudget
  positivity

/--
@isnad1 id=le.2h2v.s5.e8dc9a39e05c from=translated src=- shape=6c67d60b vocab=5a06513c
-/
theorem zetaStripLogDerivativeBudget_nonneg (H δ : ℝ) (hH : 0 ≤ H) (hδ : 0 ≤ δ) :
    0 ≤ zetaStripLogDerivativeBudget H δ := by
  have hHlog := Real.log_nonneg (show 1 ≤ H + 4 by linarith)
  have h16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
  have h5 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
  have h65 := Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)
  unfold zetaStripLogDerivativeBudget
  positivity

/--
@isnad1 id=eventual.0h1v.s4.2f2b6cbdc441 from=translated src=- shape=37acfcba vocab=9187980e
-/
theorem eventually_log_rpow_le_self (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ A ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop A (s := 1) (by norm_num)).eventuallyLE
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hb hx
  simpa only [Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx) A),
    abs_of_nonneg (by linarith : 0 ≤ x)] using hb

end TwinPrime.Analytic
