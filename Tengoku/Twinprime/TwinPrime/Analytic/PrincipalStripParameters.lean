import Tengoku.Twinprime.TwinPrime.Analytic.SiegelWalfiszStripBudget
import Tengoku.Twinprime.TwinPrime.Analytic.SmoothedPrincipalContour

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal bounds at the common contour width

At conductor one the primitive logarithmic width is twice the zeta width.
The two halvings in the common evaluation width therefore fit inside the
proved principal zero-free rectangle. The principal norm budget is at
most twice the conductor-one primitive budget.
-/

noncomputable section

namespace TwinPrime.Analytic

/--
@isnad1 id=eq.0h1v.s4.503157434277 from=translated src=- shape=ca6a8ef5 vocab=a3fa6db6
-/
theorem primitiveLogZeroFreeWidth_one_eq_twice_zeta (H : ℝ) :
    primitiveLogZeroFreeWidth 1 H = 2 * zetaLogZeroFreeWidth H := by
  unfold primitiveLogZeroFreeWidth zetaLogZeroFreeWidth
  simp only [Nat.cast_one, Real.log_one, add_zero]
  simp only [one_div, mul_inv_rev]
  ring

/--
@isnad1 id=le.0h3v.s6.b11ff870fdc3 from=translated src=- shape=3cfa56d7 vocab=2529d2d1
-/
theorem common_principal_width_le_zeta (ε d H : ℝ) :
    2 * (primitiveZeroFreeRectangleWidth ε d 1 (H + 2) / 2) ≤
      zetaLogZeroFreeWidth (H + 2) := by
  have hw := twice_primitiveZeroFreeRectangleWidth_le_log_width ε d 1 (H + 2)
  rw [primitiveLogZeroFreeWidth_one_eq_twice_zeta] at hw
  linarith

/--
@isnad1 id=le.1h2v.s5.c3f6bdc9ebd0 from=translated src=- shape=02261d0b vocab=0b592df1
-/
theorem zetaStripBudget_le_twice_primitive (H δ : ℝ) (hδ : 0 < δ) :
    zetaStripLogDerivativeBudget H δ ≤ 2 * primitiveStripLogDerivativeBudget 1 H δ := by
  have h65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have h16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have he : 2 * primitiveStripLogDerivativeBudget 1 H δ - zetaStripLogDerivativeBudget H δ =
      (288 * (1 + Real.log 5 / Real.log (6 / 5))) * (1 + Real.log 16) +
        (Real.log 16 / Real.log (6 / 5)) / δ := by
    unfold primitiveStripLogDerivativeBudget zetaStripLogDerivativeBudget
    simp only [Nat.cast_one, Real.log_one, mul_zero, add_zero]
    ring
  have hn : 0 ≤ 2 * primitiveStripLogDerivativeBudget 1 H δ - zetaStripLogDerivativeBudget H δ := by
    rw [he]
    positivity
  linarith

/--
@isnad1 id=and.4h4v.s8.32d90d9103a4 from=translated src=- shape=85d4ca91 vocab=3f58737b
-/
theorem principal_common_strip_width_and_budget (B K d L : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hd : 0 < d) (hL : 1 ≤ L) :
    siegelWalfiszStripWidthConstant B K d * L ^ (-(1 / 2 : ℝ)) ≤
        primitiveZeroFreeRectangleWidth (1 / (2 * B)) d 1 (L ^ K + 2) / 2 ∧
      zetaStripLogDerivativeBudget (L ^ K)
          (primitiveZeroFreeRectangleWidth (1 / (2 * B)) d 1 (L ^ K + 2) / 2) ≤
        (2 * siegelWalfiszStripBudgetConstant B K d) * L := by
  have hqL : ((1 : ℕ) : ℝ) ≤ L ^ B := by simpa using Real.one_le_rpow hL hB.le
  have hw := primitiveZeroFreeRectangleWidth_pos (1 / (2 * B)) d hd 1 (L ^ K + 2)
  refine ⟨siegelWalfiszStripWidthConstant_mul_rpow_le B K d L hB hK hd hL 1 le_rfl hqL, ?_⟩
  apply (zetaStripBudget_le_twice_primitive (L ^ K)
    (primitiveZeroFreeRectangleWidth (1 / (2 * B)) d 1 (L ^ K + 2) / 2) (by positivity)).trans
  have hb := mul_le_mul_of_nonneg_left
    (siegelWalfiszStripBudgetConstant_bound B K d L hB hK hd hL 1 le_rfl hqL)
    (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_assoc] using hb

end TwinPrime.Analytic
