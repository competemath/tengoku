import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSBarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact algebra of one MSS barrier update

Mixed coordinate derivatives commute. The logarithmic-derivative update and its
scalar estimate are proved with explicit nonzero denominators.
-/

namespace NoEpsilon.MSSBarrierAlgebra

open MvPolynomial MSSBarrier

/-- The final scalar inequality in the quantitative MSS shift, without dividing by
the potentially zero mixed derivative d.
@isnad1 id=le.5h6v.s7.ffc366b47a6b from=translated src=- shape=c63a92e7 vocab=7172fdac
-/
theorem scalar_shift (δ bnew bold d fnew fold : ℝ)
    (hδ : 0 < δ) (hb : bnew ≤ bold) (hbold : bold ≤ 1 - 1 / δ)
    (hd : d ≤ 0) (htangent : fnew - δ * d ≤ fold) :
    fnew - d / (1 - bnew) ≤ fold := by
  have hb' : bnew ≤ 1 - 1 / δ := hb.trans hbold
  have hinvpos : 0 < 1 / δ := one_div_pos.mpr hδ
  have hden : 0 < 1 - bnew := by linarith
  have hmul : 1 ≤ δ * (1 - bnew) := by
    have h := mul_le_mul_of_nonneg_left hb' hδ.le
    have hid : δ * (1 / δ) = 1 := by field_simp
    nlinarith
  have hinv : 1 / (1 - bnew) ≤ δ := (div_le_iff₀ hden).mpr hmul
  have hterm := mul_le_mul_of_nonneg_right hinv (neg_nonneg.mpr hd)
  simp only [div_eq_mul_inv, one_mul] at hterm ⊢
  nlinarith

end NoEpsilon.MSSBarrierAlgebra
