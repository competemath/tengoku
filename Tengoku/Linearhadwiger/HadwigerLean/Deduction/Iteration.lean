import Tengoku.Linearhadwiger.HadwigerLean.Deduction.InitialLocal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Nine iterations of the exponent bootstrap reach a power above four. -/

namespace HadwigerLean.Deduction

open HadwigerLean.Bootstrap

universe u

/-- The logarithmic exponent after `n` bootstrap steps from `1/3`.-/
noncomputable def bootstrapExponent (n : ℕ) : ℝ := ((4 : ℝ) / 3) ^ n / 3

theorem bootstrapExponent_pos (n : ℕ) : 0 < bootstrapExponent n := by
  unfold bootstrapExponent
  positivity

/-- The ninth bootstrap exponent exceeds four.-/
theorem bootstrapExponent_nine_gt_four : 4 < bootstrapExponent 9 := by
  norm_num [bootstrapExponent]

end HadwigerLean.Deduction
