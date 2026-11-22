import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Complex
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Elementary complex trigonometric majorants for integral certification. -/
namespace LeanCert.Analysis

/--
@isnad1 id=le.0h1v.s4.b1ce95caf43d from=translated src=- shape=2f36b9fd vocab=b81bbac8
-/
theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (Complex.exp (z*Complex.I)) (Complex.exp (-z*Complex.I))
  rw [← Complex.two_cos, norm_mul] at h
  have h1 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  have h2 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  norm_num [Complex.norm_exp, Complex.mul_re] at h
  linarith

end LeanCert.Analysis
