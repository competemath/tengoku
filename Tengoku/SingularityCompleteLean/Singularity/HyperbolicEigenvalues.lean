import Tengoku.SingularityCompleteLean.Singularity.DilationOrbit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive eigenvalues for a trace greater than two

The roots of X² - T X + 1 are explicit positive reciprocal numbers. Their
larger root determines the positive dilation parameter used for normalization.
-/

noncomputable section
open scoped MatrixGroups

namespace Singularity

/-- The expanding root of the determinant-one characteristic polynomial.-/
def expandingRoot (T : ℝ) : ℝ := (T + Real.sqrt (T ^ 2 - 4)) / 2

/-- The contracting root of the determinant-one characteristic polynomial.-/
def contractingRoot (T : ℝ) : ℝ := (T - Real.sqrt (T ^ 2 - 4)) / 2

/--
@isnad1 id=eq.0h1v.s4.cef60cde9010 from=translated src=- shape=b690c24f vocab=08338578
-/
theorem hyperbolicRoots_sum (T : ℝ) : expandingRoot T + contractingRoot T = T := by
  unfold expandingRoot contractingRoot
  ring

/--
@isnad1 id=eq.1h1v.s5.2a710f38eedc from=translated src=- shape=5b19c518 vocab=f9cdbcfc
-/
theorem hyperbolicRoots_mul {T : ℝ} (hT : 2 < T) :
    expandingRoot T * contractingRoot T = 1 := by
  have hs := Real.sq_sqrt (show 0 ≤ T ^ 2 - 4 by nlinarith)
  unfold expandingRoot contractingRoot
  nlinarith

/--
@isnad1 id=lt.1h1v.s4.9b8ae6409149 from=translated src=- shape=35bd48ee vocab=cd3f5955
-/
theorem expandingRoot_gt_one {T : ℝ} (hT : 2 < T) : 1 < expandingRoot T := by
  unfold expandingRoot
  nlinarith [Real.sqrt_nonneg (T ^ 2 - 4)]

/--
@isnad1 id=lt.1h1v.s4.58e5078ef6d6 from=translated src=- shape=35bd48ee vocab=517c270b
-/
theorem contractingRoot_pos {T : ℝ} (hT : 2 < T) : 0 < contractingRoot T := by
  have hmul := hyperbolicRoots_mul hT
  have hpos := expandingRoot_gt_one hT
  nlinarith

/--
@isnad1 id=eq.1h1v.s4.e1067c0830e1 from=translated src=- shape=55f73129 vocab=1f9dd3df
-/
theorem contractingRoot_eq_inv {T : ℝ} (hT : 2 < T) :
    contractingRoot T = (expandingRoot T)⁻¹ := by
  have hn : expandingRoot T ≠ 0 := ne_of_gt (lt_trans zero_lt_one (expandingRoot_gt_one hT))
  apply (mul_left_cancel₀ hn)
  rw [hyperbolicRoots_mul hT, mul_inv_cancel₀ hn]

/--
@isnad1 id=ne.1h1v.s4.f6fd77070e24 from=translated src=- shape=9c8b14d8 vocab=136d9100
-/
theorem hyperbolicRoots_ne {T : ℝ} (hT : 2 < T) : expandingRoot T ≠ contractingRoot T := by
  intro h
  have hmul := hyperbolicRoots_mul hT
  have hpos := expandingRoot_gt_one hT
  rw [← h] at hmul
  nlinarith

/-- The logarithmic parameter of the expanding eigenvalue is positive.
@isnad1 id=lt.1h1v.s5.40b7a55b32f1 from=translated src=- shape=ce65ae68 vocab=7db3a6dc
-/
theorem hyperbolicParameter_pos {T : ℝ} (hT : 2 < T) : 0 < 2 * Real.log (expandingRoot T) :=
  mul_pos (by norm_num) (Real.log_pos (expandingRoot_gt_one hT))

/-- Converting the expanding eigenvalue to the diagonal matrix parameter.
@isnad1 id=eq.1h1v.s8.e5e586aeb4d1 from=translated src=- shape=7abe7f9d vocab=852d9948
-/
theorem dilationMatrix_log (r : ℝ) (hr : 0 < r) :
    (dilationMatrix (2 * Real.log r) : Matrix (Fin 2) (Fin 2) ℝ) = !![r, 0; 0, r⁻¹] := by
  simp [dilationMatrix, Real.exp_log hr]

end Singularity
