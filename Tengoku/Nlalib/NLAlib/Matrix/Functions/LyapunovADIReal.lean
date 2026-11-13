import Tengoku.Nlalib.NLAlib.Matrix.Functions.LyapunovADIConvergence
import Tengoku.Nlalib.NLAlib.Matrix.Functions.LyapunovReal
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.ComplexificationUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Real positive-shift ADI and its actual Gramian limit -/
noncomputable section
open Filter
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {n s : Type*} [Fintype n] [Fintype s] [DecidableEq n]

/-- Positive shifts also make the actual real solves nonsingular.-/
theorem isUnit_real_sub_pos_of_hurwitz_complexification (A : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ))
    (p : ℝ) (hp : 0 < p) : IsUnit (A - p • 1) := by
  apply (isUnit_realMatrixComplexification_iff _).mp
  have h := hA.isUnit_sub_pos_smul_one p hp
  have he : (realMatrixComplexification (A - p • 1) : Matrix n n ℂ) =
      realMatrixComplexification A - (p : ℂ) • 1 := by
    simp only [map_sub, map_smul, map_one]
    congr 1
  rw [he]
  exact h

/-- The actual real Cayley matrix extends to the actual complex Cayley matrix.-/
theorem realMatrixComplexification_cayleyTransform (A : Matrix n n ℝ) (p : ℝ)
    (hP : IsUnit (A - p • 1)) :
    (realMatrixComplexification (cayleyTransform A p) : Matrix n n ℂ) =
      cayleyTransform (realMatrixComplexification A) p := by
  unfold cayleyTransform
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [map_mul, realMatrixComplexification_inv hP]
  simp only [map_add, map_sub, map_smul, map_one]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]

/-- Real Cayley powers genuinely decay for every positive shift of a real
matrix with Hurwitz complexified spectrum.-/
theorem tendsto_real_cayleyTransform_pow_zero (A : Matrix n n ℝ)
    (hA : IsHurwitz (realMatrixComplexification A : Matrix n n ℂ))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun j : ℕ => cayleyTransform A p ^ j) atTop (𝓝 0) := by
  apply (tendsto_real_matrix_pow_zero_iff_complex_spectralRadius_lt_one _).mpr
  change spectralRadius ℂ (realMatrixComplexification (cayleyTransform A p) : Matrix n n ℂ) < 1
  rw [realMatrixComplexification_cayleyTransform A p (isUnit_real_sub_pos_of_hurwitz_complexification A hA p hp)]
  exact hA.spectralRadius_cayleyTransform_lt_one p hp

end NLAlib
