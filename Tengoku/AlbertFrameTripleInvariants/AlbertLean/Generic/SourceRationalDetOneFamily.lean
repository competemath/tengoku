import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualAction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.NormalizedOrbitSection
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms detOneFamily` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms detOneFamily_surjective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms familySourceAut_surjective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms familySourceAut_linear_surjective` (it only prints; the queue checks the axioms of every declaration). -/

/-! A literal sixteen-entry rational family surjecting onto the already
defined determinant-one residual matrices.  This is a parametrization of the
existing group carrier, not a claim about saturation of any frame chart. -/

noncomputable section
namespace AlbertLean.Generic.SourceRationalDetOneFamily

open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.NormalizedOrbitSection
open AlbertLean.Generic.ResidualAction
open AlbertLean.Triality.StructuredCubic

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Rescale an arbitrary invertible four-by-four matrix on the left so that
its determinant becomes one.-/
def scaledMatrix (Z : Mat4 K) : Mat4 K := X0 (Matrix.det Z)⁻¹ * Z

/-- The displayed two-sided inverse of `scaledMatrix`.-/
def scaledMatrixInv (Z : Mat4 K) : Mat4 K :=
  Z⁻¹ * X0 (Matrix.det Z)

private theorem X0_inv_mul_X0 (d : K) (hd : d ≠ 0) :
    X0 d⁻¹ * X0 d = (1 : Mat4 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X0, Matrix.mul_apply, Fin.sum_univ_succ, hd]

private theorem X0_mul_X0_inv (d : K) (hd : d ≠ 0) :
    X0 d * X0 d⁻¹ = (1 : Mat4 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X0, Matrix.mul_apply, Fin.sum_univ_succ, hd]

/-- Every matrix with nonzero determinant gives an actual existing
`DetOneMatrix`, with no quotient or genericity premise.-/
def detOneFamily (Z : Mat4 K) (hZ : Matrix.det Z ≠ 0) : DetOneMatrix K where
  g := scaledMatrix Z
  gInv := scaledMatrixInv Z
  g_mul_gInv := by
    rw [scaledMatrix, scaledMatrixInv, Matrix.mul_assoc,
      ← Matrix.mul_assoc Z Z⁻¹ (X0 (Matrix.det Z)),
      Matrix.mul_nonsing_inv Z (isUnit_iff_ne_zero.mpr hZ),
      Matrix.one_mul, X0_inv_mul_X0 (Matrix.det Z) hZ]
  gInv_mul_g := by
    rw [scaledMatrix, scaledMatrixInv, Matrix.mul_assoc,
      ← Matrix.mul_assoc (X0 (Matrix.det Z)) (X0 (Matrix.det Z)⁻¹) Z,
      X0_mul_X0_inv (Matrix.det Z) hZ, Matrix.one_mul,
      Matrix.nonsing_inv_mul Z (isUnit_iff_ne_zero.mpr hZ)]
  det_g := by
    rw [scaledMatrix, Matrix.det_mul, det_X0]
    exact inv_mul_cancel₀ hZ

private theorem X0_one : X0 (1 : K) = (1 : Mat4 K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X0, Matrix.one_apply]

private theorem nonsing_inv_eq_specified (g : DetOneMatrix K) :
    g.g⁻¹ = g.gInv := by
  calc
    g.g⁻¹ = 1 * g.g⁻¹ := (Matrix.one_mul _).symm
    _ = (g.gInv * g.g) * g.g⁻¹ := by rw [g.gInv_mul_g]
    _ = g.gInv * (g.g * g.g⁻¹) := Matrix.mul_assoc _ _ _
    _ = g.gInv := by
      rw [Matrix.mul_nonsing_inv g.g
        (isUnit_iff_ne_zero.mpr (by simpa [g.det_g])), Matrix.mul_one]

/-- Substituting the sixteen entries of an existing determinant-one matrix
recovers the complete witness, including its specified inverse.
@isnad1 id=eq.0h2v.s5.42ba1a7f1b61 from=translated src=- shape=69281212 vocab=f8e778ba
-/
theorem detOneFamily_surjective (g : DetOneMatrix K) :
    detOneFamily g.g (by simpa [g.det_g]) = g := by
  apply DetOneMatrix.ext
  · simp [detOneFamily, scaledMatrix, g.det_g, X0_one]
  · simp [detOneFamily, scaledMatrixInv, g.det_g,
      nonsing_inv_eq_specified, X0_one]

/-- The family acts through the established genuine source automorphism on
the full source carrier.-/
def familySourceAut (Z : Mat4 K) (hZ : Matrix.det Z ≠ 0) :
    SourceAut (K := K) :=
  sourceAut (detOneFamily Z hZ)

/--
@isnad1 id=eq.0h2v.s5.4978b85749cd from=translated src=- shape=aa7c599d vocab=04106eaf
-/
theorem familySourceAut_surjective (g : DetOneMatrix K) :
    familySourceAut g.g (by simpa [g.det_g]) = sourceAut g := by
  rw [familySourceAut, detOneFamily_surjective]

/--
@isnad1 id=eq.0h3v.s9.c7c5a7e01769 from=translated src=- shape=71b82b93 vocab=ac0f195d
-/
theorem familySourceAut_linear_surjective (g : DetOneMatrix K) (x : JCoord K) :
    (familySourceAut g.g (by simpa [g.det_g])).linear x =
      (sourceAut g).linear x := by
  rw [familySourceAut_surjective]

end AlbertLean.Generic.SourceRationalDetOneFamily
