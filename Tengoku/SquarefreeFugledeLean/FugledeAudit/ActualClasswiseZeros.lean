import Tengoku.SquarefreeFugledeLean.FugledeAudit.ActualCommutation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FugledeAudit

open Matrix

noncomputable def spectralPhysicalProjectionMatrix
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i : ZMod q) : Matrix Λ Λ ℂ :=
  normalizedFourierMatrix A Λ *
    coordinateMaskMatrix (fun a : A => (physicalCRT q H a.val).1) i *
    (normalizedFourierMatrix A Λ)ᴴ

/--
@isnad1 id=eq.0h5v.s15.248de1dc274c from=translated src=- shape=069c9604 vocab=0e19c8a8
-/
theorem physical_projection_matrix_to_linear_map
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i : ZMod q) :
    (spectralPhysicalProjectionMatrix q H A Λ i).toEuclideanLin =
      spectralPhysicalProjection q H A Λ i := by
  classical
  simp only [spectralPhysicalProjectionMatrix, Matrix.toLpLin_mul_same,
    coordinate_mask_matrix_to_linear_map, spectralPhysicalProjection, fourierForward, fourierBackward]
  rfl

/--
@isnad1 id=eq.0h7v.s10.b991aa2a437e from=translated src=- shape=67125985 vocab=951dc412
-/
theorem physical_projection_matrix_entry
    (q H : ℕ) [NeZero q] [NeZero H]
    (A Λ : Finset (ZMod (q * H))) (i : ZMod q) (ξ μ : Λ) :
    spectralPhysicalProjectionMatrix q H A Λ i ξ μ =
      ((Real.sqrt (A.card : ℝ) : ℂ)⁻¹ * (Real.sqrt (A.card : ℝ) : ℂ)⁻¹) *
        ∑ a : A, if (physicalCRT q H a.val).1 = i then
          cyclicFourierEntry a.val (ξ.val - μ.val) else 0 := by
  classical
  rw [spectralPhysicalProjectionMatrix, Matrix.mul_apply]
  simp only [coordinateMaskMatrix, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    normalizedFourierMatrix, Matrix.smul_apply, restrictedFourierMatrix,
    smul_eq_mul, star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · rw [← fourier_entry_product_star]
    simp only [Complex.star_def]
    ring
  · simp

end FugledeAudit
