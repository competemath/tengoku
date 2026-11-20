/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.L1OperatorsSpace
import Tengoku.Seed.Analysis.CStarAlgebra.Matrix
import Tengoku.Seed.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The matrix dilation on `L¹(ℝ^d)`

Home: none (needs no citation: a bridging reformulation of `L1OperatorsSpace`'s linear dilation
in matrix terms — `matEquiv`'s inverse and determinant read off `Matrix.toEuclideanCLM`'s own
ring-hom and `LinearMap.det` lemmas, not a theorem of its own)

Q-0332 (SSL-5). `ScaleSpaceCore.L1OperatorsSpace` indexes the dilation by `A : E ≃L[ℝ] E`; Paper VII
writes its operators with matrices, `A : Matrix (Fin d) (Fin d) ℝ` acting on
`EuclideanSpace ℝ (Fin d)` through `Matrix.toEuclideanCLM`, with the representative
`|det A|⁻¹ f(A⁻¹ x)` read with the matrix inverse and the matrix determinant. This file is that
reading: `matEquiv A` is the equivalence of an invertible matrix, its inverse is
`toEuclideanCLM A⁻¹` and its determinant is `A.det`, so `D_A`'s representative and the relational
intertwining of `intertwines_iff_dilL1E` are stated on the nose in Paper VII's terms.
-/

namespace ScaleSpace

open MeasureTheory Matrix

variable {d : ℕ}

/-- The continuous linear equivalence of `ℝ^d` given by an invertible matrix, acting through
`Matrix.toEuclideanCLM`.-/
noncomputable def matEquiv (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearEquiv.equivOfInverse (toEuclideanCLM (𝕜 := ℝ) A)
    (toEuclideanCLM (𝕜 := ℝ) A⁻¹)
    (fun x => by
      change (toEuclideanCLM (𝕜 := ℝ) A⁻¹ * toEuclideanCLM (𝕜 := ℝ) A) x = x
      rw [← map_mul, nonsing_inv_mul A hA, map_one]
      rfl)
    (fun x => by
      change (toEuclideanCLM (𝕜 := ℝ) A * toEuclideanCLM (𝕜 := ℝ) A⁻¹) x = x
      rw [← map_mul, mul_nonsing_inv A hA, map_one]
      rfl)

@[simp] lemma matEquiv_apply (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (x : EuclideanSpace ℝ (Fin d)) : matEquiv A hA x = toEuclideanCLM (𝕜 := ℝ) A x := rfl

@[simp] lemma matEquiv_symm_apply (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (x : EuclideanSpace ℝ (Fin d)) :
    (matEquiv A hA).symm x = toEuclideanCLM (𝕜 := ℝ) A⁻¹ x := rfl

/-- The determinant of `matEquiv A` is the matrix determinant.-/
lemma det_matEquiv (A : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    LinearMap.det ((matEquiv A hA : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = A.det := by
  change LinearMap.det (Matrix.toLin (PiLp.basisFun _ _ _) (PiLp.basisFun _ _ _) A) = A.det
  exact LinearMap.det_toLin _ A

/-- `matEquiv (A B) = matEquiv A ∘ matEquiv B`.-/
lemma matEquiv_mul (A B : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    matEquiv (A * B) (by rw [det_mul]; exact hA.mul hB)
      = (matEquiv B hB).trans (matEquiv A hA) := by
  refine ContinuousLinearEquiv.ext (funext fun x => ?_)
  change toEuclideanCLM (𝕜 := ℝ) (A * B) x
    = toEuclideanCLM (𝕜 := ℝ) A (toEuclideanCLM (𝕜 := ℝ) B x)
  rw [map_mul]
  rfl

/-- `D_A D_B = D_{AB}` for matrices.-/
theorem dilL1E_matEquiv_comp (A B : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det)
    (hB : IsUnit B.det) :
    (dilL1E (matEquiv A hA)).comp (dilL1E (matEquiv B hB))
      = dilL1E (matEquiv (A * B) (by rw [det_mul]; exact hA.mul hB)) := by
  rw [dilL1E_comp, matEquiv_mul]

/-- An orthogonal matrix has `|det Q| = 1`.-/
lemma abs_det_of_transpose_mul_self {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) :
    |Q.det| = 1 := by
  have h : Q.det * Q.det = 1 := by
    have := congrArg Matrix.det hQ
    rwa [det_mul, det_transpose, det_one] at this
  have h2 : |Q.det| * |Q.det| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith [abs_nonneg Q.det]

lemma isUnit_det_of_transpose_mul_self {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Qᵀ * Q = 1) :
    IsUnit Q.det :=
  isUnit_iff_ne_zero.mpr fun h0 => by
    have := abs_det_of_transpose_mul_self hQ
    rw [h0, abs_zero] at this
    exact zero_ne_one this

end ScaleSpace
