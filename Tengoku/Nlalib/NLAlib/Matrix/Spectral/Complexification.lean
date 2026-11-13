import Tengoku.Seed.Analysis.Matrix.Spectrum
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real matrices inside `𝕜` matrices

The entrywise extension `realMatrixComplexification : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n 𝕜`
preserves and reflects the Loewner order, positive (semi)definiteness and the inverse, and
commutes with the continuous functional calculus. Real matrix results are transported from the
C⋆-algebra `Matrix n n ℂ` through it (atlas `loewner-heinz-real`).
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

section RealExtension

open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] [DecidableEq n]

/-- Entrywise extension of real matrices to `𝕜` (`ℝ` or `ℂ`) as a real star algebra
homomorphism. Source: the canonical scalar embedding; supports `loewner-heinz-real`.-/
def realMatrixComplexification : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n 𝕜 :=
  { (Algebra.ofId ℝ 𝕜).mapMatrix with
    map_star' := by intro A; ext i j; simp }

/-- The embedding acts on each matrix entry by the canonical real scalar map.
Source: the canonical scalar embedding; supports `loewner-heinz-real`.
@isnad1 id=eq.0h3v.s8.94ba81dd1136 from=translated src=- shape=6bdd2b16 vocab=dc1d741a
-/
@[simp] theorem realMatrixComplexification_apply (A : Matrix n n ℝ) :
    (realMatrixComplexification A : Matrix n n 𝕜) = A.map (algebraMap ℝ 𝕜) := rfl

/-- The extension to `𝕜` preserves and reflects positive semidefiniteness.
Source: the quadratic form on embedded real vectors and star-order preservation;
supports `loewner-heinz-real`.
@isnad1 id=iff.0h3v.s8.1f1c6df7f87f from=translated src=- shape=2b11612b vocab=6b399a58
-/
theorem posSemidef_realMatrixComplexification_iff (A : Matrix n n ℝ) :
    (realMatrixComplexification A : Matrix n n 𝕜).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro hA
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · exact (Matrix.isHermitian_map_iff (fun x => by simp)
        (algebraMap ℝ 𝕜).injective).mp hA.isHermitian
    · intro x
      have h := hA.re_dotProduct_nonneg (fun i => algebraMap ℝ 𝕜 (x i))
      simpa [Matrix.mulVec, dotProduct, realMatrixComplexification_apply, ← map_mul,
        ← map_sum] using h
  · intro hA
    apply Matrix.nonneg_iff_posSemidef.mp
    have h : (realMatrixComplexification (0 : Matrix n n ℝ) : Matrix n n 𝕜) ≤
        realMatrixComplexification A :=
      map_rel (realMatrixComplexification (𝕜 := 𝕜) (n := n)) hA.nonneg
    rwa [map_zero] at h

/-- The extension to `𝕜` preserves and reflects Loewner inequalities.
Source: the positive-semidefinite difference criterion; supports `loewner-heinz-real`.
@isnad1 id=iff.0h4v.s9.3faab802dc38 from=translated src=- shape=4f6bc775 vocab=9b00822a
-/
theorem realMatrixComplexification_le_iff (A B : Matrix n n ℝ) :
    (realMatrixComplexification A : Matrix n n 𝕜) ≤ realMatrixComplexification B ↔ A ≤ B := by
  rw [Matrix.le_iff, ← map_sub, posSemidef_realMatrixComplexification_iff, Matrix.le_iff]

/-- The entrywise extension to `𝕜` is continuous.
Source: finite-dimensional real linearity; supports `loewner-heinz-real`.
@isnad1 id=continuo.0h2v.s8.8c9ccc0c4da7 from=translated src=- shape=54de4a1c vocab=05288ffd
-/
theorem continuous_realMatrixComplexification :
    Continuous (realMatrixComplexification : Matrix n n ℝ → Matrix n n 𝕜) :=
  (realMatrixComplexification (𝕜 := 𝕜) (n := n)).toLinearMap.continuous_of_finiteDimensional

/-- Every scalar functional calculus of a real symmetric matrix commutes with the extension
to `𝕜`. Its finite spectrum makes every scalar function continuous on the spectrum.
Source: Mathlib `StarAlgHom.map_cfc`; supports `loewner-heinz-real`.
@isnad1 id=eq.1h4v.s10.f45697698533 from=translated src=- shape=99a17705 vocab=7c26fa8a
-/
theorem realMatrixComplexification_cfc (f : ℝ → ℝ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    (realMatrixComplexification (cfc f A) : Matrix n n 𝕜) =
      cfc f (realMatrixComplexification A : Matrix n n 𝕜) := by
  exact (realMatrixComplexification (𝕜 := 𝕜) (n := n)).map_cfc f A
    (A.finite_real_spectrum.continuousOn f) continuous_realMatrixComplexification hA
    (hA.map (algebraMap ℝ 𝕜) (fun x => by simp))

/-- The extension to `𝕜` preserves positive definiteness, including empty dimensions.
Source: positivity and preservation of units; supports `loewner-heinz-real`.
@isnad1 id=posdef.1h3v.s8.0bf8a2782a37 from=translated src=- shape=0c819690 vocab=c8e4e948
-/
theorem posDef_realMatrixComplexification {A : Matrix n n ℝ} (hA : A.PosDef) :
    (realMatrixComplexification A : Matrix n n 𝕜).PosDef := by
  apply (posSemidef_realMatrixComplexification_iff A).mpr hA.posSemidef |>.posDef_iff_isUnit.mpr
  exact hA.isUnit.map realMatrixComplexification

/-- The extension to `𝕜` commutes with the ordinary inverse on nonsingular matrices.
Source: preservation of the two inverse identities; supports `loewner-heinz-real`.
@isnad1 id=eq.1h3v.s9.421e2eea4292 from=translated src=- shape=8b63b463 vocab=559851c6
-/
theorem realMatrixComplexification_inv {A : Matrix n n ℝ} (hA : IsUnit A) :
    (realMatrixComplexification A⁻¹ : Matrix n n 𝕜) = (realMatrixComplexification A)⁻¹ := by
  have hAc : IsUnit (realMatrixComplexification A : Matrix n n 𝕜) :=
    hA.map realMatrixComplexification
  have hCancel : (realMatrixComplexification A : Matrix n n 𝕜) *
      realMatrixComplexification A⁻¹ = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA), map_one]
  calc
    (realMatrixComplexification A⁻¹ : Matrix n n 𝕜) =
        (realMatrixComplexification A)⁻¹ *
          (realMatrixComplexification A * realMatrixComplexification A⁻¹) := by
      rw [← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hAc), Matrix.one_mul]
    _ = (realMatrixComplexification A)⁻¹ := by rw [hCancel, Matrix.mul_one]

end RealExtension

end NLAlib
