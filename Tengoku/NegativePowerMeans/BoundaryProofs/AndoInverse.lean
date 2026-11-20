import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.Shorting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inverse compression for the Ando verifier

This file isolates the inverse-order step used in the standalone verification
of Ando's compression inequality.
-/

namespace HiaiLimPowerMeans

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {n k : Type*} [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k]

/- The inverse-order theorem uses the standard C⋆-algebra structure on
complex matrices. -/
noncomputable local instance : CStarAlgebra (Matrix k k ℂ) where

/-- Inversion reverses an isometric compression inequality.  This is the
finite-dimensional Choi inequality for the inverse function.-/
theorem inverse_compress_le
    {V : Matrix n k ℂ} (hV : MatrixIsometry V)
    {A : Matrix n n ℂ} (hA : A.PosDef) :
    (compress V A)⁻¹ ≤ compress V A⁻¹ := by
  have hshort : shorted V A ≤ compress V A := by
    have hfeasible := (shorted_variational hV hA).1
    have hlift : V * shorted V A * V.conjTranspose ≤ A := by
      change (A - V * shorted V A * V.conjTranspose).PosSemidef
      exact hfeasible
    have hcompressed := compress_mono V hlift
    have hcompLift :
        compress V (V * shorted V A * V.conjTranspose) = shorted V A := by
      calc
        compress V (V * shorted V A * V.conjTranspose) =
            (V.conjTranspose * V) * shorted V A *
              (V.conjTranspose * V) := by
          simp only [compress, Matrix.mul_assoc]
        _ = shorted V A := by rw [hV, Matrix.one_mul, Matrix.mul_one]
    rw [hcompLift] at hcompressed
    exact hcompressed
  have hshortPos : (shorted V A).PosDef := shorted_posDef hV hA
  have hcompPos : (compress V A).PosDef := compress_posDef hV hA
  have hcompInvPos : (compress V A⁻¹).PosDef := compress_posDef hV hA.inv
  letI : Invertible (shorted V A) := hshortPos.isUnit.invertible
  letI : Invertible (compress V A) := hcompPos.isUnit.invertible
  letI : Invertible (compress V A⁻¹) := hcompInvPos.isUnit.invertible
  have hinv := CStarAlgebra.ringInverse_le_ringInverse
    hshort hshortPos.isStrictlyPositive
  simpa [shorted, Ring.inverse_of_isUnit hshortPos.isUnit,
    Ring.inverse_of_isUnit hcompPos.isUnit,
    Matrix.inv_inv_of_invertible] using hinv

end

end HiaiLimPowerMeans
