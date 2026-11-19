import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.Characters
import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Algebra.CharP.Lemmas
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators ComplexConjugate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Absolute value of a nondegenerate Jacobi sum

Mathlib proves

    J(χ,φ) J(χ⁻¹,φ⁻¹) = #F

when `χ`, `φ`, and `χφ` are nontrivial.  For complex characters, inversion
is complex conjugation.  Hence `‖J(χ,φ)‖² = #F`.
-/

omit [DecidableEq F] in
/-- Complex conjugation of a Jacobi sum is the Jacobi sum of the inverse
characters.
@isnad1 id=eq.0h3v.s7.6472467757b9 from=translated src=- shape=26b56280 vocab=8d8a395e
-/
theorem star_jacobiSum
    (χ φ : MulChar F ℂ) :
    star (jacobiSum χ φ) =
      jacobiSum χ⁻¹ φ⁻¹ := by
  simp [jacobiSum, MulChar.star_apply']

omit [DecidableEq F] in
/-- A nondegenerate complex Jacobi sum over `F` has norm `sqrt (#F)`.
@isnad1 id=eq.3h3v.s8.fbb275b77b0a from=translated src=- shape=c6b707dc vocab=58896b55
-/
theorem jacobiSum_norm_eq_sqrt_card
    {χ φ : MulChar F ℂ}
    (hχ : χ ≠ 1)
    (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ =
      Real.sqrt (Fintype.card F : ℝ) := by
  have hFchar : ringChar F ≠ 0 :=
    CharP.ringChar_ne_zero_of_finite F
  have hchar : ringChar ℂ ≠ ringChar F := by
    simpa using (Ne.symm hFchar)
  have hprod :=
    jacobiSum_mul_jacobiSum_inv
      (F := F) (F' := ℂ) hchar hχ hφ hχφ
  have hstar := star_jacobiSum (F := F) χ φ
  rw [← hstar] at hprod
  have hnorm := congrArg norm hprod
  have hsq :
      ‖jacobiSum χ φ‖ ^ 2 =
        (Fintype.card F : ℝ) := by
    simpa [pow_two] using hnorm
  have hq0 : 0 ≤ (Fintype.card F : ℝ) := by
    positivity
  have hsqrt_sq :
      (Real.sqrt (Fintype.card F : ℝ)) ^ 2 =
        (Fintype.card F : ℝ) :=
    Real.sq_sqrt hq0
  have hn0 : 0 ≤ ‖jacobiSum χ φ‖ :=
    norm_nonneg _
  have hs0 :
      0 ≤ Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_nonneg _
  nlinarith

end MagicSquares
