import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.TrialitySquares
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Diagonal product entries from the accepted square formula

Polarization obtains these three entries without opening the source adjoint
or its full coordinate multiplication table. They are the entries selected by
the first frame in the public joint-moment ledger.
-/

namespace AlbertLean.Generic.ProductDiagonal

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Residual.TrialitySquares

variable {K : Type*} [Field K] [CharZero K]

theorem sourceSquare_add (x y : JCoord K) :
    sourceSquare (x + y) =
      sourceSquare x + sourceSquare y + (2 : K) • sourceProduct x y := by
  simp only [sourceSquare, sourceProduct_add_left, sourceProduct_add_right,
    sourceProduct_comm y x, two_smul]
  abel

theorem sourceProduct_d1 (x y : JCoord K) :
    (sourceProduct x y).d1 = x.d1 * y.d1 +
      (BS x.s y.s + BC x.c y.c) / 2 := by
  have h := congrArg JCoord.d1 (sourceSquare_add x y)
  simp only [add_d1, smul_d1, smul_eq_mul, sourceSquare_d1,
    add_s, add_c, nS_add, nC_add] at h
  linear_combination -(1 / 2 : K) * h

theorem sourceProduct_d2 (x y : JCoord K) :
    (sourceProduct x y).d2 = x.d2 * y.d2 +
      (BC x.c y.c + BV x.v y.v) / 2 := by
  have h := congrArg JCoord.d2 (sourceSquare_add x y)
  simp only [add_d2, smul_d2, smul_eq_mul, sourceSquare_d2,
    add_c, add_v, nC_add, nV_add] at h
  linear_combination -(1 / 2 : K) * h

theorem sourceProduct_d3 (x y : JCoord K) :
    (sourceProduct x y).d3 = x.d3 * y.d3 +
      (BV x.v y.v + BS x.s y.s) / 2 := by
  have h := congrArg JCoord.d3 (sourceSquare_add x y)
  simp only [add_d3, smul_d3, smul_eq_mul, sourceSquare_d3,
    add_v, add_s, nV_add, nS_add] at h
  linear_combination -(1 / 2 : K) * h

theorem sourceTraceForm_diagonal_left (a b c : K) (x : JCoord K) :
    sourceTraceForm (diagonal a b c) x =
      a * x.d1 + b * x.d2 + c * x.d3 := by
  simp [sourceTraceForm_formula, diagonal]

end AlbertLean.Generic.ProductDiagonal
