import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericNormalizedFrameChart
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamilyFixedBranch

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms moment_parameters` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms determinant_moment` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms openParameters` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixed_difference_values` (it only prints; the queue checks the axioms of every declaration). -/

/-! One fully explicit nonzero point of every final normalized-chart open.
No generic-open hypothesis is assumed. Its inverse-image lift needs only
a square root of -1: the orientation and first lift roots are 1 and 2. -/
noncomputable section
namespace AlbertLean.Generic.SourceNormalizationOpenWitness

open AlbertLean.Generic.GenericNormalizedFrameChart
open AlbertLean.Triality ExteriorSix CoordinateTensor
open SourceVectorPairDephase RationalEvenFamilyFixedBranch

universe u
variable (K : Type u) [Field K] [CharZero K]

def parameters : Parameters K where
  dA0 := 0
  dA1 := 1
  dB0 := 0
  dB1 := 1
  a := 1
  b := 1
  c := 2
  offDiag _ _ := 0
  Delta := 1

theorem moment_parameters : moment (parameters K) =
    Matrix.diagonal ![-(1/2 : K), -1, -(1/2 : K), -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [moment, parameters, m00, m11, m22, m33,
      normWeightedA, normWeightedB, spurSumA, spurSumB,
      pivotA, pivotB, dA2, dB2, rawOffDiag, Matrix.diagonal]

theorem determinant_moment : Matrix.det (moment (parameters K)) = (1/4 : K) := by
  rw [moment_parameters, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

def openParameters : OpenParameters K where
  toParameters := parameters K
  pivotA_ne := by norm_num [pivotA, dA2, parameters]
  pivotB_ne := by norm_num [pivotB, dB2, parameters]
  Delta_ne := by norm_num [parameters]
  detMoment_ne := by rw [determinant_moment]; norm_num
  branch_ne := by rw [determinant_moment]; norm_num [parameters]

/-- These six values certify all additional V-normalization and rational
family pivots at the same point.-/
theorem fixed_difference_values :
    nV (targetFirst (1 : K)) = 1 ∧
    nV (targetRemainder (1 : K) 3 1) = -(1/4 : K) ∧
    (differenceB1 (1 : K)).r = -2 ∧
    nV (differenceB1 (1 : K)) = 4 ∧
    (differenceB2 (1 : K) 3 1).r = 1 ∧
    nV (differenceB2 (1 : K) 3 1) = -1 := by
  rw [targetFirst_norm, targetRemainder_norm 1 3 1 (by norm_num),
    differenceB1_r, differenceB1_norm,
    differenceB2_r 1 3 1 (by norm_num),
    differenceB2_norm 1 3 1 (by norm_num)]
  norm_num

end AlbertLean.Generic.SourceNormalizationOpenWitness
