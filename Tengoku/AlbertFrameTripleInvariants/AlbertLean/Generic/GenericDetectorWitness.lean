import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericDeterminantOpen
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParameterFamily

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms chartEval_N` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms acceptedEval_N` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms acceptedEval_detN_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-! The accepted separating witness is an allowed specialization of the
actual nineteen independent base parameters. The four dependent moment
diagonals are recovered from its checked source equations. No determinant
of a numerical 4x4 matrix is expanded. -/

noncomputable section
namespace AlbertLean.Generic.GenericDetectorWitness

open Matrix
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Generic.GenericDeterminantOpen
open AlbertLean.Generic.NestedReciprocalField
open AlbertLean.Generic.WitnessChart
open AlbertLean.Generic.ParameterFamily
open AlbertLean.Generic.LawfulChart

/-- Read exactly the independent coordinates. The normalized convention is
r1=1; that condition is imposed only in the readback theorem.-/
def chartValue (y : ExplicitFrameChart ℚ) : BaseVar → ℚ
  | Sum.inl i => ![y.diagA 0, y.diagA 1, y.diagB 0, y.diagB 1] i
  | Sum.inr (Sum.inl i) => ![y.z1, y.r2, y.z2] i
  | Sum.inr (Sum.inr ij) => matrixM y ij.1.1 ij.1.2

def chartEval (y : ExplicitFrameChart ℚ) : R ℚ →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (chartValue y)

@[simp] theorem chartEval_dA0 (y : ExplicitFrameChart ℚ) : chartEval y (dA0 ℚ) = y.diagA 0 := by
  simp [chartEval, dA0, diagX, x, chartValue]

@[simp] theorem chartEval_dA1 (y : ExplicitFrameChart ℚ) : chartEval y (dA1 ℚ) = y.diagA 1 := by
  simp [chartEval, dA1, diagX, x, chartValue]

@[simp] theorem chartEval_dB0 (y : ExplicitFrameChart ℚ) : chartEval y (dB0 ℚ) = y.diagB 0 := by
  simp [chartEval, dB0, diagX, x, chartValue]

@[simp] theorem chartEval_dB1 (y : ExplicitFrameChart ℚ) : chartEval y (dB1 ℚ) = y.diagB 1 := by
  simp [chartEval, dB1, diagX, x, chartValue]

@[simp] theorem chartEval_a (y : ExplicitFrameChart ℚ) : chartEval y (a ℚ) = y.z1 := by
  simp [chartEval, a, gaugeX, x, chartValue]

@[simp] theorem chartEval_b (y : ExplicitFrameChart ℚ) : chartEval y (b ℚ) = y.r2 := by
  simp [chartEval, b, gaugeX, x, chartValue]

@[simp] theorem chartEval_c (y : ExplicitFrameChart ℚ) : chartEval y (c ℚ) = y.z2 := by
  simp [chartEval, c, gaugeX, x, chartValue]

@[simp] theorem chartEval_offX (y : ExplicitFrameChart ℚ) (ij : OffDiagonal) :
    chartEval y (offX ℚ ij) = matrixM y ij.1.1 ij.1.2 := by
  simp [chartEval, offX, x, chartValue]

theorem chartEval_off (y : ExplicitFrameChart ℚ) (i j : Fin 4) (h : i ≠ j) :
    chartEval y (off ℚ i j) = matrixM y i j := by
  simp only [off, dite_eq_right h, chartEval_offX]

section Readback
variable (y : ExplicitFrameChart ℚ) (hr : y.r1 = 1)
  (heq : EquationsVanish (explicitFrameEquationValues y))

include heq in
private theorem chartEval_dA2 : chartEval y (dA2 ℚ) = y.diagA 2 := by
  have ht := heq.1
  change y.diagA 0 + y.diagA 1 + y.diagA 2 = 0 at ht
  simp only [dA2, map_sub, map_neg, chartEval_dA0, chartEval_dA1]
  linear_combination -ht

include heq in
private theorem chartEval_dB2 : chartEval y (dB2 ℚ) = y.diagB 2 := by
  have ht := heq.2.2.2.1
  change y.diagB 0 + y.diagB 1 + y.diagB 2 = 0 at ht
  simp only [dB2, map_sub, map_neg, chartEval_dB0, chartEval_dB1]
  linear_combination -ht

include heq in
theorem chartEval_PA : chartEval y (PA ℚ) = y.diagA 1 - y.diagA 2 := by
  rw [PA, map_sub, chartEval_dA1, chartEval_dA2 y heq]

include heq in
theorem chartEval_PB : chartEval y (PB ℚ) = y.diagB 1 - y.diagB 2 := by
  rw [PB, map_sub, chartEval_dB1, chartEval_dB2 y heq]

include hr heq in
private theorem chartEval_SA :
    chartEval y (SA ℚ) = matrixM y 0 0 + matrixM y 2 2 := by
  have hs := heq.2.1
  change y.diagA 0 * y.diagA 1 + y.diagA 0 * y.diagA 2 +
    y.diagA 1 * y.diagA 2 - y.r1 * y.z1 - matrixM y 0 0 - matrixM y 2 2 + 1 = 0 at hs
  rw [hr, one_mul] at hs
  simp only [SA, map_add, map_sub, map_mul, map_one,
    chartEval_dA0, chartEval_dA1, chartEval_dA2 y heq, chartEval_a]
  linear_combination hs

include heq in
private theorem chartEval_SB :
    chartEval y (SB ℚ) = matrixM y 1 1 + matrixM y 3 3 := by
  have hs := heq.2.2.2.2.1
  change y.diagB 0 * y.diagB 1 + y.diagB 0 * y.diagB 2 +
    y.diagB 1 * y.diagB 2 - y.r2 * y.z2 - matrixM y 1 1 - matrixM y 3 3 + 1 = 0 at hs
  simp only [SB, map_add, map_sub, map_mul, map_one,
    chartEval_dB0, chartEval_dB1, chartEval_dB2 y heq, chartEval_b, chartEval_c]
  linear_combination hs

include hr heq in
private theorem chartEval_TA : chartEval y (TA ℚ) =
    y.diagA 1 * matrixM y 0 0 + y.diagA 2 * matrixM y 2 2 := by
  have hn := heq.2.2.1
  change y.diagA 0 * y.diagA 1 * y.diagA 2 - y.diagA 0 * (y.r1 * y.z1) -
    y.diagA 1 * matrixM y 0 0 - y.diagA 2 * matrixM y 2 2 +
    y.r1 * matrixM y 0 2 + y.z1 * matrixM y 2 0 = 0 at hn
  rw [hr, one_mul, one_mul] at hn
  simp only [TA, map_add, map_sub, map_mul, chartEval_dA0, chartEval_dA1,
    chartEval_dA2 y heq, chartEval_a,
    chartEval_off y 0 2 (by decide), chartEval_off y 2 0 (by decide)]
  linear_combination hn

include heq in
private theorem chartEval_TB : chartEval y (TB ℚ) =
    y.diagB 1 * matrixM y 1 1 + y.diagB 2 * matrixM y 3 3 := by
  have hn := heq.2.2.2.2.2
  change y.diagB 0 * y.diagB 1 * y.diagB 2 - y.diagB 0 * (y.r2 * y.z2) -
    y.diagB 1 * matrixM y 1 1 - y.diagB 2 * matrixM y 3 3 +
    y.r2 * matrixM y 1 3 + y.z2 * matrixM y 3 1 = 0 at hn
  simp only [TB, map_add, map_sub, map_mul, chartEval_dB0, chartEval_dB1,
    chartEval_dB2 y heq, chartEval_b, chartEval_c,
    chartEval_off y 1 3 (by decide), chartEval_off y 3 1 (by decide)]
  linear_combination hn

include hr heq in
theorem chartEval_nA0 : chartEval y (nA0 ℚ) =
    (y.diagA 1 - y.diagA 2) * matrixM y 0 0 := by
  rw [nA0, map_sub, map_mul, chartEval_TA y hr heq,
    chartEval_dA2 y heq, chartEval_SA y hr heq]
  ring

include hr heq in
theorem chartEval_nA2 : chartEval y (nA2 ℚ) =
    (y.diagA 1 - y.diagA 2) * matrixM y 2 2 := by
  rw [nA2, map_sub, map_mul, chartEval_PA y heq,
    chartEval_SA y hr heq, chartEval_nA0 y hr heq]
  ring

include heq in
theorem chartEval_nB1 : chartEval y (nB1 ℚ) =
    (y.diagB 1 - y.diagB 2) * matrixM y 1 1 := by
  rw [nB1, map_sub, map_mul, chartEval_TB y heq,
    chartEval_dB2 y heq, chartEval_SB y heq]
  ring

include heq in
theorem chartEval_nB3 : chartEval y (nB3 ℚ) =
    (y.diagB 1 - y.diagB 2) * matrixM y 3 3 := by
  rw [nB3, map_sub, map_mul, chartEval_PB y heq,
    chartEval_SB y heq, chartEval_nB1 y heq]
  ring

include hr heq in
/-- Cleared readback: no division and no nonzero-pivot premise is needed.-/
theorem chartEval_N : (N ℚ).map (chartEval y) =
    Matrix.diagonal ![y.diagA 1 - y.diagA 2, y.diagB 1 - y.diagB 2,
      y.diagA 1 - y.diagA 2, y.diagB 1 - y.diagB 2] * matrixM y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.diagonal_mul, chartEval_PA y heq, chartEval_PB y heq,
      chartEval_nA0 y hr heq, chartEval_nA2 y hr heq,
      chartEval_nB1 y heq, chartEval_nB3 y heq]

end Readback

/-- This is the separating witness, not GenericDeterminantOpen.witnessEval.-/
def acceptedEval : R ℚ →+* ℚ := chartEval witnessChart1

private theorem witness_pivotA :
    witnessChart1.diagA 1 - witnessChart1.diagA 2 = (-7 / 3 : ℚ) := by
  change (-1 : ℚ) - 4 / 3 = -7 / 3
  norm_num

private theorem witness_pivotB :
    witnessChart1.diagB 1 - witnessChart1.diagB 2 = (-7 / 3 : ℚ) := by
  change (-1 : ℚ) - 4 / 3 = -7 / 3
  norm_num

@[simp] theorem acceptedEval_PA : acceptedEval (PA ℚ) = (-7 / 3 : ℚ) :=
  (chartEval_PA witnessChart1 witnessChart1_equations).trans witness_pivotA

@[simp] theorem acceptedEval_PB : acceptedEval (PB ℚ) = (-7 / 3 : ℚ) :=
  (chartEval_PB witnessChart1 witnessChart1_equations).trans witness_pivotB

theorem acceptedEval_PA_ne_zero : acceptedEval (PA ℚ) ≠ 0 := by
  rw [acceptedEval_PA]
  norm_num

theorem acceptedEval_PB_ne_zero : acceptedEval (PB ℚ) ≠ 0 := by
  rw [acceptedEval_PB]
  norm_num

@[simp] theorem acceptedEval_a : acceptedEval (a ℚ) = 0 := chartEval_a witnessChart1
@[simp] theorem acceptedEval_b : acceptedEval (b ℚ) = 0 := chartEval_b witnessChart1
@[simp] theorem acceptedEval_c : acceptedEval (c ℚ) = 1 := chartEval_c witnessChart1

/-- The evaluated cleared matrix is a nonsingular diagonal scaling of the
already accepted residual moment.-/
theorem acceptedEval_N : (N ℚ).map acceptedEval =
    Matrix.diagonal ![(-7 / 3 : ℚ), -7 / 3, -7 / 3, -7 / 3] * parameterMoment := by
  have h := chartEval_N witnessChart1 (by rfl) witnessChart1_equations
  rw [witness_pivotA, witness_pivotB, matrixM_eq_moment_residualPairOfChart] at h
  exact h

/-- Determinant multiplicativity uses only the four diagonal factors and the
previously checked determinant of parameterMoment.-/
theorem acceptedEval_detN :
    acceptedEval (Matrix.det (N ℚ)) = (-7 / 3 : ℚ) ^ 4 * witnessScale := by
  rw [RingHom.map_det]
  change Matrix.det ((N ℚ).map acceptedEval) = _
  rw [acceptedEval_N, Matrix.det_mul, Matrix.det_diagonal, parameterMoment_det]
  norm_num [Fin.prod_univ_succ]

theorem acceptedEval_detN_ne_zero : acceptedEval (Matrix.det (N ℚ)) ≠ 0 := by
  rw [acceptedEval_detN]
  exact mul_ne_zero (pow_ne_zero 4 (by norm_num)) witnessScale_ne_zero

end AlbertLean.Generic.GenericDetectorWitness
