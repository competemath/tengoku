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

/--
@isnad1 id=eq.0h1v.s6.2009553f0761 from=translated src=- shape=4ab1a778 vocab=035fb5b6
-/
@[simp] theorem chartEval_dA0 (y : ExplicitFrameChart ℚ) : chartEval y (dA0 ℚ) = y.diagA 0 := by
  simp [chartEval, dA0, diagX, x, chartValue]

/--
@isnad1 id=eq.0h1v.s6.74507c7c7c0c from=translated src=- shape=4ab1a778 vocab=543a93e7
-/
@[simp] theorem chartEval_dA1 (y : ExplicitFrameChart ℚ) : chartEval y (dA1 ℚ) = y.diagA 1 := by
  simp [chartEval, dA1, diagX, x, chartValue]

/--
@isnad1 id=eq.0h1v.s6.d29f01071585 from=translated src=- shape=4ab1a778 vocab=416d888b
-/
@[simp] theorem chartEval_dB0 (y : ExplicitFrameChart ℚ) : chartEval y (dB0 ℚ) = y.diagB 0 := by
  simp [chartEval, dB0, diagX, x, chartValue]

/--
@isnad1 id=eq.0h1v.s6.62a04ed113c8 from=translated src=- shape=4ab1a778 vocab=276be327
-/
@[simp] theorem chartEval_dB1 (y : ExplicitFrameChart ℚ) : chartEval y (dB1 ℚ) = y.diagB 1 := by
  simp [chartEval, dB1, diagX, x, chartValue]

/--
@isnad1 id=eq.0h1v.s6.ff31039ebca6 from=translated src=- shape=84eaf886 vocab=b2ea912e
-/
@[simp] theorem chartEval_a (y : ExplicitFrameChart ℚ) : chartEval y (a ℚ) = y.z1 := by
  simp [chartEval, a, gaugeX, x, chartValue]

/--
@isnad1 id=eq.0h1v.s6.7903a45652b6 from=translated src=- shape=84eaf886 vocab=3927b3bb
-/
@[simp] theorem chartEval_b (y : ExplicitFrameChart ℚ) : chartEval y (b ℚ) = y.r2 := by
  simp [chartEval, b, gaugeX, x, chartValue]

/--
@isnad1 id=eq.0h1v.s6.ad02f74cab44 from=translated src=- shape=84eaf886 vocab=26449f37
-/
@[simp] theorem chartEval_c (y : ExplicitFrameChart ℚ) : chartEval y (c ℚ) = y.z2 := by
  simp [chartEval, c, gaugeX, x, chartValue]

/--
@isnad1 id=eq.0h2v.s7.7e07e4eb7d2a from=translated src=- shape=17fda06f vocab=48f3eee2
-/
@[simp] theorem chartEval_offX (y : ExplicitFrameChart ℚ) (ij : OffDiagonal) :
    chartEval y (offX ℚ ij) = matrixM y ij.1.1 ij.1.2 := by
  simp [chartEval, offX, x, chartValue]

/--
@isnad1 id=eq.1h3v.s6.5e2e0595f293 from=translated src=- shape=483bd7c6 vocab=280ee304
-/
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
/--
@isnad1 id=eq.1h1v.s7.149252ab726e from=translated src=- shape=cf26a0f4 vocab=0e28dc17
-/
theorem chartEval_PA : chartEval y (PA ℚ) = y.diagA 1 - y.diagA 2 := by
  rw [PA, map_sub, chartEval_dA1, chartEval_dA2 y heq]

include heq in
/--
@isnad1 id=eq.1h1v.s7.1ad5f0ad491a from=translated src=- shape=cf26a0f4 vocab=2739cbea
-/
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
/--
@isnad1 id=eq.2h1v.s7.79a1a662707c from=translated src=- shape=72782c91 vocab=2b6c9f95
-/
theorem chartEval_nA0 : chartEval y (nA0 ℚ) =
    (y.diagA 1 - y.diagA 2) * matrixM y 0 0 := by
  rw [nA0, map_sub, map_mul, chartEval_TA y hr heq,
    chartEval_dA2 y heq, chartEval_SA y hr heq]
  ring

include hr heq in
/--
@isnad1 id=eq.2h1v.s7.59b24eff920e from=translated src=- shape=72782c91 vocab=f9b377b6
-/
theorem chartEval_nA2 : chartEval y (nA2 ℚ) =
    (y.diagA 1 - y.diagA 2) * matrixM y 2 2 := by
  rw [nA2, map_sub, map_mul, chartEval_PA y heq,
    chartEval_SA y hr heq, chartEval_nA0 y hr heq]
  ring

include heq in
/--
@isnad1 id=eq.1h1v.s7.33c75cabc170 from=translated src=- shape=e1268d35 vocab=689e513c
-/
theorem chartEval_nB1 : chartEval y (nB1 ℚ) =
    (y.diagB 1 - y.diagB 2) * matrixM y 1 1 := by
  rw [nB1, map_sub, map_mul, chartEval_TB y heq,
    chartEval_dB2 y heq, chartEval_SB y heq]
  ring

include heq in
/--
@isnad1 id=eq.1h1v.s7.bf0c217cee5d from=translated src=- shape=e1268d35 vocab=7d0e6d11
-/
theorem chartEval_nB3 : chartEval y (nB3 ℚ) =
    (y.diagB 1 - y.diagB 2) * matrixM y 3 3 := by
  rw [nB3, map_sub, map_mul, chartEval_PB y heq,
    chartEval_SB y heq, chartEval_nB1 y heq]
  ring

include hr heq in
/-- Cleared readback: no division and no nonzero-pivot premise is needed.
@isnad1 id=eq.2h1v.s8.3285391e427a from=translated src=- shape=4553d594 vocab=2ac1a8fc
-/
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

/--
@isnad1 id=eq.0h0v.s6.a73513a01525 from=translated src=- shape=a64fd6aa vocab=a826b2f9
-/
@[simp] theorem acceptedEval_PA : acceptedEval (PA ℚ) = (-7 / 3 : ℚ) :=
  (chartEval_PA witnessChart1 witnessChart1_equations).trans witness_pivotA

/--
@isnad1 id=eq.0h0v.s6.51edb12cdb8f from=translated src=- shape=a64fd6aa vocab=c5f3839a
-/
@[simp] theorem acceptedEval_PB : acceptedEval (PB ℚ) = (-7 / 3 : ℚ) :=
  (chartEval_PB witnessChart1 witnessChart1_equations).trans witness_pivotB

/--
@isnad1 id=ne.0h0v.s6.9b0ffe91b769 from=translated src=- shape=bdb72b4d vocab=144a2843
-/
theorem acceptedEval_PA_ne_zero : acceptedEval (PA ℚ) ≠ 0 := by
  rw [acceptedEval_PA]
  norm_num

/--
@isnad1 id=ne.0h0v.s6.8193c0952bf3 from=translated src=- shape=bdb72b4d vocab=032b1cc5
-/
theorem acceptedEval_PB_ne_zero : acceptedEval (PB ℚ) ≠ 0 := by
  rw [acceptedEval_PB]
  norm_num

/--
@isnad1 id=eq.0h0v.s6.f751cc194e7b from=translated src=- shape=bdb72b4d vocab=28e6694a
-/
@[simp] theorem acceptedEval_a : acceptedEval (a ℚ) = 0 := chartEval_a witnessChart1
/--
@isnad1 id=eq.0h0v.s6.bf9b93719230 from=translated src=- shape=bdb72b4d vocab=2bdf5f71
-/
@[simp] theorem acceptedEval_b : acceptedEval (b ℚ) = 0 := chartEval_b witnessChart1
/--
@isnad1 id=eq.0h0v.s6.07f015199670 from=translated src=- shape=bdb72b4d vocab=acdd0a5a
-/
@[simp] theorem acceptedEval_c : acceptedEval (c ℚ) = 1 := chartEval_c witnessChart1

/-- The evaluated cleared matrix is a nonsingular diagonal scaling of the
already accepted residual moment.
@isnad1 id=eq.0h0v.s8.96f3da4a08ae from=translated src=- shape=bee877cd vocab=435f47d1
-/
theorem acceptedEval_N : (N ℚ).map acceptedEval =
    Matrix.diagonal ![(-7 / 3 : ℚ), -7 / 3, -7 / 3, -7 / 3] * parameterMoment := by
  have h := chartEval_N witnessChart1 (by rfl) witnessChart1_equations
  rw [witness_pivotA, witness_pivotB, matrixM_eq_moment_residualPairOfChart] at h
  exact h

/-- Determinant multiplicativity uses only the four diagonal factors and the
previously checked determinant of parameterMoment.
@isnad1 id=eq.0h0v.s7.0b8ba4d1539b from=translated src=- shape=65fe65d2 vocab=cba6bcea
-/
theorem acceptedEval_detN :
    acceptedEval (Matrix.det (N ℚ)) = (-7 / 3 : ℚ) ^ 4 * witnessScale := by
  rw [RingHom.map_det]
  change Matrix.det ((N ℚ).map acceptedEval) = _
  rw [acceptedEval_N, Matrix.det_mul, Matrix.det_diagonal, parameterMoment_det]
  norm_num [Fin.prod_univ_succ]

/--
@isnad1 id=ne.0h0v.s6.dfa7df4f309c from=translated src=- shape=acdfbbf4 vocab=65f19383
-/
theorem acceptedEval_detN_ne_zero : acceptedEval (Matrix.det (N ℚ)) ≠ 0 := by
  rw [acceptedEval_detN]
  exact mul_ne_zero (pow_ne_zero 4 (by norm_num)) witnessScale_ne_zero

end AlbertLean.Generic.GenericDetectorWitness
