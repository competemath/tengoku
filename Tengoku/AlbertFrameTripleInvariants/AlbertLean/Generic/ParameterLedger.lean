import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FibreLedger
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParameterFamily
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ProductDiagonal
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ProjectorSector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Public-ledger targets on the reciprocal parameter family

This module proves that, with the non-residual chart fields and residual
moment fixed, every entry of the public ledger is affine in the symmetric
determinant-root sum.  It follows that the genuine normalized root exchange
preserves the ledger, and that one public `Q` entry recovers the root sum.
The proof passes through source projector sectors; it does not identify the
coordinate residual base with the public ledger.
-/

noncomputable section

namespace AlbertLean.Generic.ParameterLedger

set_option maxRecDepth 10000

open AlbertLean
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.FibreLedger
open AlbertLean.Generic.LawfulChart
open AlbertLean.Generic.ParameterFamily
open AlbertLean.Generic.ProductDiagonal
open AlbertLean.Generic.ProjectorSector
open AlbertLean.Generic.ResidualAction
open AlbertLean.Generic.WitnessChart
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Comparison.StructuredProductF0
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredProduct

/-- Quadratic, linear, and constant coefficients of the three ordered
spectral projectors.-/
def projectorSquareCoeff : Fin 3 → ℚ := ![1 / 2, -1, 1 / 2]
def projectorLinearCoeff : Fin 3 → ℚ := ![-1 / 2, 0, 1 / 2]
def projectorOneCoeff : Fin 3 → ℚ := ![0, 1, 0]

/-- A spectral projector written wholly in the source Albert coordinates.-/
def sourceProjector (z : JCoord ℚ) (i : Fin 3) : JCoord ℚ :=
  sourceCombo z (projectorSquareCoeff i) (projectorLinearCoeff i)
    (projectorOneCoeff i)

/--
@isnad1 id=eq.0h1v.s8.a13a57cdecd6 from=translated src=- shape=2ed0334c vocab=ac620425
-/
theorem structuredEquiv_sourceSquare (z : JCoord ℚ) :
    structuredEquiv (sourceSquare z) =
      structuredProduct (structuredEquiv z) (structuredEquiv z) := by
  exact StructuredSourceProductAgreesWithF0 z z

/-- The source polynomial is exactly the frozen public projector in every
ordered slot.
@isnad1 id=eq.0h2v.s8.264e11461665 from=translated src=- shape=e867aa03 vocab=1a6f417b
-/
theorem structuredEquiv_sourceProjector (z : JCoord ℚ) (i : Fin 3) :
    structuredEquiv (sourceProjector z i) = projector (structuredEquiv z) i := by
  rw [sourceProjector, sourceCombo, map_add, map_add, map_smul, map_smul,
    map_smul, structuredEquiv_sourceOne, structuredEquiv_sourceSquare]
  fin_cases i
  · change (0 : ℚ) • one + (-1 / 2 : ℚ) • structuredEquiv z +
        (1 / 2 : ℚ) •
          structuredProduct (structuredEquiv z) (structuredEquiv z) =
      (2 : ℚ)⁻¹ •
        (structuredProduct (structuredEquiv z) (structuredEquiv z) -
          structuredEquiv z)
    module
  · change (1 : ℚ) • one + (0 : ℚ) • structuredEquiv z +
        (-1 : ℚ) •
          structuredProduct (structuredEquiv z) (structuredEquiv z) =
      one - structuredProduct (structuredEquiv z) (structuredEquiv z)
    module
  · change (0 : ℚ) • one + (1 / 2 : ℚ) • structuredEquiv z +
        (1 / 2 : ℚ) •
          structuredProduct (structuredEquiv z) (structuredEquiv z) =
      (2 : ℚ)⁻¹ •
        (structuredProduct (structuredEquiv z) (structuredEquiv z) +
          structuredEquiv z)
    module

private theorem chart_deltaX (x : ExplicitFrameChart ℚ) :
    deltaX x.s1 x.s2 x.c1 x.c2 = delta (residualPairOfChart x) := by
  rw [deltaX_eq_det_XMatrix]
  rfl

private theorem chart_deltaStarA (x : ExplicitFrameChart ℚ) :
    deltaStarA x.s1 x.s2 x.c1 x.c2 =
      deltaStar (residualPairOfChart x) := by
  rw [deltaStarA_eq_det_AMatrix]
  rfl

private theorem sourceProjector_encoderA_d1 (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderA x) i).d1 =
      projectorOneCoeff i + projectorLinearCoeff i * x.diagA 0 +
        projectorSquareCoeff i *
          (x.diagA 0 ^ 2 + matrixM x 0 0 + matrixM x 2 2) := by
  rw [sourceProjector, sourceCombo_d1]
  rfl

private theorem sourceProjector_encoderA_d2 (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderA x) i).d2 =
      projectorOneCoeff i + projectorLinearCoeff i * x.diagA 1 +
        projectorSquareCoeff i *
          (x.diagA 1 ^ 2 + matrixM x 2 2 + x.r1 * x.z1) := by
  rw [sourceProjector, sourceCombo_d2]
  simp [encoderA, vectorA, matrixM, momentMatrix, nC, nV, Pf, BW]

private theorem sourceProjector_encoderA_d3 (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderA x) i).d3 =
      projectorOneCoeff i + projectorLinearCoeff i * x.diagA 2 +
        projectorSquareCoeff i *
          (x.diagA 2 ^ 2 + x.r1 * x.z1 + matrixM x 0 0) := by
  rw [sourceProjector, sourceCombo_d3]
  simp [encoderA, vectorA, matrixM, momentMatrix, nS, nV, Pf, BW]

private theorem sourceProjector_encoderB_d1 (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderB x) i).d1 =
      projectorOneCoeff i + projectorLinearCoeff i * x.diagB 0 +
        projectorSquareCoeff i *
          (x.diagB 0 ^ 2 + matrixM x 1 1 + matrixM x 3 3) := by
  rw [sourceProjector, sourceCombo_d1]
  rfl

private theorem sourceProjector_encoderB_d2 (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderB x) i).d2 =
      projectorOneCoeff i + projectorLinearCoeff i * x.diagB 1 +
        projectorSquareCoeff i *
          (x.diagB 1 ^ 2 + matrixM x 3 3 + x.r2 * x.z2) := by
  rw [sourceProjector, sourceCombo_d2]
  simp [encoderB, vectorB, matrixM, momentMatrix, nC, nV, Pf, BW]

private theorem sourceProjector_encoderB_d3 (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderB x) i).d3 =
      projectorOneCoeff i + projectorLinearCoeff i * x.diagB 2 +
        projectorSquareCoeff i *
          (x.diagB 2 ^ 2 + x.r2 * x.z2 + matrixM x 1 1) := by
  rw [sourceProjector, sourceCombo_d3]
  simp [encoderB, vectorB, matrixM, momentMatrix, nS, nV, Pf, BW]

private theorem sourceProjector_encoderA_s (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderA x) i).s =
      mixedS x.s1 x.c1
        (sWeight (encoderA x) (projectorSquareCoeff i)
          (projectorLinearCoeff i))
        (projectorSquareCoeff i) x.r1 x.z1 := by
  exact sourceCombo_s_of_plane _ _ _ _ rfl

private theorem sourceProjector_encoderB_s (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderB x) i).s =
      mixedS x.s2 x.c2
        (sWeight (encoderB x) (projectorSquareCoeff i)
          (projectorLinearCoeff i))
        (projectorSquareCoeff i) x.r2 x.z2 := by
  exact sourceCombo_s_of_plane _ _ _ _ rfl

private theorem sourceProjector_encoderA_c (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderA x) i).c =
      mixedC x.s1 x.c1
        (cWeight (encoderA x) (projectorSquareCoeff i)
          (projectorLinearCoeff i))
        (projectorSquareCoeff i) x.r1 x.z1 := by
  exact sourceCombo_c_of_plane _ _ _ _ rfl

private theorem sourceProjector_encoderB_c (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderB x) i).c =
      mixedC x.s2 x.c2
        (cWeight (encoderB x) (projectorSquareCoeff i)
          (projectorLinearCoeff i))
        (projectorSquareCoeff i) x.r2 x.z2 := by
  exact sourceCombo_c_of_plane _ _ _ _ rfl

private theorem sourceProjector_encoderA_v (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderA x) i).v =
      mixedV (vectorA x) x.s1 x.c1
        (vWeight (encoderA x) (projectorSquareCoeff i)
          (projectorLinearCoeff i))
        (projectorSquareCoeff i) := by
  exact sourceCombo_v _ _ _ _

private theorem sourceProjector_encoderB_v (x : ExplicitFrameChart ℚ)
    (i : Fin 3) :
    (sourceProjector (encoderB x) i).v =
      mixedV (vectorB x) x.s2 x.c2
        (vWeight (encoderB x) (projectorSquareCoeff i)
          (projectorLinearCoeff i))
        (projectorSquareCoeff i) := by
  exact sourceCombo_v _ _ _ _

private theorem matrixM_reinsert_of_moment_eq (x : ExplicitFrameChart ℚ)
    (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) :
    matrixM (chartWithResidualPair x Q) = matrixM x := by
  rw [matrixM_eq_moment_residualPairOfChart,
    residualPairOfChart_chartWithResidualPair, hM,
    ← matrixM_eq_moment_residualPairOfChart]

private theorem sourceProjector_encoderA_diagonal_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (i : Fin 3) :
    (sourceProjector (encoderA (chartWithResidualPair x Q)) i).d1 =
        (sourceProjector (encoderA x) i).d1 ∧
      (sourceProjector (encoderA (chartWithResidualPair x Q)) i).d2 =
        (sourceProjector (encoderA x) i).d2 ∧
      (sourceProjector (encoderA (chartWithResidualPair x Q)) i).d3 =
        (sourceProjector (encoderA x) i).d3 := by
  rw [sourceProjector_encoderA_d1, sourceProjector_encoderA_d1,
    sourceProjector_encoderA_d2, sourceProjector_encoderA_d2,
    sourceProjector_encoderA_d3, sourceProjector_encoderA_d3,
    matrixM_reinsert_of_moment_eq x Q hM]
  simp [chartWithResidualPair]

private theorem sourceProjector_encoderB_diagonal_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (i : Fin 3) :
    (sourceProjector (encoderB (chartWithResidualPair x Q)) i).d1 =
        (sourceProjector (encoderB x) i).d1 ∧
      (sourceProjector (encoderB (chartWithResidualPair x Q)) i).d2 =
        (sourceProjector (encoderB x) i).d2 ∧
      (sourceProjector (encoderB (chartWithResidualPair x Q)) i).d3 =
        (sourceProjector (encoderB x) i).d3 := by
  rw [sourceProjector_encoderB_d1, sourceProjector_encoderB_d1,
    sourceProjector_encoderB_d2, sourceProjector_encoderB_d2,
    sourceProjector_encoderB_d3, sourceProjector_encoderB_d3,
    matrixM_reinsert_of_moment_eq x Q hM]
  simp [chartWithResidualPair]

private theorem sourceProjector_s_pair_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (j l : Fin 3) :
    BS (sourceProjector (encoderA (chartWithResidualPair x Q)) j).s
        (sourceProjector (encoderB (chartWithResidualPair x Q)) l).s =
      BS (sourceProjector (encoderA x) j).s
        (sourceProjector (encoderB x) l).s := by
  have hmomentMatrix :
      momentMatrix (chartWithResidualPair x Q).s1
          (chartWithResidualPair x Q).s2 (chartWithResidualPair x Q).c1
          (chartWithResidualPair x Q).c2 =
        momentMatrix x.s1 x.s2 x.c1 x.c2 := by
    change matrixM (chartWithResidualPair x Q) = matrixM x
    exact matrixM_reinsert_of_moment_eq x Q hM
  rw [sourceProjector_encoderA_s, sourceProjector_encoderB_s, mixedS_pair,
    sourceProjector_encoderA_s, sourceProjector_encoderB_s, mixedS_pair,
    hmomentMatrix]
  simp only [sWeight, encoderA, encoderB, chartWithResidualPair]

private theorem sourceProjector_c_pair_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (j l : Fin 3) :
    BC (sourceProjector (encoderA (chartWithResidualPair x Q)) j).c
        (sourceProjector (encoderB (chartWithResidualPair x Q)) l).c =
      BC (sourceProjector (encoderA x) j).c
        (sourceProjector (encoderB x) l).c := by
  have hmomentMatrix :
      momentMatrix (chartWithResidualPair x Q).s1
          (chartWithResidualPair x Q).s2 (chartWithResidualPair x Q).c1
          (chartWithResidualPair x Q).c2 =
        momentMatrix x.s1 x.s2 x.c1 x.c2 := by
    change matrixM (chartWithResidualPair x Q) = matrixM x
    exact matrixM_reinsert_of_moment_eq x Q hM
  rw [sourceProjector_encoderA_c, sourceProjector_encoderB_c, mixedC_pair,
    sourceProjector_encoderA_c, sourceProjector_encoderB_c, mixedC_pair,
    hmomentMatrix]
  simp only [cWeight, encoderA, encoderB, chartWithResidualPair]

private theorem sourceProjector_v_pair_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (j l : Fin 3) :
    BV (sourceProjector (encoderA (chartWithResidualPair x Q)) j).v
        (sourceProjector (encoderB (chartWithResidualPair x Q)) l).v =
      BV (sourceProjector (encoderA x) j).v
          (sourceProjector (encoderB x) l).v +
        projectorSquareCoeff j * projectorSquareCoeff l *
          (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  have hmomentMatrix :
      momentMatrix (chartWithResidualPair x Q).s1
          (chartWithResidualPair x Q).s2 (chartWithResidualPair x Q).c1
          (chartWithResidualPair x Q).c2 =
        momentMatrix x.s1 x.s2 x.c1 x.c2 := by
    change matrixM (chartWithResidualPair x Q) = matrixM x
    exact matrixM_reinsert_of_moment_eq x Q hM
  rw [sourceProjector_encoderA_v, sourceProjector_encoderB_v,
    mixedV_pair (h1 := rfl) (h2 := rfl),
    sourceProjector_encoderA_v, sourceProjector_encoderB_v,
    mixedV_pair (h1 := rfl) (h2 := rfl),
    hmomentMatrix,
    chart_deltaX, chart_deltaStarA,
    residualPairOfChart_chartWithResidualPair,
    chart_deltaX, chart_deltaStarA]
  simp only [baseRootSum]
  simp only [vWeight, encoderA, encoderB, vectorA, vectorB,
    chartWithResidualPair]
  ring

/-- With all non-residual chart fields and the residual moment fixed, a
projector pairing changes only through the symmetric determinant-root sum.
The coefficient is the product of the two projector-square coefficients.
@isnad1 id=eq.1h4v.s7.108d0488ba5d from=translated src=- shape=f955fdef vocab=04c09db5
-/
theorem sourceProjector_pairing_reinsert (x : ExplicitFrameChart ℚ)
    (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (j l : Fin 3) :
    sourceTraceForm
        (sourceProjector (encoderA (chartWithResidualPair x Q)) j)
        (sourceProjector (encoderB (chartWithResidualPair x Q)) l) =
      sourceTraceForm (sourceProjector (encoderA x) j)
          (sourceProjector (encoderB x) l) +
        projectorSquareCoeff j * projectorSquareCoeff l *
          (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  rw [sourceTraceForm_formula, sourceTraceForm_formula]
  have hA := sourceProjector_encoderA_diagonal_reinsert x Q hM j
  have hB := sourceProjector_encoderB_diagonal_reinsert x Q hM l
  rw [hA.1, hA.2.1, hA.2.2, hB.1, hB.2.1, hB.2.2,
    sourceProjector_s_pair_reinsert x Q hM j l,
    sourceProjector_c_pair_reinsert x Q hM j l,
    sourceProjector_v_pair_reinsert x Q hM j l]
  ring

private theorem ledger_Q_eq_source (x : ExplicitFrameChart ℚ) (j l : Fin 3) :
    (ledger (chartWitnessTriple x)).Q j l =
      sourceTraceForm (sourceProjector (encoderA x) j)
        (sourceProjector (encoderB x) l) := by
  rw [sourceTraceForm_agrees_with_f0,
    structuredEquiv_sourceProjector, structuredEquiv_sourceProjector]
  rfl

/-- Every public `Q` entry is affine in the symmetric determinant-root sum
when the residual moment and all non-residual chart fields are fixed.
@isnad1 id=eq.1h4v.s6.cc3c5a1b95b3 from=translated src=- shape=698c2485 vocab=421d0491
-/
theorem ledger_Q_reinsert (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (j l : Fin 3) :
    (ledger (chartWitnessTriple (chartWithResidualPair x Q))).Q j l =
      (ledger (chartWitnessTriple x)).Q j l +
        projectorSquareCoeff j * projectorSquareCoeff l *
          (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  rw [ledger_Q_eq_source, ledger_Q_eq_source]
  exact sourceProjector_pairing_reinsert x Q hM j l

/-- The two public pair tables involving the fixed diagonal frame do not
change when the residual moment is fixed.
@isnad1 id=eq.1h2v.s5.78084d74a3ca from=translated src=- shape=097df56e vocab=6c97fa66
-/
theorem ledger_P_reinsert (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) :
    (ledger (chartWitnessTriple (chartWithResidualPair x Q))).P =
      (ledger (chartWitnessTriple x)).P := by
  funext i j
  change traceForm (projector chartBaseEncoder i)
      (projector (structuredEquiv
        (encoderA (chartWithResidualPair x Q))) j) =
    traceForm (projector chartBaseEncoder i)
      (projector (structuredEquiv (encoderA x)) j)
  rw [chartBaseEncoder_eq_theta1E,
    traceForm_projector_theta1E_left, traceForm_projector_theta1E_left,
    ← structuredEquiv_sourceProjector, ← structuredEquiv_sourceProjector]
  have h := sourceProjector_encoderA_diagonal_reinsert x Q hM j
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/--
@isnad1 id=eq.1h2v.s5.479bb2188df6 from=translated src=- shape=097df56e vocab=f4f24bab
-/
theorem ledger_R_reinsert (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) :
    (ledger (chartWitnessTriple (chartWithResidualPair x Q))).R =
      (ledger (chartWitnessTriple x)).R := by
  funext l i
  change traceForm
      (projector (structuredEquiv
        (encoderB (chartWithResidualPair x Q))) l)
      (projector chartBaseEncoder i) =
    traceForm (projector (structuredEquiv (encoderB x)) l)
      (projector chartBaseEncoder i)
  rw [chartBaseEncoder_eq_theta1E,
    traceForm_projector_theta1E_right, traceForm_projector_theta1E_right,
    ← structuredEquiv_sourceProjector, ← structuredEquiv_sourceProjector]
  have h := sourceProjector_encoderB_diagonal_reinsert x Q hM l
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- Coefficient with which the varying vector-sector pairing enters each
diagonal coordinate of a source product.-/
def rawJointCoeff : Fin 3 → ℚ := ![0, 1 / 2, 1 / 2]

private theorem sourceProduct_projectors_d1_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (j l : Fin 3) :
    (sourceProduct
        (sourceProjector (encoderA (chartWithResidualPair x Q)) j)
        (sourceProjector (encoderB (chartWithResidualPair x Q)) l)).d1 =
      (sourceProduct (sourceProjector (encoderA x) j)
        (sourceProjector (encoderB x) l)).d1 := by
  rw [sourceProduct_d1, sourceProduct_d1]
  have hA := sourceProjector_encoderA_diagonal_reinsert x Q hM j
  have hB := sourceProjector_encoderB_diagonal_reinsert x Q hM l
  rw [hA.1, hB.1, sourceProjector_s_pair_reinsert x Q hM j l,
    sourceProjector_c_pair_reinsert x Q hM j l]

private theorem sourceProduct_projectors_d2_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (j l : Fin 3) :
    (sourceProduct
        (sourceProjector (encoderA (chartWithResidualPair x Q)) j)
        (sourceProjector (encoderB (chartWithResidualPair x Q)) l)).d2 =
      (sourceProduct (sourceProjector (encoderA x) j)
          (sourceProjector (encoderB x) l)).d2 +
        (1 / 2 : ℚ) * projectorSquareCoeff j * projectorSquareCoeff l *
          (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  rw [sourceProduct_d2, sourceProduct_d2]
  have hA := sourceProjector_encoderA_diagonal_reinsert x Q hM j
  have hB := sourceProjector_encoderB_diagonal_reinsert x Q hM l
  rw [hA.2.1, hB.2.1, sourceProjector_c_pair_reinsert x Q hM j l,
    sourceProjector_v_pair_reinsert x Q hM j l]
  ring

private theorem sourceProduct_projectors_d3_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (j l : Fin 3) :
    (sourceProduct
        (sourceProjector (encoderA (chartWithResidualPair x Q)) j)
        (sourceProjector (encoderB (chartWithResidualPair x Q)) l)).d3 =
      (sourceProduct (sourceProjector (encoderA x) j)
          (sourceProjector (encoderB x) l)).d3 +
        (1 / 2 : ℚ) * projectorSquareCoeff j * projectorSquareCoeff l *
          (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  rw [sourceProduct_d3, sourceProduct_d3]
  have hA := sourceProjector_encoderA_diagonal_reinsert x Q hM j
  have hB := sourceProjector_encoderB_diagonal_reinsert x Q hM l
  rw [hA.2.2, hB.2.2, sourceProjector_v_pair_reinsert x Q hM j l,
    sourceProjector_s_pair_reinsert x Q hM j l]
  ring

private def sourceDiagonal (z : JCoord ℚ) : Fin 3 → ℚ := ![z.d1, z.d2, z.d3]

private theorem sourceProduct_projectors_diagonal_reinsert
    (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (i j l : Fin 3) :
    sourceDiagonal
        (sourceProduct
          (sourceProjector (encoderA (chartWithResidualPair x Q)) j)
          (sourceProjector (encoderB (chartWithResidualPair x Q)) l)) i =
      sourceDiagonal
          (sourceProduct (sourceProjector (encoderA x) j)
            (sourceProjector (encoderB x) l)) i +
        rawJointCoeff i * projectorSquareCoeff j * projectorSquareCoeff l *
          (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  fin_cases i
  · simpa [sourceDiagonal, rawJointCoeff] using
      sourceProduct_projectors_d1_reinsert x Q hM j l
  · simpa [sourceDiagonal, rawJointCoeff] using
      sourceProduct_projectors_d2_reinsert x Q hM j l
  · simpa [sourceDiagonal, rawJointCoeff] using
      sourceProduct_projectors_d3_reinsert x Q hM j l

/-- The uncentered public joint moment is the corresponding diagonal source
coordinate of the product of source projectors.-/
private theorem rawJoint_eq_sourceDiagonal (x : ExplicitFrameChart ℚ)
    (i j l : Fin 3) :
    traceForm (projector chartBaseEncoder i)
        (structuredProduct (projector (f0EncoderA x) j)
          (projector (f0EncoderB x) l)) =
      sourceDiagonal
        (sourceProduct (sourceProjector (encoderA x) j)
          (sourceProjector (encoderB x) l)) i := by
  have hprod := StructuredSourceProductAgreesWithF0
    (sourceProjector (encoderA x) j) (sourceProjector (encoderB x) l)
  change traceForm (projector chartBaseEncoder i)
      (structuredProduct
        (projector (structuredEquiv (encoderA x)) j)
        (projector (structuredEquiv (encoderB x)) l)) = _
  rw [← structuredEquiv_sourceProjector, ← structuredEquiv_sourceProjector,
    ← hprod, chartBaseEncoder_eq_theta1E,
    traceForm_projector_theta1E_left]
  fin_cases i <;> rfl

private theorem rawJoint_reinsert (x : ExplicitFrameChart ℚ)
    (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (i j l : Fin 3) :
    traceForm (projector chartBaseEncoder i)
        (structuredProduct
          (projector (f0EncoderA (chartWithResidualPair x Q)) j)
          (projector (f0EncoderB (chartWithResidualPair x Q)) l)) =
      traceForm (projector chartBaseEncoder i)
          (structuredProduct (projector (f0EncoderA x) j)
            (projector (f0EncoderB x) l)) +
        rawJointCoeff i * projectorSquareCoeff j * projectorSquareCoeff l *
          (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  rw [rawJoint_eq_sourceDiagonal, rawJoint_eq_sourceDiagonal]
  exact sourceProduct_projectors_diagonal_reinsert x Q hM i j l

/-- Coefficient of the root-sum variation after the public centering term is
subtracted from the raw joint moment.-/
def centeredJointCoeff (i : Fin 3) : ℚ := rawJointCoeff i - 1 / 3

/--
@isnad1 id=eq.1h5v.s6.67a85d5a91fc from=translated src=- shape=08598326 vocab=059de409
-/
theorem ledger_C0_reinsert (x : ExplicitFrameChart ℚ) (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) (i j l : Fin 3) :
    (ledger (chartWitnessTriple (chartWithResidualPair x Q))).C0 i j l =
      (ledger (chartWitnessTriple x)).C0 i j l +
        centeredJointCoeff i * projectorSquareCoeff j *
          projectorSquareCoeff l *
            (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  have hP := congrFun (congrFun (ledger_P_reinsert x Q hM) i) j
  have hR := congrFun (congrFun (ledger_R_reinsert x Q hM) l) i
  have hQ := ledger_Q_reinsert x Q hM j l
  have hC0 :
      (ledger (chartWitnessTriple x)).C0 i j l =
        traceForm (projector chartBaseEncoder i)
            (structuredProduct (projector (f0EncoderA x) j)
              (projector (f0EncoderB x) l)) -
          ((ledger (chartWitnessTriple x)).P i j +
            (ledger (chartWitnessTriple x)).Q j l +
            (ledger (chartWitnessTriple x)).R l i) / 3 +
          2 / 9 := by
    rfl
  change
    traceForm (projector chartBaseEncoder i)
        (structuredProduct
          (projector (f0EncoderA (chartWithResidualPair x Q)) j)
          (projector (f0EncoderB (chartWithResidualPair x Q)) l)) -
        ((ledger (chartWitnessTriple (chartWithResidualPair x Q))).P i j +
          (ledger (chartWitnessTriple (chartWithResidualPair x Q))).Q j l +
          (ledger (chartWitnessTriple (chartWithResidualPair x Q))).R l i) / 3 +
        2 / 9 = _
  rw [rawJoint_reinsert x Q hM i j l, hP, hQ, hR, hC0]
  simp only [centeredJointCoeff]
  ring

/-- Apply the universal affine root-sum variation to a public ledger.-/
def shiftLedger (L : Ledger) (d : ℚ) : Ledger where
  P := L.P
  Q := fun j l => L.Q j l +
    projectorSquareCoeff j * projectorSquareCoeff l * d
  R := L.R
  C0 := fun i j l => L.C0 i j l +
    centeredJointCoeff i * projectorSquareCoeff j *
      projectorSquareCoeff l * d

/-- Complete 54-entry public-ledger variation with fixed retained chart data
and residual moment.
@isnad1 id=eq.1h2v.s5.997ea9eae0b6 from=translated src=- shape=0aff989c vocab=9dab6d3f
-/
theorem ledger_reinsert_eq_shiftLedger (x : ExplicitFrameChart ℚ)
    (Q : ResidualPair ℚ)
    (hM : moment Q = moment (residualPairOfChart x)) :
    ledger (chartWitnessTriple (chartWithResidualPair x Q)) =
      shiftLedger (ledger (chartWitnessTriple x))
        (baseRootSum (residualPairOfChart x) - baseRootSum Q) := by
  simp only [shiftLedger, ledger]
  rw [Ledger.mk.injEq]
  refine ⟨ledger_P_reinsert x Q hM, ?_, ledger_R_reinsert x Q hM, ?_⟩
  · funext j l
    exact ledger_Q_reinsert x Q hM j l
  · funext i j l
    exact ledger_C0_reinsert x Q hM i j l

/-- The symmetric determinant-root sum along the normalized family.-/
def parameterRootSum (t : ℚ) : ℚ := t + witnessScale / t

/-- The genuine normalized root exchange fixes the symmetric root sum.
@isnad1 id=eq.1h1v.s4.666408c34b0e from=translated src=- shape=87e591bd vocab=a1264920
-/
theorem parameterRootSum_reciprocal (t : ℚ) (ht : t ≠ 0) :
    parameterRootSum (witnessScale / t) = parameterRootSum t := by
  have h := (parameterResidualPair_reciprocal_sameBase t ht).2
  simpa only [parameterResidualPair_baseRootSum, parameterRootSum] using h

/-- The complete public `Q` table is an explicit affine function of the
symmetric determinant-root sum.
@isnad1 id=eq.1h3v.s6.e32a2093a5c3 from=translated src=- shape=458c8556 vocab=75be53f4
-/
theorem parameter_Q_affine (t : ℚ) (ht : t ≠ 0) (j l : Fin 3) :
    (ledger (parameterTriple t ht)).Q j l =
      (ledger (parameterTriple 1 one_ne_zero)).Q j l +
        projectorSquareCoeff j * projectorSquareCoeff l *
          ((1 + witnessScale) - parameterRootSum t) := by
  rw [parameterTriple, parameterChart]
  rw [ledger_Q_reinsert witnessChart1 (parameterResidualPair t ht)]
  · rw [parameterTriple_one]
    simp [parameterRootSum, baseRootSum, witnessChart1_delta,
      witnessChart1_deltaStar]
  · exact parameterResidualPair_moment t ht

/-- The full public ledger is affine in the symmetric root sum.
@isnad1 id=eq.1h1v.s5.c142b1d6c0d8 from=translated src=- shape=740aa7c2 vocab=9b56ca32
-/
theorem parameter_ledger_affine (t : ℚ) (ht : t ≠ 0) :
    ledger (parameterTriple t ht) =
      shiftLedger (ledger (parameterTriple 1 one_ne_zero))
        ((1 + witnessScale) - parameterRootSum t) := by
  rw [parameterTriple, parameterChart,
    ledger_reinsert_eq_shiftLedger witnessChart1 (parameterResidualPair t ht)]
  · rw [parameterTriple_one]
    simp [parameterRootSum, baseRootSum, witnessChart1_delta,
      witnessChart1_deltaStar]
  · exact parameterResidualPair_moment t ht

/-- At the two accepted parameters the public ledgers agree.  This is the
existing finite witness theorem transported through the chart readers.
@isnad1 id=eq.0h0v.s3.8fc8ba9b3f0c from=translated src=- shape=f3663c79 vocab=64c08f92
-/
theorem parameterLedger_one_eq_witnessScale :
    ledger (parameterTriple 1 one_ne_zero) =
      ledger (parameterTriple witnessScale witnessScale_ne_zero) := by
  rw [parameterTriple_one, parameterTriple_witnessScale]
  exact witnessCharts_ledger_eq

/-- Exact root-sum factorization target for the complete public ledger.  It is
separate from the residual-base definition so downstream theorems cannot
silently treat coordinate data as public moments.-/
def RootSumLedgerLaw : Prop :=
  ∃ L : ℚ → Ledger, ∀ (t : ℚ) (ht : t ≠ 0),
    ledger (parameterTriple t ht) = L (parameterRootSum t)

/-- The complete source-sector calculation establishes root-sum
factorization; this is no longer an assumption at the parameter-family level.
@isnad1 id=rootsuml.0h0v.s0.0e52ce3148ce from=translated src=- shape=45709ebd vocab=0e52ce31
-/
theorem parameter_rootSumLedgerLaw : RootSumLedgerLaw := by
  refine ⟨fun s => shiftLedger (ledger (parameterTriple 1 one_ne_zero))
    ((1 + witnessScale) - s), ?_⟩
  intro t ht
  exact parameter_ledger_affine t ht

/-- Root-sum factorization makes the full public ledger invariant under the
genuine reciprocal root exchange.
@isnad1 id=eq.2h1v.s4.dff94f1f16c0 from=translated src=- shape=406d6199 vocab=1e7b9577
-/
theorem ledger_eq_reciprocal_of_rootSumLedgerLaw
    (hLaw : RootSumLedgerLaw) (t : ℚ) (ht : t ≠ 0) :
    ledger
        (parameterTriple (witnessScale / t)
          (reciprocalParameter_ne_zero t ht)) =
      ledger (parameterTriple t ht) := by
  rcases hLaw with ⟨L, hL⟩
  rw [hL, hL, parameterRootSum_reciprocal t ht]

/-- The complete public ledger is invariant under the genuine normalized
root exchange on every nonzero member of the parameter family.
@isnad1 id=eq.1h1v.s4.cd5e6efb32cb from=translated src=- shape=78eb8352 vocab=46fc038d
-/
theorem parameter_ledger_reciprocal (t : ℚ) (ht : t ≠ 0) :
    ledger
        (parameterTriple (witnessScale / t)
          (reciprocalParameter_ne_zero t ht)) =
      ledger (parameterTriple t ht) :=
  ledger_eq_reciprocal_of_rootSumLedgerLaw parameter_rootSumLedgerLaw t ht

/-- The predicted affine value of the `(1,1)` public `Q` entry.  This one
entry has coefficient `-1` in the symmetric root sum and would recover that
sum from the public ledger.-/
def q11AffineValue (t : ℚ) : ℚ :=
  (ledger (parameterTriple 1 one_ne_zero)).Q 1 1 +
    (1 + witnessScale) - parameterRootSum t

/-- The exact scalar identity targeted by the source-sector calculation.-/
def Q11AffineLaw : Prop :=
  ∀ (t : ℚ) (ht : t ≠ 0),
    (ledger (parameterTriple t ht)).Q 1 1 = q11AffineValue t

/-- The source-sector pairing calculation proves the predicted `Q₁₁` law.
@isnad1 id=q11affin.0h0v.s0.774930f5f7c9 from=translated src=- shape=45709ebd vocab=774930f5
-/
theorem parameter_Q11_affine : Q11AffineLaw := by
  intro t ht
  rw [parameter_Q_affine t ht 1 1]
  simp [q11AffineValue, projectorSquareCoeff]
  ring

/-- Equality of complete public ledgers is exactly equality of the symmetric
determinant-root sum on the nonzero normalized parameter family.
@isnad1 id=iff.2h2v.s5.827cbd86eb7e from=translated src=- shape=9ecbfbed vocab=1c2984bf
-/
theorem parameter_ledger_eq_iff (t u : ℚ) (ht : t ≠ 0) (hu : u ≠ 0) :
    ledger (parameterTriple t ht) = ledger (parameterTriple u hu) ↔
      parameterRootSum t = parameterRootSum u := by
  constructor
  · intro h
    have hQ := congrArg (fun L : Ledger => L.Q 1 1) h
    rw [parameter_Q_affine t ht 1 1, parameter_Q_affine u hu 1 1] at hQ
    simp [projectorSquareCoeff] at hQ
    linarith
  · intro h
    rw [parameter_ledger_affine t ht, parameter_ledger_affine u hu, h]

/-- The predicted `Q₁₁` formula holds at the original accepted parameter.
@isnad1 id=eq.0h0v.s5.d177db08d9f6 from=translated src=- shape=f78e792d vocab=68e72fa7
-/
theorem q11AffineValue_one :
    (ledger (parameterTriple 1 one_ne_zero)).Q 1 1 = q11AffineValue 1 := by
  simp [q11AffineValue, parameterRootSum]

/-- The predicted `Q₁₁` formula also holds at the accepted reciprocal
parameter, using the independently proved complete-ledger equality.
@isnad1 id=eq.0h0v.s5.da8ec5f9b8bf from=translated src=- shape=93851438 vocab=d7eccf68
-/
theorem q11AffineValue_witnessScale :
    (ledger (parameterTriple witnessScale witnessScale_ne_zero)).Q 1 1 =
      q11AffineValue witnessScale := by
  have h := congrArg (fun L : Ledger => L.Q 1 1)
    parameterLedger_one_eq_witnessScale
  rw [← h]
  simp [q11AffineValue, parameterRootSum, witnessScale_ne_zero]
  ring

/-- Under the targeted `Q₁₁` identity, that single public ledger entry
recovers the symmetric determinant-root sum.
@isnad1 id=eq.2h1v.s6.f40d571aeb5b from=translated src=- shape=f752c9e6 vocab=7ea096fd
-/
theorem parameterRootSum_eq_of_Q11AffineLaw
    (hLaw : Q11AffineLaw) (t : ℚ) (ht : t ≠ 0) :
    parameterRootSum t =
      1 + witnessScale +
        (ledger (parameterTriple 1 one_ne_zero)).Q 1 1 -
          (ledger (parameterTriple t ht)).Q 1 1 := by
  rw [hLaw t ht]
  simp only [q11AffineValue]
  ring

/-- The proved `Q₁₁` identity recovers the root sum without a hypothesis.
@isnad1 id=eq.1h1v.s6.3c6810c64642 from=translated src=- shape=1c7cf9a2 vocab=3a0cf053
-/
theorem parameterRootSum_eq_Q11 (t : ℚ) (ht : t ≠ 0) :
    parameterRootSum t =
      1 + witnessScale +
        (ledger (parameterTriple 1 one_ne_zero)).Q 1 1 -
          (ledger (parameterTriple t ht)).Q 1 1 :=
  parameterRootSum_eq_of_Q11AffineLaw parameter_Q11_affine t ht

end AlbertLean.Generic.ParameterLedger
