import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SecondStatement
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CoordinateDomain
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParameterLaurent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Matrix-chart comparison for `SecondStatement`

`SecondStatement.lean` gives the fixed-chart reconstruction proposition in
a matrix-pair presentation. This module identifies that presentation with
the source-coordinate chart, including the moment, normalized parameter
family and three labelled encoders. Products and detectors are transported
in subsequent modules.
-/

noncomputable section

namespace AlbertLean.Generic.TauChart

set_option maxHeartbeats 2000000

open AlbertLean
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.CoordinateDomain
open AlbertLean.Generic.FullOrbitFibre
open AlbertLean.Generic.LawfulChart
open AlbertLean.Generic.ParameterFamily
open AlbertLean.Generic.ParameterLaurent
open AlbertLean.Generic.ResidualAction
open AlbertLean.Generic.WitnessChart
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction

/-- Forget the statement wrapper and read the same two matrices as a source
residual pair.-/
def sourcePair (P : SecondStatement.MatrixPair) : ResidualPair ℚ :=
  ⟨P.A, P.X⟩

/-- Wrap a source residual pair for the literal second statement.-/
def publicPair (P : ResidualPair ℚ) : SecondStatement.MatrixPair :=
  ⟨P.A, P.X⟩

@[simp] theorem sourcePair_publicPair (P : ResidualPair ℚ) :
    sourcePair (publicPair P) = P := by
  cases P
  rfl

@[simp] theorem publicPair_sourcePair (P : SecondStatement.MatrixPair) :
    publicPair (sourcePair P) = P := by
  cases P
  rfl

/-- The literal matrix in the public statement is the fixed source moment.-/
theorem statementM_eq_parameterMoment :
    SecondStatement.M = parameterMoment := by
  rw [parameterMoment_eq_witnessChart1_A]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SecondStatement.M, residualPairOfChart, AMatrix,
      witnessChart1, f0ToStructured, theta1F, theta1K, q]

/-- The literal reciprocal determinant constant agrees with the accepted
chart constant.-/
theorem statementMScalar_eq_witnessScale :
    SecondStatement.m = witnessScale := by
  norm_num [SecondStatement.m, witnessScale]

@[simp] theorem sourcePair_moment (P : SecondStatement.MatrixPair) :
    moment (sourcePair P) = P.A * P.X := rfl

@[simp] theorem sourcePair_delta (P : SecondStatement.MatrixPair) :
    delta (sourcePair P) = Matrix.det P.X := rfl

@[simp] theorem sourcePair_deltaStar (P : SecondStatement.MatrixPair) :
    deltaStar (sourcePair P) = Matrix.det P.A := rfl

/-- The public normal form and source normal form are literally the same
matrix pair off the parameter pole.-/
theorem sourcePair_normalizedPair (t : ℚ) (ht : t ≠ 0) :
    sourcePair (SecondStatement.normalizedPair t) =
      parameterResidualPair t ht := by
  apply ResidualPair.ext
  · change SecondStatement.M * SecondStatement.diagonal4 t⁻¹ =
      (parameterResidualPair t ht).A
    rw [parameterResidualPair_A, statementM_eq_parameterMoment]
    rfl
  · change SecondStatement.diagonal4 t = (parameterResidualPair t ht).X
    rw [parameterResidualPair_X]
    rfl

end AlbertLean.Generic.TauChart
