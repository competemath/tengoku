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

/--
@isnad1 id=eq.0h1v.s3.1f787243a2c4 from=translated src=- shape=e9e6e124 vocab=0f78e624
-/
@[simp] theorem sourcePair_publicPair (P : ResidualPair ℚ) :
    sourcePair (publicPair P) = P := by
  cases P
  rfl

/--
@isnad1 id=eq.0h1v.s3.dd327b145a78 from=translated src=- shape=47dcad53 vocab=47a4cac3
-/
@[simp] theorem publicPair_sourcePair (P : SecondStatement.MatrixPair) :
    publicPair (sourcePair P) = P := by
  cases P
  rfl

/-- The literal matrix in the public statement is the fixed source moment.
@isnad1 id=eq.0h0v.s2.30722e141203 from=translated src=- shape=54c8eceb vocab=5d3b9e2b
-/
theorem statementM_eq_parameterMoment :
    SecondStatement.M = parameterMoment := by
  rw [parameterMoment_eq_witnessChart1_A]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [SecondStatement.M, residualPairOfChart, AMatrix,
      witnessChart1, f0ToStructured, theta1F, theta1K, q]

/-- The literal reciprocal determinant constant agrees with the accepted
chart constant.
@isnad1 id=eq.0h0v.s2.e0617eb70736 from=translated src=- shape=54c8eceb vocab=4adfe3bf
-/
theorem statementMScalar_eq_witnessScale :
    SecondStatement.m = witnessScale := by
  norm_num [SecondStatement.m, witnessScale]

/--
@isnad1 id=eq.0h1v.s5.eef05fdf5f05 from=translated src=- shape=cad88e57 vocab=1fb02103
-/
@[simp] theorem sourcePair_moment (P : SecondStatement.MatrixPair) :
    moment (sourcePair P) = P.A * P.X := rfl

/--
@isnad1 id=eq.0h1v.s5.c93c17a88822 from=translated src=- shape=8a4d0bf6 vocab=eea9f321
-/
@[simp] theorem sourcePair_delta (P : SecondStatement.MatrixPair) :
    delta (sourcePair P) = Matrix.det P.X := rfl

/--
@isnad1 id=eq.0h1v.s5.d1f9e56fabdf from=translated src=- shape=8a4d0bf6 vocab=e85cbde8
-/
@[simp] theorem sourcePair_deltaStar (P : SecondStatement.MatrixPair) :
    deltaStar (sourcePair P) = Matrix.det P.A := rfl

/-- The public normal form and source normal form are literally the same
matrix pair off the parameter pole.
@isnad1 id=eq.1h1v.s4.66873481cd7e from=translated src=- shape=e10b44ba vocab=1d5c2b9a
-/
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
