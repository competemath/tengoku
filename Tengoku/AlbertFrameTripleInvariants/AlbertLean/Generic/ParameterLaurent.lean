import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.DetectorSeparation
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ParameterFamily

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sparse public coordinates of the reciprocal parameter family

Only five public coordinates vary in the normalized residual family.  This
module identifies its ordered public triple with the generic Laurent-family
surface used by the division-free detector circuit.  The proof reads the
chart matrices and the frozen source-to-F0 order; it does not expand a Jordan
product or detector.
-/

noncomputable section

namespace AlbertLean.Generic.ParameterLaurent

set_option maxHeartbeats 2000000

open AlbertLean
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.DetectorSeparation
open AlbertLean.Generic.LawfulChart
open AlbertLean.Generic.ParameterFamily
open AlbertLean.Generic.ResidualAction
open AlbertLean.Generic.WitnessChart
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Residual.SL4PairAction

/-- The inverse-parameter direction in the second encoder.-/
def parameterFInv : Coord :=
  (-3 / 2 : ℚ) • basisVec 18 + 2 • basisVec 26

/-- The constant Laurent coefficient in the second encoder.-/
def parameterFConst : Coord := theta1F - parameterFInv

/-- The positive-parameter direction in the third encoder.-/
def parameterKPos : Coord := basisVec 22

/-- The inverse-parameter direction in the third encoder.-/
def parameterKInv : Coord :=
  basisVec 18 - (13 / 9 : ℚ) • basisVec 26

/-- The constant Laurent coefficient in the third encoder.-/
def parameterKConst : Coord := theta1K - parameterKPos - parameterKInv

/-- At the accepted unit parameter, the fixed moment is literally the first
accepted covector matrix.
@isnad1 id=eq.0h0v.s4.c04e80954c5b from=translated src=- shape=a64ad2b1 vocab=6b08eb2a
-/
theorem parameterMoment_eq_witnessChart1_A :
    parameterMoment = (residualPairOfChart witnessChart1).A := by
  rw [parameterMoment, moment, witnessChart1_X, Matrix.mul_one]

/-- The first public encoder is fixed throughout the family.
@isnad1 id=eq.1h1v.s4.797df9a5bcb3 from=translated src=- shape=63be9574 vocab=77372447
-/
theorem parameterTriple_cE (t : ℚ) (ht : t ≠ 0) :
    (parameterTriple t ht).cE = theta1E := by
  exact chartBaseEncoder_eq_theta1E

/-- The second public encoder has Laurent exponents `0` and `-1`.
@isnad1 id=eq.1h1v.s5.a193626f4eca from=translated src=- shape=92448c51 vocab=514fd8ce
-/
theorem parameterTriple_cF (t : ℚ) (ht : t ≠ 0) :
    (parameterTriple t ht).cF =
      parameterFConst + t⁻¹ • parameterFInv := by
  funext i
  fin_cases i <;>
    simp [parameterTriple, parameterChart, chartWitnessTriple,
      f0EncoderA, structuredEquiv, structuredToF0, encoderA, vectorA,
      chartWithResidualPair, parameterFConst, parameterFInv,
      parameterMoment_eq_witnessChart1_A, parameterResidualPair_X,
      parameterResidualPair_A_zero, parameterResidualPair_A_one,
      parameterResidualPair_A_two, parameterResidualPair_A_three,
      AlbertLean.Residual.NormalizedOrbitSection.X0,
      residualPairOfChart, AMatrix, witnessChart1, f0ToStructured,
      theta1F, basisVec, q] <;>
    ring

/-- The third public encoder has Laurent exponents `-1`, `0`, and `1`.
@isnad1 id=eq.1h1v.s6.0849dad6bcc2 from=translated src=- shape=0a992d66 vocab=94119840
-/
theorem parameterTriple_cK (t : ℚ) (ht : t ≠ 0) :
    (parameterTriple t ht).cK =
      parameterKConst + t • parameterKPos + t⁻¹ • parameterKInv := by
  funext i
  fin_cases i <;>
    simp [parameterTriple, parameterChart, chartWitnessTriple,
      f0EncoderB, structuredEquiv, structuredToF0, encoderB, vectorB,
      chartWithResidualPair, parameterKConst, parameterKPos, parameterKInv,
      parameterMoment_eq_witnessChart1_A, parameterResidualPair_X,
      parameterResidualPair_A_zero, parameterResidualPair_A_one,
      parameterResidualPair_A_two, parameterResidualPair_A_three,
      AlbertLean.Residual.NormalizedOrbitSection.X0,
      residualPairOfChart, AMatrix, witnessChart1, f0ToStructured,
      theta1K, basisVec, q] <;>
    ring

/-- Exact bridge from the lawful chart family to the generic Laurent detector
surface.
@isnad1 id=eq.1h1v.s4.5bd7f3192f63 from=translated src=- shape=825d7b8b vocab=178f36f7
-/
theorem parameterTriple_eq_laurentTriple (t : ℚ) (ht : t ≠ 0) :
    parameterTriple t ht =
      laurentTriple theta1E parameterFConst parameterFInv
        parameterKConst parameterKPos parameterKInv t := by
  rw [show parameterTriple t ht =
      ⟨(parameterTriple t ht).cE, (parameterTriple t ht).cF,
        (parameterTriple t ht).cK⟩ by
    cases parameterTriple t ht
    rfl]
  rw [parameterTriple_cE, parameterTriple_cF, parameterTriple_cK]
  rfl

end AlbertLean.Generic.ParameterLaurent
