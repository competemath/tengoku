import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.WitnessChartMatrices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The accepted exact witness pair lies in one lawful residual chart fibre

The chart records below read the spinor coordinates of the accepted public
witnesses in the existing source-to-F0 order. Their remaining coordinates
are literally identical. Finite matrix calculations verify the residual
open and common base; lawfulness and unequal detectors reuse accepted proofs.
No detector calculation or matrix inverse is introduced here.
-/

noncomputable section

namespace AlbertLean.Generic.WitnessChart

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlbertLean
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Generic.ChartBridge
open AlbertLean.Generic.LawfulChart
open AlbertLean.Generic.ResidualAction
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Triality.ExteriorSix

theorem chartWitnessTriple_witnessChart1 :
    chartWitnessTriple witnessChart1 = witnessTheta1 := by
  simp only [chartWitnessTriple, witnessTheta1, chartBaseEncoder_eq_theta1E,
    witnessChart1_f0EncoderA, witnessChart1_f0EncoderB]

theorem chartWitnessTriple_witnessChartM :
    chartWitnessTriple witnessChartM = witnessThetaM := by
  simp only [chartWitnessTriple, witnessThetaM, chartBaseEncoder_eq_theta1E,
    thetaME_eq_theta1E_fast, witnessChartM_f0EncoderA, witnessChartM_f0EncoderB]

theorem witnessChart1_lawful : LawfulFrameTriple (chartWitnessTriple witnessChart1) := by
  rw [chartWitnessTriple_witnessChart1]
  exact witnessTheta1Lawful

theorem witnessChartM_lawful : LawfulFrameTriple (chartWitnessTriple witnessChartM) := by
  rw [chartWitnessTriple_witnessChartM]
  exact witnessThetaMLawful

theorem witnessChart1_equations :
    EquationsVanish (explicitFrameEquationValues witnessChart1) :=
  (equationsVanish_iff_lawfulFrameTriple witnessChart1).mpr witnessChart1_lawful

theorem witnessChartM_equations :
    EquationsVanish (explicitFrameEquationValues witnessChartM) :=
  (equationsVanish_iff_lawfulFrameTriple witnessChartM).mpr witnessChartM_lawful

theorem witnessChart1_isKappaLift : IsKappaLift witnessChart1 := by
  change (1 : ℚ) * 1 - 0 * 0 = 1
  norm_num

theorem witnessChartM_isKappaLift : IsKappaLift witnessChartM := by
  change (1 : ℚ) * 1 - 0 * 0 = 1
  norm_num

/-- Reinsertion changes precisely the four residual spinor fields.-/
theorem witnessChartM_eq_reinsert :
    witnessChartM =
      chartWithResidualPair witnessChart1 (residualPairOfChart witnessChartM) := by
  calc
    witnessChartM =
        chartWithResidualPair witnessChartM (residualPairOfChart witnessChartM) :=
      (chartWithResidualPair_self witnessChartM).symm
    _ = chartWithResidualPair witnessChart1 (residualPairOfChart witnessChartM) := rfl

private def witnessA1 : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![3 / 2, -2, -245 / 54, -3 / 2],
    ![-2, 1, -3 / 2, 1],
    ![0, -2, -35 / 18, 2],
    ![3 / 2, -91 / 27, 0, -13 / 9]]

private def witnessAM : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![3 / 2, -2, -245 / 54, -8748 / 410231],
    ![-2, 1, -3 / 2, 5832 / 410231],
    ![0, -2, -35 / 18, 11664 / 410231],
    ![3 / 2, -91 / 27, 0, -8424 / 410231]]

private theorem witnessChart1_A :
    (residualPairOfChart witnessChart1).A = witnessA1 := by
  change
    (fun i j : Fin 4 =>
      ![(![q 3 2, q (-2) 1, q (-245) 54, q (-3) 2] : Fin 4 → ℚ) j,
        (![q (-2) 1, q 1 1, q (-3) 2, q 1 1] : Fin 4 → ℚ) j,
        (![0, q (-2) 1, q (-35) 18, q 2 1] : Fin 4 → ℚ) j,
        (![q 3 2, q (-91) 27, 0, q (-13) 9] : Fin 4 → ℚ) j] i) = witnessA1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q, witnessA1]

private theorem witnessChartM_A :
    (residualPairOfChart witnessChartM).A = witnessAM := by
  change
    (fun i j : Fin 4 =>
      ![(![q 3 2, q (-2) 1, q (-245) 54, q (-8748) 410231] : Fin 4 → ℚ) j,
        (![q (-2) 1, q 1 1, q (-3) 2, q 5832 410231] : Fin 4 → ℚ) j,
        (![0, q (-2) 1, q (-35) 18, q 11664 410231] : Fin 4 → ℚ) j,
        (![q 3 2, q (-91) 27, 0, q (-8424) 410231] : Fin 4 → ℚ) j] i) = witnessAM
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [q, witnessAM]

theorem witnessChart1_delta : delta (residualPairOfChart witnessChart1) = 1 := by
  rw [delta, witnessChart1_X, Matrix.det_one]

theorem witnessChartM_delta :
    delta (residualPairOfChart witnessChartM) = witnessScale := by
  rw [delta, witnessChartM_X]
  exact AlbertLean.Residual.NormalizedOrbitSection.det_X0 witnessScale

theorem witnessChart1_deltaStar :
    deltaStar (residualPairOfChart witnessChart1) = witnessScale := by
  change Matrix.det
    (AMatrix witnessChart1.s1 witnessChart1.s2 witnessChart1.c1 witnessChart1.c2) =
      witnessScale
  rw [← deltaStarA_eq_det_AMatrix]
  change
    -BW
      (hodgeStar (dualWedge2
        (![q 3 2, q (-2) 1, q (-245) 54, q (-3) 2] : Udual ℚ)
        (![0, q (-2) 1, q (-35) 18, q 2 1] : Udual ℚ)))
      (hodgeStar (dualWedge2
        (![q (-2) 1, q 1 1, q (-3) 2, q 1 1] : Udual ℚ)
        (![q 3 2, q (-91) 27, 0, q (-13) 9] : Udual ℚ))) = witnessScale
  norm_num [BW, hodgeStar, dualWedge2, q, witnessScale] <;> decide +kernel

/-- The fourth vector column scales by m while the fourth covector column
scales by its reciprocal, leaving the literal residual moment unchanged.-/
theorem witnessCharts_moment_eq :
    moment (residualPairOfChart witnessChartM) =
      moment (residualPairOfChart witnessChart1) := by
  unfold moment
  rw [witnessChart1_X, witnessChartM_X, witnessChart1_A, witnessChartM_A,
    Matrix.mul_one]
  ext i j
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessAM, witnessA1, witnessScale]

/-- Multiplicativity obtains the second covector determinant from the first;
no second determinant expansion or inverse calculation is needed.-/
theorem witnessChartM_deltaStar :
    deltaStar (residualPairOfChart witnessChartM) = 1 := by
  have h := congrArg Matrix.det witnessCharts_moment_eq
  simp only [moment, Matrix.det_mul] at h
  change deltaStar (residualPairOfChart witnessChartM) *
      delta (residualPairOfChart witnessChartM) =
    deltaStar (residualPairOfChart witnessChart1) *
      delta (residualPairOfChart witnessChart1) at h
  rw [witnessChart1_delta, witnessChart1_deltaStar, witnessChartM_delta] at h
  norm_num [witnessScale] at h
  linarith

theorem witnessChart1_open : ResidualOpen (residualPairOfChart witnessChart1) := by
  constructor
  · rw [witnessChart1_delta]
    norm_num
  · rw [witnessChart1_deltaStar]
    norm_num [witnessScale]

theorem witnessChartM_open : ResidualOpen (residualPairOfChart witnessChartM) := by
  constructor
  · rw [witnessChartM_delta]
    norm_num [witnessScale]
  · rw [witnessChartM_deltaStar]
    norm_num

theorem witnessChart1_branch :
    delta (residualPairOfChart witnessChart1) ≠
      deltaStar (residualPairOfChart witnessChart1) := by
  rw [witnessChart1_delta, witnessChart1_deltaStar]
  norm_num [witnessScale]

theorem witnessCharts_sameResidualBase :
    sameResidualBase (residualPairOfChart witnessChart1)
      (residualPairOfChart witnessChartM) := by
  constructor
  · exact witnessCharts_moment_eq
  · change delta (residualPairOfChart witnessChartM) +
        deltaStar (residualPairOfChart witnessChartM) =
      delta (residualPairOfChart witnessChart1) +
        deltaStar (residualPairOfChart witnessChart1)
    rw [witnessChart1_delta, witnessChart1_deltaStar,
      witnessChartM_delta, witnessChartM_deltaStar]
    exact add_comm _ _

/-- The accepted unequal detector values witness separation on this fibre;
the existing detector proof is reused, not recomputed.-/
theorem witnessCharts_detector_ne :
    traceCubeDetector (chartWitnessTriple witnessChart1) ≠
      traceCubeDetector (chartWitnessTriple witnessChartM) := by
  rw [chartWitnessTriple_witnessChart1, chartWitnessTriple_witnessChartM]
  exact witnessDetectorValues.2.2

/-- A nonempty lawful explicit residual fibre contains two members with
unequal invariant detector values and identical retained chart fields.-/
theorem lawful_residual_fibre_detector_separated_nonempty :
    ∃ x y : ExplicitFrameChart ℚ,
      LawfulFrameTriple (chartWitnessTriple x) ∧
      LawfulFrameTriple (chartWitnessTriple y) ∧
      ResidualOpen (residualPairOfChart x) ∧
      ResidualOpen (residualPairOfChart y) ∧
      sameResidualBase (residualPairOfChart x) (residualPairOfChart y) ∧
      y = chartWithResidualPair x (residualPairOfChart y) ∧
      traceCubeDetector (chartWitnessTriple x) ≠
        traceCubeDetector (chartWitnessTriple y) := by
  exact ⟨witnessChart1, witnessChartM, witnessChart1_lawful, witnessChartM_lawful,
    witnessChart1_open, witnessChartM_open, witnessCharts_sameResidualBase,
    witnessChartM_eq_reinsert, witnessCharts_detector_ne⟩

end AlbertLean.Generic.WitnessChart
