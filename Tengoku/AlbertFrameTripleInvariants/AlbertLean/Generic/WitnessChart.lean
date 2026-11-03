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

/--
@isnad1 id=eq.0h0v.s2.32ed88f9887a from=translated src=- shape=4b736592 vocab=e52e4c08
-/
theorem chartWitnessTriple_witnessChart1 :
    chartWitnessTriple witnessChart1 = witnessTheta1 := by
  simp only [chartWitnessTriple, witnessTheta1, chartBaseEncoder_eq_theta1E,
    witnessChart1_f0EncoderA, witnessChart1_f0EncoderB]

/--
@isnad1 id=eq.0h0v.s2.293ed4944661 from=translated src=- shape=4b736592 vocab=e7df29a7
-/
theorem chartWitnessTriple_witnessChartM :
    chartWitnessTriple witnessChartM = witnessThetaM := by
  simp only [chartWitnessTriple, witnessThetaM, chartBaseEncoder_eq_theta1E,
    thetaME_eq_theta1E_fast, witnessChartM_f0EncoderA, witnessChartM_f0EncoderB]

/--
@isnad1 id=lawfulfr.0h0v.s1.21694524ae98 from=translated src=- shape=87ceb31f vocab=8ead1706
-/
theorem witnessChart1_lawful : LawfulFrameTriple (chartWitnessTriple witnessChart1) := by
  rw [chartWitnessTriple_witnessChart1]
  exact witnessTheta1Lawful

/--
@isnad1 id=lawfulfr.0h0v.s1.4d0ace495efa from=translated src=- shape=87ceb31f vocab=71405253
-/
theorem witnessChartM_lawful : LawfulFrameTriple (chartWitnessTriple witnessChartM) := by
  rw [chartWitnessTriple_witnessChartM]
  exact witnessThetaMLawful

/--
@isnad1 id=equation.0h0v.s3.0bd213d4d073 from=translated src=- shape=be2594e7 vocab=4298ce0f
-/
theorem witnessChart1_equations :
    EquationsVanish (explicitFrameEquationValues witnessChart1) :=
  (equationsVanish_iff_lawfulFrameTriple witnessChart1).mpr witnessChart1_lawful

/--
@isnad1 id=equation.0h0v.s3.8af7ed767760 from=translated src=- shape=be2594e7 vocab=7f16d622
-/
theorem witnessChartM_equations :
    EquationsVanish (explicitFrameEquationValues witnessChartM) :=
  (equationsVanish_iff_lawfulFrameTriple witnessChartM).mpr witnessChartM_lawful

/--
@isnad1 id=iskappal.0h0v.s2.67bdfff7d6c7 from=translated src=- shape=25b03439 vocab=96064fb4
-/
theorem witnessChart1_isKappaLift : IsKappaLift witnessChart1 := by
  change (1 : ℚ) * 1 - 0 * 0 = 1
  norm_num

/--
@isnad1 id=iskappal.0h0v.s2.759bcc463dff from=translated src=- shape=25b03439 vocab=3a040718
-/
theorem witnessChartM_isKappaLift : IsKappaLift witnessChartM := by
  change (1 : ℚ) * 1 - 0 * 0 = 1
  norm_num

/-- Reinsertion changes precisely the four residual spinor fields.
@isnad1 id=eq.0h0v.s4.c412d409408c from=translated src=- shape=7b553f42 vocab=6ed36cd3
-/
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

/--
@isnad1 id=eq.0h0v.s3.d9e02563d714 from=translated src=- shape=bda7d87c vocab=5681cc88
-/
theorem witnessChart1_delta : delta (residualPairOfChart witnessChart1) = 1 := by
  rw [delta, witnessChart1_X, Matrix.det_one]

/--
@isnad1 id=eq.0h0v.s3.8bb26c6717bf from=translated src=- shape=59d4783e vocab=c3671cb5
-/
theorem witnessChartM_delta :
    delta (residualPairOfChart witnessChartM) = witnessScale := by
  rw [delta, witnessChartM_X]
  exact AlbertLean.Residual.NormalizedOrbitSection.det_X0 witnessScale

/--
@isnad1 id=eq.0h0v.s3.692bc05f8cc8 from=translated src=- shape=59d4783e vocab=36c92257
-/
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
scales by its reciprocal, leaving the literal residual moment unchanged.
@isnad1 id=eq.0h0v.s4.4d4fdfc63693 from=translated src=- shape=3144e0b5 vocab=dedb8cea
-/
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
no second determinant expansion or inverse calculation is needed.
@isnad1 id=eq.0h0v.s3.32b817b79d9a from=translated src=- shape=bda7d87c vocab=0f40c5b3
-/
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

/--
@isnad1 id=residual.0h0v.s3.62c14b15b3f2 from=translated src=- shape=be2594e7 vocab=3c3b14f4
-/
theorem witnessChart1_open : ResidualOpen (residualPairOfChart witnessChart1) := by
  constructor
  · rw [witnessChart1_delta]
    norm_num
  · rw [witnessChart1_deltaStar]
    norm_num [witnessScale]

/--
@isnad1 id=residual.0h0v.s3.c311cba3c6fb from=translated src=- shape=be2594e7 vocab=4a1f383c
-/
theorem witnessChartM_open : ResidualOpen (residualPairOfChart witnessChartM) := by
  constructor
  · rw [witnessChartM_delta]
    norm_num [witnessScale]
  · rw [witnessChartM_deltaStar]
    norm_num

/--
@isnad1 id=ne.0h0v.s4.41dad799c5a2 from=translated src=- shape=ae44ea1b vocab=41b8ff65
-/
theorem witnessChart1_branch :
    delta (residualPairOfChart witnessChart1) ≠
      deltaStar (residualPairOfChart witnessChart1) := by
  rw [witnessChart1_delta, witnessChart1_deltaStar]
  norm_num [witnessScale]

/--
@isnad1 id=sameresi.0h0v.s3.84c0a64431c8 from=translated src=- shape=52363e58 vocab=f48fc255
-/
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
the existing detector proof is reused, not recomputed.
@isnad1 id=ne.0h0v.s3.6f258836cb18 from=translated src=- shape=51699e26 vocab=6a0a9005
-/
theorem witnessCharts_detector_ne :
    traceCubeDetector (chartWitnessTriple witnessChart1) ≠
      traceCubeDetector (chartWitnessTriple witnessChartM) := by
  rw [chartWitnessTriple_witnessChart1, chartWitnessTriple_witnessChartM]
  exact witnessDetectorValues.2.2

/-- A nonempty lawful explicit residual fibre contains two members with
unequal invariant detector values and identical retained chart fields.
@isnad1 id=ex.0h0v.s6.f41aeb625e83 from=translated src=- shape=0f35e475 vocab=529fc3ab
-/
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
