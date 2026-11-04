import Tengoku.Pi2Lean.Row12.BetaContourAnalytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.scalarPolePlus_continuous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.scalarPoleMinus_continuous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.scalarLambda_path_continuous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.scalarBetaPositiveResidue_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.beta_positive_residue_limit` (it only prints; the queue checks the axioms of every declaration). -/

open Set Filter Metric Complex
open scoped Topology

namespace Row12

set_option maxHeartbeats 1000000

/--
@isnad1 id=continuo.0h0v.s3.8d4c0eb04900 from=translated src=- shape=e3d48bcb vocab=2a557081
-/
theorem scalarPolePlus_continuous : Continuous scalarPolePlus := by
  unfold scalarPolePlus scalarPathX scalarMid scalarEll scalarM
  fun_prop

/--
@isnad1 id=continuo.0h0v.s3.088b108f5c9e from=translated src=- shape=e3d48bcb vocab=98a3f11e
-/
theorem scalarPoleMinus_continuous : Continuous scalarPoleMinus := by
  unfold scalarPoleMinus scalarPathX scalarMid scalarEll scalarM
  fun_prop

/--
@isnad1 id=continuo.0h0v.s4.31a6df457c8c from=translated src=- shape=18759164 vocab=2f75d0ff
-/
theorem scalarLambda_path_continuous : Continuous (fun U => scalarLambda (scalarPathX U)) := by
  unfold scalarLambda scalarPathX
  fun_prop

/--
@isnad1 id=continuo.0h2v.s5.e740f55aa335 from=translated src=- shape=2071d655 vocab=584c626c
-/
theorem scalarBetaPositiveResidue_continuousAt_zero (i j : Fin 3) :
    ContinuousAt (fun U : ℝ => scalarBetaPositiveResidue U i j) 0 := by
  have hX : ContinuousAt (fun U : ℝ => (scalarPathX U:ℂ)) 0 := by
    unfold scalarPathX
    fun_prop
  have hLP := (betaFrameLP_differentiableAt (scalarPathX 0:ℂ) i j).continuousAt.comp
    (f := fun U : ℝ => (scalarPathX U:ℂ)) (x := 0) hX
  have hRP := (betaFrameRP_differentiableAt (scalarPathX 0:ℂ) i j).continuousAt.comp
    (f := fun U : ℝ => (scalarPathX U:ℂ)) (x := 0) hX
  have hS : ContinuousAt (fun U : ℝ => (Real.sqrt (scalarM (scalarPathX U)):ℂ)) 0 := by
    unfold scalarM scalarPathX
    fun_prop
  have hD : ContinuousAt (fun U : ℝ => betaFrameDenom (scalarPathX U:ℂ)) 0 := by
    unfold betaFrameDenom betaFrameM scalarPathX
    fun_prop
  have hD0 : betaFrameDenom (scalarPathX 0:ℂ) ≠ 0 := by
    norm_num [betaFrameDenom,betaFrameM,scalarPathX]
  exact ((Complex.continuous_ofReal.continuousAt.mul hLP).add (hS.mul hRP)).div hD hD0

/--
@isnad1 id=tendsto.0h0v.s6.79b7ee5648ea from=translated src=- shape=54d32a47 vocab=256dfe80
-/
theorem beta_positive_residue_limit :
    Tendsto (fun U : ℝ =>
      betaBranchNumerator (scalarBetaPositiveResidue U) (scalarLambda (scalarPathX U))
        (scalarPolePlus U)) (nhds 0) (nhds ((1/(36*Real.pi^2):ℝ):ℂ)) := by
  have ha : ContinuousAt (fun U : ℝ => (scalarPolePlus U:ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp scalarPolePlus_continuous.continuousAt
  have hl : ContinuousAt (fun U : ℝ => (scalarLambda (scalarPathX U):ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp scalarLambda_path_continuous.continuousAt
  have ha0 : (scalarPolePlus 0:ℂ) ≠ 0 := by rw [scalar_contact_poles.1]; norm_num
  have hquot := hl.div ha ha0
  have hqa : ‖(scalarPolePlus 0:ℂ)‖ < 1 := by rw [scalar_contact_poles.1]; norm_num
  have hqb : (scalarLambda (scalarPathX 0):ℂ)/(scalarPolePlus 0:ℂ) = 27/125 := by
    norm_num [scalarLambda,scalarPathX,rho,scalar_contact_poles.1]
  have hX (i : Fin 3) : ContinuousAt (fun U : ℝ => dualState (scalarPolePlus U:ℂ) i) 0 :=
    (dualState_entry_analyticAt i _ hqa).continuousAt.comp
      (f := fun U : ℝ => (scalarPolePlus U:ℂ)) (x := 0) ha
  have hY (j : Fin 3) : ContinuousAt (fun U : ℝ =>
      dualState ((scalarLambda (scalarPathX U):ℂ)/(scalarPolePlus U:ℂ)) j) 0 :=
    (dualState_entry_analyticAt j _ (by rw [hqb]; norm_num)).continuousAt.comp
      (f := fun U : ℝ => (scalarLambda (scalarPathX U):ℂ)/(scalarPolePlus U:ℂ))
      (x := 0) hquot
  have hc : ContinuousAt (fun U : ℝ =>
      betaBranchNumerator (scalarBetaPositiveResidue U) (scalarLambda (scalarPathX U))
        (scalarPolePlus U)) 0 := by
    unfold betaBranchNumerator betaPair
    exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
      ((hX i).mul (scalarBetaPositiveResidue_continuousAt_zero i j)).mul (hY j)))
  have he : betaBranchNumerator (scalarBetaPositiveResidue 0) (scalarLambda (scalarPathX 0))
      (scalarPolePlus 0) = ((1/(36*Real.pi^2):ℝ):ℂ) := by
    unfold betaBranchNumerator
    rw [scalar_beta_contact_residue,scalar_contact_poles.1]
    norm_num only [scalarLambda,scalarPathX,rho] 
    convert actual_dual_contact_residue using 1
    norm_num
  simpa only [he] using hc.tendsto

end Row12

