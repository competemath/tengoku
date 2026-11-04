import Tengoku.Pi2Lean.Row12.BetaJointAnalytic
import Tengoku.Pi2Lean.Row12.BetaLowerGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.betaFluxIntegrand_joint_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.scalar_balanced_circle_domain` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaFrame_real_path_agreement` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaFrameDenom_real_path_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaFlux_circle_regular` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaFluxCircle_eq_of_between_poles` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.betaFluxCircle_between_poles_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.beta_balanced_fixedCircle_eventually_of_off_pole` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.beta_balanced_fixedCircle_eventually` (it only prints; the queue checks the axioms of every declaration). -/

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

/--
@isnad1 id=and.2h1v.s6.03edb9b76937 from=translated src=- shape=5efd154b vocab=996ad8a4
-/
theorem scalar_balanced_circle_domain {U : ℝ} (hU : 0 < U) (hU1 : U < 1) :
    0 < Real.sqrt (scalarLambda (scalarPathX U)) ∧
      Real.sqrt (scalarLambda (scalarPathX U)) < 1 ∧
      ‖(scalarLambda (scalarPathX U):ℂ)‖ < Real.sqrt (scalarLambda (scalarPathX U)) := by
  have hx := scalarPathX_mem hU hU1
  have hl := scalarLambda_pos hx.1
  have hp : (scalarPathX U)^3 < 1 := pow_lt_one₀ hx.1.le hx.2 (by omega)
  have hl1 : scalarLambda (scalarPathX U) < 1 := by
    unfold scalarLambda
    have h := mul_lt_mul_of_pos_left hp (by norm_num [rho] : 0 < rho)
    norm_num [rho] at h ⊢
    linarith
  have hr := Real.sqrt_pos.2 hl
  have hs := Real.sq_sqrt hl.le
  have hr1 : Real.sqrt (scalarLambda (scalarPathX U)) < 1 := by nlinarith
  refine ⟨hr,hr1,?_⟩
  rw [Complex.norm_of_nonneg hl.le]
  nlinarith

/--
@isnad1 id=and.0h1v.s4.a2fb2cdfb394 from=translated src=- shape=13e478a1 vocab=ccb25d24
-/
theorem betaFrame_real_path_agreement (U : ℝ) :
    betaFrameX (U:ℂ)=(scalarPathX U:ℂ) ∧
      betaFrameLambda (betaFrameX (U:ℂ))=(scalarLambda (scalarPathX U):ℂ) := by
  constructor
  · simp [betaFrameX,scalarPathX]
  · simp [betaFrameX,scalarPathX,betaFrameLambda,betaFrameRho,scalarLambda,rho]

/--
@isnad1 id=ne.3h1v.s6.312fdb36f299 from=translated src=- shape=9f498d3f vocab=ac00a24e
-/
theorem betaFrameDenom_real_path_ne_zero {U : ℝ} (hU : 0 < U) (hU1 : U < 1)
    (hE : 99*scalarPathX U-50 ≠ 0) :
    betaFrameDenom (betaFrameX (U:ℂ)) ≠ 0 := by
  have hx := scalarPathX_mem hU hU1
  rw [(betaFrame_real_path_agreement U).1,(betaFrame_real_agreement (scalarPathX U)).2.2.2.2.2.1]
  apply Complex.ofReal_ne_zero.mpr
  unfold scalarDenom
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hx.1.ne')
    (scalarM_pos hx.2).ne') (pow_ne_zero 2 hE)

/--
@isnad1 id=ne.6h3v.s6.9b83edc688b1 from=translated src=- shape=a73fd28a vocab=c57e25f1
-/
theorem betaFlux_circle_regular {U : ℝ} (hU : 0 < U) (hU1 : U < 1)
    {r : ℝ} (hplus : scalarPolePlus U < r) (hminus : r < scalarPoleMinus U)
    (hd : betaFrameDenom (betaFrameX (U:ℂ)) ≠ 0) :
    ∀ s ∈ sphere (0:ℂ) r, betaFrameH (U:ℂ) s ≠ 0 := by
  intro s hs
  have hp := scalarPolePlus_pos_lt_radius hU hU1
  have hmpos : 0 < scalarPoleMinus U := hp.1.trans (hplus.trans hminus)
  have hsn : ‖s‖ = r := by simpa using mem_sphere.mp hs
  have hsa : s-(scalarPolePlus U:ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    rw [h,Complex.norm_of_nonneg hp.1.le] at hsn
    linarith
  have hsb : s-(scalarPoleMinus U:ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    rw [h,Complex.norm_of_nonneg hmpos.le] at hsn
    linarith
  unfold betaFrameH
  rw [scalar_beta_pole_factor hU hU1]
  exact mul_ne_zero hd (mul_ne_zero hsa hsb)

/--
@isnad1 id=eq.9h3v.s6.36216fdbda21 from=translated src=- shape=8d792e99 vocab=dd47d0fa
-/
theorem betaFluxCircle_eq_of_between_poles {U : ℝ} (hU : 0 < U) (hU1 : U < 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hl : ‖(scalarLambda (scalarPathX U):ℂ)‖ < r)
    (ha : scalarPolePlus U < r) (hb : R < scalarPoleMinus U) (hR : R < 1)
    (hd : betaFrameDenom (betaFrameX (U:ℂ)) ≠ 0) :
    betaFluxCircle (U:ℂ) R = betaFluxCircle (U:ℂ) r := by
  let A : Set ℂ := closedBall (0:ℂ) R \ ball (0:ℂ) r
  have hp := scalarPolePlus_pos_lt_radius hU hU1
  have hmpos : 0 < scalarPoleMinus U := (hr.trans_le hrR).trans hb
  have hDom (s : ℂ) (hs : s ∈ A) :
      betaFrameH (U:ℂ) s ≠ 0 ∧ s ≠ 0 ∧ ‖s‖ < 1 ∧ ‖betaFrameB (U:ℂ) s‖ < 1 := by
    obtain ⟨hs0,hs1,hb1⟩ := betaBranch_annulus_domain
      (scalarLambda (scalarPathX U)) s hr hl hR hs
    have hsR : ‖s‖ ≤ R := by simpa using mem_closedBall.mp hs.1
    have hsr : r ≤ ‖s‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hs.2
    have hsa : s-(scalarPolePlus U:ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      rw [h,Complex.norm_of_nonneg hp.1.le] at hsr
      linarith
    have hsb : s-(scalarPoleMinus U:ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      rw [h,Complex.norm_of_nonneg hmpos.le] at hsR
      linarith
    have hH : betaFrameH (U:ℂ) s ≠ 0 := by
      unfold betaFrameH
      rw [scalar_beta_pole_factor hU hU1]
      exact mul_ne_zero hd (mul_ne_zero hsa hsb)
    refine ⟨hH,hs0,hs1,?_⟩
    simpa only [betaFrameB,(betaFrame_real_path_agreement U).2] using hb1
  have hF (s : ℂ) (hs : s ∈ A) : DifferentiableAt ℂ (betaFluxIntegrand (U:ℂ)) s := by
    obtain ⟨hH,hs0,hs1,hb1⟩ := hDom s hs
    exact (betaFluxIntegrand_joint_analyticAt ((U:ℂ),s) hH hs0 hs1 hb1).curry_right.differentiableAt
  have he : (∮ s in C(0,R), betaFluxIntegrand (U:ℂ) s) =
      ∮ s in C(0,r), betaFluxIntegrand (U:ℂ) s :=
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR
      countable_empty (fun s hs => (hF s hs).continuousAt.continuousWithinAt) (by
        intro s hs
        exact hF s ⟨ball_subset_closedBall hs.1.1,
          fun he => hs.1.2 (ball_subset_closedBall he)⟩)
  unfold betaFluxCircle
  rw [he]

/--
@isnad1 id=eq.13h3v.s7.59f703e13954 from=translated src=- shape=a3a03bda vocab=a6c2ce54
-/
theorem betaFluxCircle_between_poles_eq {U : ℝ} (hU : 0 < U) (hU1 : U < 1)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hr1 : r < 1) (hR1 : R < 1)
    (hlr : ‖(scalarLambda (scalarPathX U):ℂ)‖ < r)
    (hlR : ‖(scalarLambda (scalarPathX U):ℂ)‖ < R)
    (har : scalarPolePlus U < r) (haR : scalarPolePlus U < R)
    (hbr : r < scalarPoleMinus U) (hbR : R < scalarPoleMinus U)
    (hd : betaFrameDenom (betaFrameX (U:ℂ)) ≠ 0) :
    betaFluxCircle (U:ℂ) R = betaFluxCircle (U:ℂ) r := by
  rcases le_total r R with hrR | hRr
  · exact betaFluxCircle_eq_of_between_poles hU hU1 hr hrR hlr har hbR hR1 hd
  · exact (betaFluxCircle_eq_of_between_poles hU hU1 hR hRr hlR haR hbr hr1 hd).symm

/--
@isnad1 id=eventual.2h1v.s6.d726c685be6e from=translated src=- shape=15b54056 vocab=99ee9a68
-/
theorem beta_balanced_fixedCircle_eventually_of_off_pole {U : ℝ}
    (hU : 0 < U) (hU1 : U < 1) :
    ∀ᶠ V in nhds U, 99*scalarPathX V-50 ≠ 0 → betaFluxBalanced V =
      betaFluxCircle (V:ℂ) (Real.sqrt (scalarLambda (scalarPathX U))) := by
  let r : ℝ := Real.sqrt (scalarLambda (scalarPathX U))
  obtain ⟨hr,hr1,hl⟩ := scalar_balanced_circle_domain hU hU1
  have ha := (scalarPolePlus_pos_lt_radius hU hU1).2
  have hb := scalarPoleMinus_gt_radius hU hU1
  have hA : ∀ᶠ V in nhds U, scalarPolePlus V < r :=
    scalarPolePlus_continuous.continuousAt.tendsto.eventually (Iio_mem_nhds ha)
  have hB : ∀ᶠ V in nhds U, r < scalarPoleMinus V :=
    scalarPoleMinus_continuous.continuousAt.tendsto.eventually (Ioi_mem_nhds hb)
  have hLC : Continuous (fun V : ℝ => ‖(scalarLambda (scalarPathX V):ℂ)‖) :=
    (Complex.continuous_ofReal.comp scalarLambda_path_continuous).norm
  have hL : ∀ᶠ V in nhds U, ‖(scalarLambda (scalarPathX V):ℂ)‖ < r :=
    hLC.continuousAt.tendsto.eventually (Iio_mem_nhds hl)
  filter_upwards [hA,hB,hL,isOpen_Ioo.mem_nhds (show U ∈ Ioo (0:ℝ) 1 from ⟨hU,hU1⟩)]
    with V hAV hBV hLV hV
  intro hEV
  obtain ⟨hRV,hRV1,hlV⟩ := scalar_balanced_circle_domain hV.1 hV.2
  exact betaFluxCircle_between_poles_eq hV.1 hV.2 hr hRV hr1 hRV1 hLV hlV hAV
    (scalarPolePlus_pos_lt_radius hV.1 hV.2).2 hBV
    (scalarPoleMinus_gt_radius hV.1 hV.2)
    (betaFrameDenom_real_path_ne_zero hV.1 hV.2 hEV)

/--
@isnad1 id=eventual.3h1v.s6.9ec39ad5c6fb from=translated src=- shape=ba5d452e vocab=4042479f
-/
theorem beta_balanced_fixedCircle_eventually {U : ℝ} (hU : 0 < U) (hU1 : U < 1)
    (hE : 99*scalarPathX U-50 ≠ 0) :
    betaFluxBalanced =ᶠ[nhds U] (fun V : ℝ =>
      betaFluxCircle (V:ℂ) (Real.sqrt (scalarLambda (scalarPathX U)))) := by
  have hEC : Continuous (fun V : ℝ => 99*scalarPathX V-50) := by
    unfold scalarPathX
    fun_prop
  filter_upwards [beta_balanced_fixedCircle_eventually_of_off_pole hU hU1,
    hEC.continuousAt.eventually_ne hE] with V hV hE
  exact hV hE

end Row12

