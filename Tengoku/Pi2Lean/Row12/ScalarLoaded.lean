import Tengoku.Pi2Lean.Row12.AngularBridge
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.scalarComplexLoaded_cast` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.scalarIntegrand_path_bounds` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.scalarComplexLoaded_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.scalarIntegrand_continuousOn` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.scalarIntegrand_intervalIntegrable` (it only prints; the queue checks the axioms of every declaration). -/

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

noncomputable def scalarIntegrand (U : ℝ) : ℝ :=
  angularLoaded (rho*(1-U^2)^3)

noncomputable def scalarComplexLoaded (q : ℂ) : ℂ :=
  9*squaredNativeEuler 0 q+180*squaredNativeEuler 1 q+
    1288*squaredNativeEuler 2 q+3192*squaredNativeEuler 3 q

/--
@isnad1 id=eq.2h1v.s5.6648cd787489 from=translated src=- shape=0b72c4b8 vocab=ff8b5b8f
-/
theorem scalarComplexLoaded_cast {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    scalarComplexLoaded (q:ℂ) = (angularLoaded q:ℂ) := by
  rw [angularLoaded_cast_eq_squaredNativeEuler hq0 hq1]
  unfold scalarComplexLoaded
  ring

/--
@isnad1 id=and.1h1v.s7.a3cfcbab648d from=translated src=- shape=4edbcfbb vocab=e7d50482
-/
theorem scalarIntegrand_path_bounds {U : ℝ} (hU : U ∈ Icc (0:ℝ) 1) :
    0 ≤ rho*(1-U^2)^3 ∧ rho*(1-U^2)^3 < 1 := by
  have hx0 : 0 ≤ 1-U^2 := sub_nonneg.mpr (pow_le_one₀ hU.1 hU.2)
  have hx1 : 1-U^2 ≤ 1 := by nlinarith [sq_nonneg U]
  have hr0 : 0 ≤ rho := by norm_num [rho]
  have hr1 : rho < 1 := by norm_num [rho]
  refine ⟨mul_nonneg hr0 (pow_nonneg hx0 3),?_⟩
  exact ((mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1) hr0).trans_eq
    (mul_one rho)).trans_lt hr1

/--
@isnad1 id=analytic.1h1v.s5.18c0d313c77f from=translated src=- shape=a859375d vocab=56e86b19
-/
theorem scalarComplexLoaded_analyticAt (q : ℂ) (hq : ‖q‖ < 1) :
    AnalyticAt ℂ scalarComplexLoaded q := by
  unfold scalarComplexLoaded
  exact (((analyticAt_const.mul (squaredNativeEuler_analyticAt 0 q hq)).add
    (analyticAt_const.mul (squaredNativeEuler_analyticAt 1 q hq))).add
    (analyticAt_const.mul (squaredNativeEuler_analyticAt 2 q hq))).add
    (analyticAt_const.mul (squaredNativeEuler_analyticAt 3 q hq))

/--
@isnad1 id=continuo.0h0v.s4.8967aa6e1e90 from=translated src=- shape=6c3888e7 vocab=704a73db
-/
theorem scalarIntegrand_continuousOn : ContinuousOn scalarIntegrand (Icc (0:ℝ) 1) := by
  have hpath : Continuous (fun U : ℝ => (rho*(1-U^2)^3:ℝ)) := by fun_prop
  have hpathC : Continuous (fun U : ℝ => ((rho*(1-U^2)^3:ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp hpath
  have hc : ContinuousOn (fun U : ℝ => (scalarComplexLoaded ((rho*(1-U^2)^3:ℝ):ℂ)).re)
      (Icc (0:ℝ) 1) := by
    intro U hU
    obtain ⟨hq0,hq1⟩ := scalarIntegrand_path_bounds hU
    have hn : ‖((rho*(1-U^2)^3:ℝ):ℂ)‖ < 1 := by
      rw [Complex.norm_of_nonneg hq0]
      exact hq1
    exact Complex.continuous_re.continuousAt.comp_continuousWithinAt
      ((scalarComplexLoaded_analyticAt _ hn).continuousAt.comp_continuousWithinAt
        (f := fun V : ℝ => ((rho*(1-V^2)^3:ℝ):ℂ)) (x := U)
        hpathC.continuousAt.continuousWithinAt)
  apply hc.congr
  intro U hU
  obtain ⟨hq0,hq1⟩ := scalarIntegrand_path_bounds hU
  simpa only [Complex.ofReal_re,scalarIntegrand] using
    (congrArg Complex.re (scalarComplexLoaded_cast hq0 hq1)).symm

/--
@isnad1 id=interval.0h0v.s4.4536a545299f from=translated src=- shape=aefc7754 vocab=83a69ace
-/
theorem scalarIntegrand_intervalIntegrable : IntervalIntegrable scalarIntegrand volume 0 1 :=
  scalarIntegrand_continuousOn.intervalIntegrable_of_Icc (by norm_num)

end Row12

