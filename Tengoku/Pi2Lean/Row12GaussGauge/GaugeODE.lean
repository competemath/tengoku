import Tengoku.Pi2Lean.Row12GaussGauge.Pullback
import Tengoku.Pi2Lean.Row12GaussGauge.Factor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeW_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeW_analyticAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeW_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeW_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY2_equation_eventually` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeW_equation_eventually` (it only prints; the queue checks the axioms of every declaration). -/

open Filter Set Row12

namespace Row12GaussGauge

noncomputable def gaugeW (z : ℝ) : ℝ := gaugeL z*gaugeY1 z

/--
@isnad1 id=eq.0h0v.s3.7a96efe45c87 from=translated src=- shape=3c26ae4f vocab=46aacbcd
-/
theorem gaugeW_zero : gaugeW 0 = 1 := by
  simp [gaugeW, gaugeL_zero, gaugeY1_zero]

/--
@isnad1 id=analytic.0h0v.s5.1c43a8994cb1 from=translated src=- shape=7489677a vocab=9b7b23b7
-/
theorem gaugeW_analyticAt_zero : AnalyticAt ℝ gaugeW 0 :=
  gaugeL_analyticAt_zero.mul gaugeY1_analyticAt_zero

/--
@isnad1 id=analytic.2h1v.s6.d4cadc965530 from=translated src=- shape=933e5a1b vocab=d0bdb995
-/
theorem gaugeW_analyticAt (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    AnalyticAt ℝ gaugeW z :=
  (gaugeL_analyticAt z (by positivity) (by positivity)).mul
    (gaugeY1_analyticAt z hz hz1)

/--
@isnad1 id=eq.2h1v.s6.b256757cf0dc from=translated src=- shape=f86e5d60 vocab=b5f2d922
-/
theorem gaugeW_equation (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    nativeTheta (nativeTheta gaugeW) z+gaugeB2 z*nativeTheta gaugeW z+
      gaugeC2 z*gaugeW z = 0 :=
  gaugeL_mul_euler_equation gaugeY1 z hz hz1 (gaugeY1_analyticAt z hz hz1)
    (gaugeY1_equation z hz hz1)

/--
@isnad1 id=eventual.0h0v.s6.b4a9d33f0cd0 from=translated src=- shape=6f6de35c vocab=32642cb7
-/
theorem gaugeY2_equation_eventually :
    (fun z => nativeTheta (nativeTheta gaugeY2) z+
      gaugeB2 z*nativeTheta gaugeY2 z+gaugeC2 z*gaugeY2 z)
        =ᶠ[nhdsWithin 0 (Ioi 0)] 0 := by
  have hn : ∀ᶠ q in nhds (0:ℝ), q < (1/8:ℝ) := isOpen_Iio.mem_nhds (by norm_num)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz1 hz
  exact gaugeY2_equation z hz hz1

/--
@isnad1 id=eventual.0h0v.s6.d91dfe7c080d from=translated src=- shape=6f6de35c vocab=484471ae
-/
theorem gaugeW_equation_eventually :
    (fun z => nativeTheta (nativeTheta gaugeW) z+
      gaugeB2 z*nativeTheta gaugeW z+gaugeC2 z*gaugeW z)
        =ᶠ[nhdsWithin 0 (Ioi 0)] 0 := by
  have hn : ∀ᶠ q in nhds (0:ℝ), q < (1/8:ℝ) := isOpen_Iio.mem_nhds (by norm_num)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz1 hz
  exact gaugeW_equation z hz hz1

end Row12GaussGauge

