import Tengoku.Pi2Lean.Row12.GaussQuadratic
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeRoot_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeRoot_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeRatio_sq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeRatio_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeRatio_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP1_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP2_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeBase_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeK1_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeK2_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP1_quadratic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP2_quadratic` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP1_norm_lt_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP2_norm_lt_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP1_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP2_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP1_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP2_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY1_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY2_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY1_analyticAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY2_analyticAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY1_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY2_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeRatio_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeRatio_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeBase_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeK1_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeK2_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeB1_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeB2_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeC1_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeC2_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeMu_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeB1_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeB2_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeC1_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeC2_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeB1_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeB2_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeC1_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeC2_continuousAt_zero` (it only prints; the queue checks the axioms of every declaration). -/

open Filter Set Row12

namespace Row12GaussGauge

noncomputable def gaugeRatio (D z : ℝ) : ℝ :=
  Real.sqrt (1 + 64*z) / Real.sqrt (1 + D*z)

noncomputable def gaugeP1 (z : ℝ) : ℝ :=
  (1 - (1-8*z)*gaugeRatio 16 z/(1+16*z))/2

noncomputable def gaugeP2 (z : ℝ) : ℝ :=
  (1 - (1-512*z)*gaugeRatio 256 z/(1+256*z))/2

noncomputable def gaugeL (z : ℝ) : ℝ :=
  Real.exp ((Real.log (1+256*z)-Real.log (1+16*z))/4)

noncomputable def gaugeY1 (z : ℝ) : ℝ := gaussA (gaugeP1 z)
noncomputable def gaugeY2 (z : ℝ) : ℝ := gaussA (gaugeP2 z)

noncomputable def gaugeBase (C D z : ℝ) : ℝ :=
  C*gaugeRatio D z/((1+64*z)*(1+D*z)^2)

noncomputable def gaugeK1 (z : ℝ) : ℝ := z*gaugeBase 864 16 z
noncomputable def gaugeK2 (z : ℝ) : ℝ := gaugeBase 432 256 z

noncomputable def gaugeT (D z : ℝ) : ℝ :=
  -32/(1+64*z)-5*D/(2*(1+D*z))

noncomputable def gaugeB1 (z : ℝ) : ℝ :=
  z*(-8/(1+16*z)+32/(1+64*z))
noncomputable def gaugeC1 (z : ℝ) : ℝ :=
  -240*z^2/((1+64*z)*(1+16*z)^2)
noncomputable def gaugeB2 (z : ℝ) : ℝ :=
  z*(-128/(1+256*z)+32/(1+64*z))
noncomputable def gaugeC2 (z : ℝ) : ℝ :=
  -60*z/((1+64*z)*(1+256*z)^2)

noncomputable def gaugeMu (z : ℝ) : ℝ := 60/((1+16*z)*(1+256*z))

/--
@isnad1 id=hasderiv.1h2v.s7.eb7c99ae515b from=translated src=- shape=06f418a9 vocab=119ed9c2
-/
theorem gaugeRoot_hasDerivAt (D z : ℝ) (hp : 0 < 1+D*z) :
    HasDerivAt (fun x : ℝ => Real.sqrt (1+D*x)) (D/(2*Real.sqrt (1+D*z))) z := by
  simpa only [Pi.add_apply, id_eq, zero_add, mul_one] using
    ((hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul D)).sqrt (ne_of_gt hp)

/--
@isnad1 id=analytic.1h2v.s6.ad8b0767e5dc from=translated src=- shape=d39a2653 vocab=bf3f2e5e
-/
theorem gaugeRoot_analyticAt (D z : ℝ) (hp : 0 < 1+D*z) :
    AnalyticAt ℝ (fun x : ℝ => Real.sqrt (1+D*x)) z := by
  have ha : AnalyticAt ℝ (fun x : ℝ => 1+D*x) z := by fun_prop
  have hl : AnalyticAt ℝ (fun x : ℝ => Real.log (1+D*x)) z :=
    ha.log hp
  have hh : AnalyticAt ℝ (fun x : ℝ => Real.log (1+D*x)*(1/2)) z := by fun_prop
  apply hh.rexp'.congr
  have hn : {x : ℝ | 0 < 1+D*x} ∈ nhds z :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hp
  filter_upwards [hn] with x hx
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]

/--
@isnad1 id=eq.2h2v.s7.9145c70f49dd from=translated src=- shape=ec607791 vocab=ad800de1
-/
theorem gaugeRatio_sq (D z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+D*z) :
    gaugeRatio D z ^ 2 = (1+64*z)/(1+D*z) := by
  rw [gaugeRatio, div_pow, Real.sq_sqrt hS.le, Real.sq_sqrt hD.le]

/--
@isnad1 id=hasderiv.2h2v.s7.59b547e19f5f from=translated src=- shape=543b7229 vocab=544c6f98
-/
theorem gaugeRatio_hasDerivAt (D z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+D*z) :
    HasDerivAt (gaugeRatio D)
      (gaugeRatio D z*(32/(1+64*z)-D/(2*(1+D*z)))) z := by
  have hs : Real.sqrt (1+64*z) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hS)
  have hd : Real.sqrt (1+D*z) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hD)
  have hs2 := Real.sq_sqrt hS.le
  have hd2 := Real.sq_sqrt hD.le
  have hder := (gaugeRoot_hasDerivAt 64 z hS).div (gaugeRoot_hasDerivAt D z hD) hd
  have he : (64/(2*Real.sqrt (1+64*z))*Real.sqrt (1+D*z) -
      Real.sqrt (1+64*z)*(D/(2*Real.sqrt (1+D*z))))/Real.sqrt (1+D*z)^2 =
      gaugeRatio D z*(32/(1+64*z)-D/(2*(1+D*z))) := by
    unfold gaugeRatio
    generalize Real.sqrt (1+64*z) = s at hs hs2 ⊢
    generalize Real.sqrt (1+D*z) = d at hd hd2 ⊢
    rw [← hs2, ← hd2]
    field_simp [hs, hd]
    ring
  convert! hder.congr_deriv he using 1

/--
@isnad1 id=analytic.2h2v.s6.61ad9cb337fc from=translated src=- shape=a43a4982 vocab=959cb6e9
-/
theorem gaugeRatio_analyticAt (D z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+D*z) :
    AnalyticAt ℝ (gaugeRatio D) z := by
  exact (gaugeRoot_analyticAt 64 z hS).div (gaugeRoot_analyticAt D z hD)
    (ne_of_gt (Real.sqrt_pos.2 hD))

/--
@isnad1 id=hasderiv.2h1v.s6.d294a03f299f from=translated src=- shape=0832bae2 vocab=0e983694
-/
theorem gaugeP1_hasDerivAt (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    HasDerivAt gaugeP1 (gaugeK1 z) z := by
  have hR := gaugeRatio_hasDerivAt 16 z hS hD
  have ht := ((hasDerivAt_id z).const_mul 8).const_sub 1
  have hd := (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul 16)
  have hp := (((ht.mul hR).div hd (ne_of_gt hD)).const_sub 1).div_const 2
  have he : -((( -(8*1)*gaugeRatio 16 z + (1-8*z)*
      (gaugeRatio 16 z*(32/(1+64*z)-16/(2*(1+16*z)))))*(1+16*z) -
      ((1-8*z)*gaugeRatio 16 z)*(0+16*1))/(1+16*z)^2)/2 = gaugeK1 z := by
    unfold gaugeK1 gaugeBase
    generalize hSe : 1+64*z = s at hS ⊢
    generalize hDe : 1+16*z = d at hD ⊢
    field_simp [ne_of_gt hS, ne_of_gt hD]
    rw [← hSe, ← hDe]
    ring
  convert! hp.congr_deriv he using 1

/--
@isnad1 id=hasderiv.2h1v.s6.e0dea1c65774 from=translated src=- shape=0832bae2 vocab=dc4a7bfb
-/
theorem gaugeP2_hasDerivAt (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    HasDerivAt gaugeP2 (gaugeK2 z) z := by
  have hR := gaugeRatio_hasDerivAt 256 z hS hD
  have ht := ((hasDerivAt_id z).const_mul 512).const_sub 1
  have hd := (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul 256)
  have hp := (((ht.mul hR).div hd (ne_of_gt hD)).const_sub 1).div_const 2
  have he : -(((-(512*1)*gaugeRatio 256 z + (1-512*z)*
      (gaugeRatio 256 z*(32/(1+64*z)-256/(2*(1+256*z)))))*(1+256*z) -
      ((1-512*z)*gaugeRatio 256 z)*(0+256*1))/(1+256*z)^2)/2 = gaugeK2 z := by
    unfold gaugeK2 gaugeBase
    generalize hSe : 1+64*z = s at hS ⊢
    generalize hDe : 1+256*z = d at hD ⊢
    field_simp [ne_of_gt hS, ne_of_gt hD]
    rw [← hSe, ← hDe]
    ring
  convert! hp.congr_deriv he using 1

/--
@isnad1 id=hasderiv.2h3v.s6.32f236daf22d from=translated src=- shape=830325d8 vocab=e408ca14
-/
theorem gaugeBase_hasDerivAt (C D z : ℝ) (hS : 0 < 1+64*z)
    (hD : 0 < 1+D*z) :
    HasDerivAt (gaugeBase C D) (gaugeBase C D z*gaugeT D z) z := by
  have hR := gaugeRatio_hasDerivAt D z hS hD
  have hSder := (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul 64)
  have hDder := (hasDerivAt_const z 1).add ((hasDerivAt_id z).const_mul D)
  have hd := ((hR.const_mul C).div (hSder.mul (hDder.pow 2))
    (mul_ne_zero (ne_of_gt hS) (pow_ne_zero 2 (ne_of_gt hD))))
  have he : ((C*
      (gaugeRatio D z*(32/(1+64*z)-D/(2*(1+D*z)))))*((1+64*z)*(1+D*z)^2) -
      (C*gaugeRatio D z)*((0+64*1)*(1+D*z)^2 +
      (1+64*z)*(2*(1+D*z)^(2-1)*(0+D*1))))/((1+64*z)*(1+D*z)^2)^2 =
      gaugeBase C D z*gaugeT D z := by
    unfold gaugeBase gaugeT
    generalize 1+64*z = s at hS ⊢
    generalize 1+D*z = d at hD ⊢
    field_simp [ne_of_gt hS, ne_of_gt hD]
    ring
  convert! hd.congr_deriv he using 1

/--
@isnad1 id=hasderiv.3h1v.s7.df8cf63a7e45 from=translated src=- shape=4218b51e vocab=be106427
-/
theorem gaugeK1_hasDerivAt (z : ℝ) (hz : z ≠ 0) (hS : 0 < 1+64*z)
    (hD : 0 < 1+16*z) :
    HasDerivAt gaugeK1 (gaugeK1 z*(1/z+gaugeT 16 z)) z := by
  have hd := (hasDerivAt_id z).mul (gaugeBase_hasDerivAt 864 16 z hS hD)
  have he : 1*gaugeBase 864 16 z + z*(gaugeBase 864 16 z*gaugeT 16 z) =
      gaugeK1 z*(1/z+gaugeT 16 z) := by
    unfold gaugeK1
    field_simp [hz]
  convert! hd.congr_deriv he using 1

/--
@isnad1 id=hasderiv.2h1v.s7.bfb2927c1bbd from=translated src=- shape=e0b8c5c8 vocab=31405159
-/
theorem gaugeK2_hasDerivAt (z : ℝ) (hS : 0 < 1+64*z)
    (hD : 0 < 1+256*z) :
    HasDerivAt gaugeK2 (gaugeK2 z*gaugeT 256 z) z :=
  gaugeBase_hasDerivAt 432 256 z hS hD

/--
@isnad1 id=eq.2h1v.s7.f626ca339f7b from=translated src=- shape=73dbbd32 vocab=67334456
-/
theorem gaugeP1_quadratic (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    4*gaugeP1 z*(1-gaugeP1 z) = 1728*z^2/(1+16*z)^3 := by
  have hs := gaugeRatio_sq 16 z hS hD
  unfold gaugeP1
  generalize hdEq : 1+16*z = d at hD hs ⊢
  field_simp [ne_of_gt hD] at hs ⊢
  rw [← hdEq] at hs ⊢
  linear_combination - 4*(1-8*z)^2 * hs

/--
@isnad1 id=eq.2h1v.s7.f16b212721b4 from=translated src=- shape=a7e0dd61 vocab=bd677304
-/
theorem gaugeP2_quadratic (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    4*gaugeP2 z*(1-gaugeP2 z) = 1728*z/(1+256*z)^3 := by
  have hs := gaugeRatio_sq 256 z hS hD
  unfold gaugeP2
  generalize hdEq : 1+256*z = d at hD hs ⊢
  field_simp [ne_of_gt hD] at hs ⊢
  rw [← hdEq] at hs ⊢
  linear_combination - 4*(1-512*z)^2 * hs

/--
@isnad1 id=lt.2h1v.s5.c92f3a17e710 from=translated src=- shape=75c5e161 vocab=24184f16
-/
theorem gaugeP1_norm_lt_one (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    ‖gaugeP1 z‖ < 1 := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+16*z := by positivity
  have hq := gaugeP1_quadratic z hS hD
  have hqp : 0 < 1728*z^2/(1+16*z)^3 := by positivity
  have ht : 0 < 1-8*z := by linarith
  have hr : 0 < gaugeRatio 16 z := by
    unfold gaugeRatio
    exact div_pos (Real.sqrt_pos.2 hS) (Real.sqrt_pos.2 hD)
  have hp : gaugeP1 z < 1/2 := by
    unfold gaugeP1
    have hv : 0 < (1-8*z)*gaugeRatio 16 z/(1+16*z) := by positivity
    linarith
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> nlinarith

/--
@isnad1 id=lt.2h1v.s5.6b325472ca7a from=translated src=- shape=75c5e161 vocab=8038a449
-/
theorem gaugeP2_norm_lt_one (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    ‖gaugeP2 z‖ < 1 := by
  have ht : 0 < 1-8*z := by linarith
  have hS : 0 < 1+64*z := by linarith
  have hD : 0 < 1+256*z := by positivity
  have hq := gaugeP2_quadratic z hS hD
  have hqp : 0 < 1728*z/(1+256*z)^3 := by positivity
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> nlinarith

/--
@isnad1 id=analytic.2h1v.s6.9dfacdd5e58d from=translated src=- shape=f5026244 vocab=bbdccaa9
-/
theorem gaugeP1_analyticAt (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    AnalyticAt ℝ gaugeP1 z := by
  have hR := gaugeRatio_analyticAt 16 z hS hD
  unfold gaugeP1
  fun_prop (disch := exact ne_of_gt hD)

/--
@isnad1 id=analytic.2h1v.s6.b911a61b9d60 from=translated src=- shape=f5026244 vocab=d1db0f19
-/
theorem gaugeP2_analyticAt (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    AnalyticAt ℝ gaugeP2 z := by
  have hR := gaugeRatio_analyticAt 256 z hS hD
  unfold gaugeP2
  fun_prop (disch := exact ne_of_gt hD)

/--
@isnad1 id=eq.0h0v.s3.49590c32bbf1 from=translated src=- shape=3c26ae4f vocab=d7edb3b3
-/
theorem gaugeP1_zero : gaugeP1 0 = 0 := by norm_num [gaugeP1, gaugeRatio]
/--
@isnad1 id=eq.0h0v.s3.75ea2d0545f8 from=translated src=- shape=3c26ae4f vocab=457927f2
-/
theorem gaugeP2_zero : gaugeP2 0 = 0 := by norm_num [gaugeP2, gaugeRatio]
/--
@isnad1 id=eq.0h0v.s3.5181391be7d2 from=translated src=- shape=3c26ae4f vocab=74e1cef3
-/
theorem gaugeY1_zero : gaugeY1 0 = 1 := by simp [gaugeY1, gaugeP1_zero, gaussA_zero]
/--
@isnad1 id=eq.0h0v.s3.417ec21892b8 from=translated src=- shape=3c26ae4f vocab=973f9c15
-/
theorem gaugeY2_zero : gaugeY2 0 = 1 := by simp [gaugeY2, gaugeP2_zero, gaussA_zero]
/--
@isnad1 id=eq.0h0v.s3.cfec5e7831fc from=translated src=- shape=3c26ae4f vocab=cbd5dfaf
-/
theorem gaugeL_zero : gaugeL 0 = 1 := by norm_num [gaugeL]

/--
@isnad1 id=analytic.0h0v.s5.5ebe4e67e60c from=translated src=- shape=7489677a vocab=a99ea612
-/
theorem gaugeY1_analyticAt_zero : AnalyticAt ℝ gaugeY1 0 := by
  have ha : AnalyticAt ℝ gaussA (gaugeP1 0) := by
    rw [gaugeP1_zero]
    exact gaussA_analyticAt 0 (by norm_num)
  exact ha.comp (gaugeP1_analyticAt 0 (by norm_num) (by norm_num))

/--
@isnad1 id=analytic.0h0v.s5.5dd4c0ca1682 from=translated src=- shape=7489677a vocab=4f996a14
-/
theorem gaugeY2_analyticAt_zero : AnalyticAt ℝ gaugeY2 0 := by
  have ha : AnalyticAt ℝ gaussA (gaugeP2 0) := by
    rw [gaugeP2_zero]
    exact gaussA_analyticAt 0 (by norm_num)
  exact ha.comp (gaugeP2_analyticAt 0 (by norm_num) (by norm_num))

/--
@isnad1 id=analytic.2h1v.s6.1d408cfbef3a from=translated src=- shape=933e5a1b vocab=eaa0f2a3
-/
theorem gaugeY1_analyticAt (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    AnalyticAt ℝ gaugeY1 z :=
  (gaussA_analyticAt (gaugeP1 z) (gaugeP1_norm_lt_one z hz0 hz1)).comp
    (gaugeP1_analyticAt z (by positivity) (by positivity))

/--
@isnad1 id=analytic.2h1v.s6.4862b5faf0d9 from=translated src=- shape=933e5a1b vocab=e1b066de
-/
theorem gaugeY2_analyticAt (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    AnalyticAt ℝ gaugeY2 z :=
  (gaussA_analyticAt (gaugeP2 z) (gaugeP2_norm_lt_one z hz0 hz1)).comp
    (gaugeP2_analyticAt z (by positivity) (by positivity))

/--
@isnad1 id=lt.2h2v.s6.552e36118791 from=translated src=- shape=f9e56490 vocab=98474184
-/
theorem gaugeRatio_pos (D z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+D*z) :
    0 < gaugeRatio D z := by
  exact div_pos (Real.sqrt_pos.2 hS) (Real.sqrt_pos.2 hD)

/--
@isnad1 id=eq.0h1v.s4.b5c7b4ea0915 from=translated src=- shape=1d838610 vocab=45f64d1b
-/
theorem gaugeRatio_zero (D : ℝ) : gaugeRatio D 0 = 1 := by
  norm_num [gaugeRatio]

/--
@isnad1 id=eq.0h2v.s4.faee381d3c11 from=translated src=- shape=2d8bf611 vocab=dfeb65b8
-/
theorem gaugeBase_zero (C D : ℝ) : gaugeBase C D 0 = C := by
  norm_num [gaugeBase, gaugeRatio]

/--
@isnad1 id=eq.0h0v.s3.33a4601723b3 from=translated src=- shape=3c26ae4f vocab=4af251ce
-/
theorem gaugeK1_zero : gaugeK1 0 = 0 := by
  norm_num [gaugeK1]

/--
@isnad1 id=eq.0h0v.s4.bac7d471bcf9 from=translated src=- shape=3c26ae4f vocab=5afb5e48
-/
theorem gaugeK2_zero : gaugeK2 0 = 432 := by
  norm_num [gaugeK2, gaugeBase_zero]

/--
@isnad1 id=eq.0h0v.s3.97c49c456aff from=translated src=- shape=3c26ae4f vocab=5163cff5
-/
theorem gaugeB1_zero : gaugeB1 0 = 0 := by
  norm_num [gaugeB1]

/--
@isnad1 id=eq.0h0v.s3.505ed9021958 from=translated src=- shape=3c26ae4f vocab=9474a745
-/
theorem gaugeB2_zero : gaugeB2 0 = 0 := by
  norm_num [gaugeB2]

/--
@isnad1 id=eq.0h0v.s3.eee783e93e7d from=translated src=- shape=3c26ae4f vocab=18061690
-/
theorem gaugeC1_zero : gaugeC1 0 = 0 := by
  norm_num [gaugeC1]

/--
@isnad1 id=eq.0h0v.s3.ceb3f1a9f04e from=translated src=- shape=3c26ae4f vocab=e88da47a
-/
theorem gaugeC2_zero : gaugeC2 0 = 0 := by
  norm_num [gaugeC2]

/--
@isnad1 id=eq.0h0v.s4.0a224a6fc4b9 from=translated src=- shape=3c26ae4f vocab=13a0c751
-/
theorem gaugeMu_zero : gaugeMu 0 = 60 := by
  norm_num [gaugeMu]

/--
@isnad1 id=analytic.2h1v.s6.fd22b0667bfb from=translated src=- shape=8d4650ba vocab=21f8b14b
-/
theorem gaugeB1_analyticAt (z : ℝ) (hS : 1+64*z ≠ 0)
    (hD : 1+16*z ≠ 0) :
    AnalyticAt ℝ gaugeB1 z := by
  unfold gaugeB1
  fun_prop (disch := assumption)

/--
@isnad1 id=analytic.2h1v.s6.024fc6b845f5 from=translated src=- shape=8d4650ba vocab=f2e7007e
-/
theorem gaugeB2_analyticAt (z : ℝ) (hS : 1+64*z ≠ 0)
    (hD : 1+256*z ≠ 0) :
    AnalyticAt ℝ gaugeB2 z := by
  unfold gaugeB2
  fun_prop (disch := assumption)

/--
@isnad1 id=analytic.2h1v.s6.e191e98e4c93 from=translated src=- shape=8d4650ba vocab=be76a5ea
-/
theorem gaugeC1_analyticAt (z : ℝ) (hS : 1+64*z ≠ 0)
    (hD : 1+16*z ≠ 0) : AnalyticAt ℝ gaugeC1 z := by
  have hd : (1+64*z)*(1+16*z)^2 ≠ 0 := mul_ne_zero hS (pow_ne_zero 2 hD)
  unfold gaugeC1
  fun_prop (disch := assumption)

/--
@isnad1 id=analytic.2h1v.s6.0f39fac3b4e5 from=translated src=- shape=8d4650ba vocab=19b6d6e7
-/
theorem gaugeC2_analyticAt (z : ℝ) (hS : 1+64*z ≠ 0)
    (hD : 1+256*z ≠ 0) : AnalyticAt ℝ gaugeC2 z := by
  have hd : (1+64*z)*(1+256*z)^2 ≠ 0 := mul_ne_zero hS (pow_ne_zero 2 hD)
  unfold gaugeC2
  fun_prop (disch := assumption)

/--
@isnad1 id=continuo.0h0v.s4.2a68329db9f8 from=translated src=- shape=5446e38f vocab=408136c3
-/
theorem gaugeB1_continuousAt_zero : ContinuousAt gaugeB1 0 :=
  (gaugeB1_analyticAt 0 (by norm_num) (by norm_num)).continuousAt

/--
@isnad1 id=continuo.0h0v.s4.769b7e93733b from=translated src=- shape=5446e38f vocab=31cffc42
-/
theorem gaugeB2_continuousAt_zero : ContinuousAt gaugeB2 0 :=
  (gaugeB2_analyticAt 0 (by norm_num) (by norm_num)).continuousAt

/--
@isnad1 id=continuo.0h0v.s4.3372ccbc7c5b from=translated src=- shape=5446e38f vocab=d375a7e0
-/
theorem gaugeC1_continuousAt_zero : ContinuousAt gaugeC1 0 :=
  (gaugeC1_analyticAt 0 (by norm_num) (by norm_num)).continuousAt

/--
@isnad1 id=continuo.0h0v.s4.8d288450ba33 from=translated src=- shape=5446e38f vocab=666a7aa3
-/
theorem gaugeC2_continuousAt_zero : ContinuousAt gaugeC2 0 :=
  (gaugeC2_analyticAt 0 (by norm_num) (by norm_num)).continuousAt

end Row12GaussGauge

