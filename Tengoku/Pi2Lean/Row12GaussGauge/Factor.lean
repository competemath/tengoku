import Tengoku.Pi2Lean.Row12GaussGauge.Algebra
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeMuPrime` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_eq_rpow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_analyticAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_eventually_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeMu_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeMu_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_second_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_second_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeB_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeC_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeC_deriv_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_mul_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_mul_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_mul_second_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_mul_second_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_mul_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gauge_factor_nativeTheta_second` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeL_mul_euler_equation` (it only prints; the queue checks the axioms of every declaration). -/

open Filter Set

namespace Row12GaussGauge

/-- The explicit derivative of the actual logarithmic gauge derivative.-/
noncomputable def gaugeMuPrime (z : ℝ) : ℝ :=
  -60 * (272 + 8192*z) / ((1+16*z)^2 * (1+256*z)^2)

/--
@isnad1 id=lt.0h1v.s3.01c6ce19f522 from=translated src=- shape=8a62b088 vocab=bfb12232
-/
theorem gaugeL_pos (z : ℝ) : 0 < gaugeL z := Real.exp_pos _

/--
@isnad1 id=eq.2h1v.s7.c05b47f9341f from=translated src=- shape=d7a598ef vocab=0cee1d63
-/
theorem gaugeL_eq_rpow (z : ℝ) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    gaugeL z = ((1+256*z)/(1+16*z)) ^ (1/4 : ℝ) := by
  rw [Real.rpow_def_of_pos (div_pos h256 h16),
    Real.log_div (ne_of_gt h256) (ne_of_gt h16)]
  unfold gaugeL
  congr 1
  ring

/--
@isnad1 id=analytic.2h1v.s6.ec8b147a57d9 from=translated src=- shape=f5026244 vocab=4eae7b38
-/
theorem gaugeL_analyticAt (z : ℝ) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    AnalyticAt ℝ gaugeL z := by
  have ha1 : AnalyticAt ℝ (fun x : ℝ => 1+16*x) z := by fun_prop
  have ha2 : AnalyticAt ℝ (fun x : ℝ => 1+256*x) z := by fun_prop
  have h1 : AnalyticAt ℝ (fun x : ℝ => Real.log (1+16*x)) z :=
    ha1.log h16
  have h2 : AnalyticAt ℝ (fun x : ℝ => Real.log (1+256*x)) z :=
    ha2.log h256
  have h3 : AnalyticAt ℝ
      (fun x : ℝ => (Real.log (1+256*x)-Real.log (1+16*x))/4) z := by
    fun_prop
  exact h3.rexp'

/--
@isnad1 id=analytic.0h0v.s5.7c37ace91887 from=translated src=- shape=7489677a vocab=9ac2e4cd
-/
theorem gaugeL_analyticAt_zero : AnalyticAt ℝ gaugeL 0 :=
  gaugeL_analyticAt 0 (by norm_num) (by norm_num)

/--
@isnad1 id=eventual.2h1v.s7.0ba8c4b621ea from=translated src=- shape=8d4468fc vocab=6177208d
-/
theorem gaugeL_eventually_pos (z : ℝ) (h16 : 0 < 1+16*z)
    (h256 : 0 < 1+256*z) :
    ∀ᶠ x : ℝ in nhds z, 0 < 1+16*x ∧ 0 < 1+256*x := by
  have h1 : {x : ℝ | 0 < 1+16*x} ∈ nhds z :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds h16
  have h2 : {x : ℝ | 0 < 1+256*x} ∈ nhds z :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds h256
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

/--
@isnad1 id=hasderiv.2h1v.s6.9dfb87b061aa from=translated src=- shape=83a26b95 vocab=a827edbf
-/
theorem gaugeL_hasDerivAt (z : ℝ) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    HasDerivAt gaugeL (gaugeL z*gaugeMu z) z := by
  have h1 : HasDerivAt (fun x : ℝ => 1+16*x) 16 z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul (16 : ℝ)).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => 1+256*x) 256 z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul (256 : ℝ)).const_add 1
  have hd := ((h2.log (ne_of_gt h256)).sub (h1.log (ne_of_gt h16))).div_const 4
  have he : (256/(1+256*z)-16/(1+16*z))/4 = gaugeMu z := by
    unfold gaugeMu
    calc
      (256/(1+256*z)-16/(1+16*z))/4 =
          ((256*(1+16*z)-16*(1+256*z))/((1+256*z)*(1+16*z)))/4 := by
        rw [div_sub_div _ _ (ne_of_gt h256) (ne_of_gt h16)]
        ring
      _ = (240/((1+256*z)*(1+16*z)))/4 := by
        congr 2
        ring
      _ = 60/((1+16*z)*(1+256*z)) := by
        rw [mul_comm (1+256*z) (1+16*z)]
        ring
  exact (hd.congr_deriv he).exp

/--
@isnad1 id=eq.2h1v.s6.9b8fc88aafdc from=translated src=- shape=e75544d9 vocab=936ae365
-/
theorem gaugeL_deriv (z : ℝ) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    deriv gaugeL z = gaugeL z*gaugeMu z :=
  (gaugeL_hasDerivAt z h16 h256).deriv

/--
@isnad1 id=hasderiv.2h1v.s6.062567a88e68 from=translated src=- shape=0832bae2 vocab=c08b7963
-/
theorem gaugeMu_hasDerivAt (z : ℝ) (h16 : 0 < 1+16*z)
    (h256 : 0 < 1+256*z) : HasDerivAt gaugeMu (gaugeMuPrime z) z := by
  have h1 : HasDerivAt (fun x : ℝ => 1+16*x) 16 z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul (16 : ℝ)).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => 1+256*x) 256 z := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id z).const_mul (256 : ℝ)).const_add 1
  have hd := (hasDerivAt_const z (60 : ℝ)).div (h1.mul h2)
    (mul_ne_zero (ne_of_gt h16) (ne_of_gt h256))
  have he : (0*((1+16*z)*(1+256*z))-
      60*(16*(1+256*z)+(1+16*z)*256))/((1+16*z)*(1+256*z))^2 =
      gaugeMuPrime z := by
    unfold gaugeMuPrime
    field_simp [ne_of_gt h16, ne_of_gt h256]
    ring
  exact hd.congr_deriv he

/--
@isnad1 id=eq.2h1v.s6.9260d41b7949 from=translated src=- shape=fa980e7a vocab=07b95528
-/
theorem gaugeMu_deriv (z : ℝ) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    deriv gaugeMu z = gaugeMuPrime z := (gaugeMu_hasDerivAt z h16 h256).deriv

/--
@isnad1 id=hasderiv.2h1v.s7.c7fa9e7cd8ad from=translated src=- shape=e8a0f74b vocab=02756e62
-/
theorem gaugeL_second_hasDerivAt (z : ℝ) (h16 : 0 < 1+16*z)
    (h256 : 0 < 1+256*z) :
    HasDerivAt (deriv gaugeL) (gaugeL z*(gaugeMuPrime z+(gaugeMu z)^2)) z := by
  have hd := (gaugeL_hasDerivAt z h16 h256).mul (gaugeMu_hasDerivAt z h16 h256)
  have he : deriv gaugeL =ᶠ[nhds z] (fun x : ℝ => gaugeL x*gaugeMu x) := by
    filter_upwards [gaugeL_eventually_pos z h16 h256] with x hx
    exact gaugeL_deriv x hx.1 hx.2
  exact (hd.congr_of_eventuallyEq he).congr_deriv (by ring)

/--
@isnad1 id=eq.2h1v.s7.bfc7dc01aae6 from=translated src=- shape=69a7e091 vocab=29d08eec
-/
theorem gaugeL_second_deriv (z : ℝ) (h16 : 0 < 1+16*z)
    (h256 : 0 < 1+256*z) :
    deriv (deriv gaugeL) z = gaugeL z*(gaugeMuPrime z+(gaugeMu z)^2) :=
  (gaugeL_second_hasDerivAt z h16 h256).deriv

/--
@isnad1 id=eq.2h1v.s6.bf67711aff3e from=translated src=- shape=f9559dcb vocab=e46cb0d1
-/
theorem gaugeB_identity (z : ℝ) (hz0 : 0 < z) (_hz1 : z < 1/8) :
    gaugeB1 z = gaugeB2 z+2*z*gaugeMu z := by
  have h16 : 1+16*z ≠ 0 := ne_of_gt (by positivity : 0 < 1+16*z)
  have h256 : 1+256*z ≠ 0 := ne_of_gt (by positivity : 0 < 1+256*z)
  have h64 : 1+64*z ≠ 0 := ne_of_gt (by positivity : 0 < 1+64*z)
  unfold gaugeB1 gaugeB2 gaugeMu
  field_simp [h16, h256, h64]
  ring

/--
@isnad1 id=eq.2h1v.s7.c12da0e12514 from=translated src=- shape=5890fa7a vocab=595c489d
-/
theorem gaugeC_identity (z : ℝ) (hz0 : 0 < z) (_hz1 : z < 1/8) :
    gaugeC1 z = gaugeC2 z+z^2*(gaugeMuPrime z+(gaugeMu z)^2)+
      z*(1+gaugeB2 z)*gaugeMu z := by
  have h16 : 1+16*z ≠ 0 := ne_of_gt (by positivity : 0 < 1+16*z)
  have h256 : 1+256*z ≠ 0 := ne_of_gt (by positivity : 0 < 1+256*z)
  have h64 : 1+64*z ≠ 0 := ne_of_gt (by positivity : 0 < 1+64*z)
  unfold gaugeC1 gaugeC2 gaugeB2 gaugeMuPrime gaugeMu
  field_simp [h16, h256, h64]
  ring

/--
@isnad1 id=eq.2h1v.s7.6e8c79aec7b7 from=translated src=- shape=56badeac vocab=931a05d9
-/
theorem gaugeC_deriv_identity (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8) :
    gaugeC1 z = gaugeC2 z+z^2*(deriv gaugeMu z+(gaugeMu z)^2)+
      z*(1+gaugeB2 z)*gaugeMu z := by
  rw [gaugeMu_deriv z (by positivity) (by positivity)]
  exact gaugeC_identity z hz0 hz1

/--
@isnad1 id=hasderiv.3h2v.s7.2ef74f8bd741 from=translated src=- shape=a018a466 vocab=e2c0f8ba
-/
theorem gaugeL_mul_hasDerivAt (f : ℝ → ℝ) (z : ℝ)
    (hf : DifferentiableAt ℝ f z) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    HasDerivAt (fun x : ℝ => gaugeL x*f x)
      (gaugeL z*(deriv f z+gaugeMu z*f z)) z := by
  exact ((gaugeL_hasDerivAt z h16 h256).mul hf.hasDerivAt).congr_deriv (by ring)

/--
@isnad1 id=eq.3h2v.s7.f17b507ef24a from=translated src=- shape=e6484c2c vocab=667a0150
-/
theorem gaugeL_mul_deriv (f : ℝ → ℝ) (z : ℝ)
    (hf : DifferentiableAt ℝ f z) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    deriv (fun x : ℝ => gaugeL x*f x) z =
      gaugeL z*(deriv f z+gaugeMu z*f z) :=
  (gaugeL_mul_hasDerivAt f z hf h16 h256).deriv

/--
@isnad1 id=hasderiv.3h2v.s8.f85e9ddd0bf0 from=translated src=- shape=131ff88e vocab=0afafe8a
-/
theorem gaugeL_mul_second_hasDerivAt (f : ℝ → ℝ) (z : ℝ)
    (hf : AnalyticAt ℝ f z) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    HasDerivAt (deriv (fun x : ℝ => gaugeL x*f x))
      (gaugeL z*(deriv (deriv f) z+2*gaugeMu z*deriv f z+
        (gaugeMuPrime z+(gaugeMu z)^2)*f z)) z := by
  have hd := (gaugeL_hasDerivAt z h16 h256).mul
    (hf.deriv.differentiableAt.hasDerivAt.add
      ((gaugeMu_hasDerivAt z h16 h256).mul hf.differentiableAt.hasDerivAt))
  have he : deriv (fun x : ℝ => gaugeL x*f x) =ᶠ[nhds z]
      (fun x : ℝ => gaugeL x*(deriv f x+gaugeMu x*f x)) := by
    filter_upwards [gaugeL_eventually_pos z h16 h256, hf.eventually_analyticAt]
      with x hx hfx
    exact gaugeL_mul_deriv f x hfx.differentiableAt hx.1 hx.2
  exact (hd.congr_of_eventuallyEq he).congr_deriv (by
    simp only [Pi.add_apply, Pi.mul_apply]
    ring)

/--
@isnad1 id=eq.3h2v.s8.43079d20ff7f from=translated src=- shape=29b7aced vocab=22d105fe
-/
theorem gaugeL_mul_second_deriv (f : ℝ → ℝ) (z : ℝ)
    (hf : AnalyticAt ℝ f z) (h16 : 0 < 1+16*z) (h256 : 0 < 1+256*z) :
    deriv (deriv (fun x : ℝ => gaugeL x*f x)) z =
      gaugeL z*(deriv (deriv f) z+2*gaugeMu z*deriv f z+
        (gaugeMuPrime z+(gaugeMu z)^2)*f z) :=
  (gaugeL_mul_second_hasDerivAt f z hf h16 h256).deriv

/-- Multiplication by the actual exponential gauge sends the first equation to the second.
@isnad1 id=eq.4h2v.s8.f6ff9ef170a7 from=translated src=- shape=54989009 vocab=1edc2525
-/
theorem gaugeL_mul_equation (f : ℝ → ℝ) (z : ℝ) (hz0 : 0 < z) (hz1 : z < 1/8)
    (hf : AnalyticAt ℝ f z)
    (heq : z^2*deriv (deriv f) z+z*(1+gaugeB1 z)*deriv f z+gaugeC1 z*f z = 0) :
    z^2*deriv (deriv (fun x : ℝ => gaugeL x*f x)) z+
      z*(1+gaugeB2 z)*deriv (fun x : ℝ => gaugeL x*f x) z+
      gaugeC2 z*(gaugeL z*f z) = 0 := by
  rw [gaugeL_mul_second_deriv f z hf (by positivity) (by positivity),
    gaugeL_mul_deriv f z hf.differentiableAt (by positivity) (by positivity)]
  rw [gaugeB_identity z hz0 hz1, gaugeC_identity z hz0 hz1] at heq
  linear_combination gaugeL z*heq

/--
@isnad1 id=eq.1h2v.s7.aa78c89e13c7 from=translated src=- shape=e63c2e83 vocab=937fc1bd
-/
theorem gauge_factor_nativeTheta_second (f : ℝ → ℝ) (z : ℝ)
    (hf : AnalyticAt ℝ f z) :
    Row12.nativeTheta (Row12.nativeTheta f) z =
      z*deriv f z+z^2*deriv (deriv f) z := by
  have hd := (hasDerivAt_id z).mul hf.deriv.differentiableAt.hasDerivAt
  change z*deriv (fun x : ℝ => x*deriv f x) z = _
  have he : deriv (fun x : ℝ => x*deriv f x) z =
      deriv f z+z*deriv (deriv f) z := by
    convert! hd.deriv using 1
    simp only [id_eq, one_mul]
  rw [he]
  ring

/--
@isnad1 id=eq.4h2v.s7.70a29549ebd9 from=translated src=- shape=afff3888 vocab=d12665ee
-/
theorem gaugeL_mul_euler_equation (f : ℝ → ℝ) (z : ℝ) (hz0 : 0 < z)
    (hz1 : z < 1/8) (hf : AnalyticAt ℝ f z)
    (heq : Row12.nativeTheta (Row12.nativeTheta f) z+
      gaugeB1 z*Row12.nativeTheta f z+gaugeC1 z*f z = 0) :
    Row12.nativeTheta (Row12.nativeTheta (fun x : ℝ => gaugeL x*f x)) z+
      gaugeB2 z*Row12.nativeTheta (fun x : ℝ => gaugeL x*f x) z+
      gaugeC2 z*(gaugeL z*f z) = 0 := by
  have heq' : z^2*deriv (deriv f) z+z*(1+gaugeB1 z)*deriv f z+gaugeC1 z*f z = 0 := by
    rw [gauge_factor_nativeTheta_second f z hf] at heq
    dsimp only [Row12.nativeTheta] at heq
    linear_combination heq
  have hLf : AnalyticAt ℝ (fun x : ℝ => gaugeL x*f x) z :=
    (gaugeL_analyticAt z (by positivity) (by positivity)).mul hf
  rw [gauge_factor_nativeTheta_second _ z hLf]
  dsimp only [Row12.nativeTheta]
  linear_combination gaugeL_mul_equation f z hz0 hz1 hf heq'

end Row12GaussGauge

