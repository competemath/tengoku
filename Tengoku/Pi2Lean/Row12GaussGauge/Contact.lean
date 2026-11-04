import Tengoku.Pi2Lean.Row12GaussGauge.Transformation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gauss_contact_value` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gauss_complement_hasDerivAt_contact` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gauss_complement_nativeTheta_contact` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gauss_contact_nativeTheta` (it only prints; the queue checks the axioms of every declaration). -/

open Row12

namespace Row12GaussGauge

/--
@isnad1 id=eq.0h0v.s6.8048d7aaf697 from=translated src=- shape=933ba716 vocab=bba983b1
-/
theorem gauss_contact_value :
    gaussA (1-gaussP (27/125:ℝ)) = Real.sqrt 2*gaussG (27/125) := by
  have he := gauge_transformation (1/64:ℝ) (by norm_num) (by norm_num)
  simpa only [gaugeY1, gaugeY2, gaugeP1_contact, gaugeP2_contact,
    gaugeL_contact, gaussG] using he

/--
@isnad1 id=hasderiv.0h0v.s7.28e7e125e6c4 from=translated src=- shape=7a0b5ca9 vocab=3a6cf0dd
-/
theorem gauss_complement_hasDerivAt_contact :
    HasDerivAt (fun q : ℝ => gaussA (1-gaussP q))
      (-deriv gaussA (1-gaussP (27/125:ℝ))/(4*Real.sqrt (1-27/125)))
      (27/125) := by
  have hp : ‖(1-gaussP (27/125:ℝ))‖ < 1 := by
    rw [← gaugeP2_contact]
    exact gaugeP2_norm_lt_one (1/64) (by norm_num) (by norm_num)
  have hd := (gaussA_analyticAt (1-gaussP (27/125:ℝ)) hp).differentiableAt.hasDerivAt.comp (27/125)
      ((gaussP_hasDerivAt (27/125) (by norm_num)).const_sub 1)
  apply hd.congr_deriv
  ring

/--
@isnad1 id=eq.0h0v.s7.70665e0e3c58 from=translated src=- shape=c72231af vocab=6b0224d1
-/
theorem gauss_complement_nativeTheta_contact :
    nativeTheta (fun q : ℝ => gaussA (1-gaussP q)) (27/125) =
      -(27/125:ℝ)*deriv gaussA (1-gaussP (27/125))/(4*Real.sqrt (1-27/125)) := by
  rw [nativeTheta, gauss_complement_hasDerivAt_contact.deriv]
  ring

/--
@isnad1 id=eq.0h0v.s7.d0a563e72696 from=translated src=- shape=7cb8aa50 vocab=45758ba2
-/
theorem gauss_contact_nativeTheta :
    nativeTheta (fun q : ℝ => gaussA (1-gaussP q)) (27/125) =
      -Real.sqrt 2*nativeTheta gaussG (27/125)-
        (3*Real.sqrt 2/28)*gaussG (27/125) := by
  have hk := gaugeK2_contact_ne_zero
  have hr : Real.sqrt (1-(27/125:ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have he := gauge_transformation_derivative (1/64:ℝ) (by norm_num) (by norm_num)
  rw [gaugeP1_contact, gaugeP2_contact, gaugeL_contact, gaugeK_contact_eq,
    gaugeMu_contact] at he
  have ha : deriv gaussA (1-gaussP (27/125:ℝ)) =
      (Real.sqrt 2*(48/5)*gaussA (gaussP (27/125))+
        Real.sqrt 2*(deriv gaussA (gaussP (27/125))*gaugeK2 (1/64)))/gaugeK2 (1/64) :=
    (eq_div_iff hk).2 he
  have hc : (27/125:ℝ)*(48/5)/
      (4*Real.sqrt (1-27/125)*gaugeK2 (1/64)) = 3/28 := by
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) hr) hk)).2
    rw [gaugeK2_contact_normalization]
    norm_num
  rw [gauss_complement_nativeTheta_contact, ha]
  dsimp only [nativeTheta]
  rw [gaussG_deriv (27/125) (by norm_num) (by norm_num)]
  dsimp only [gaussG]
  calc
    _ = -Real.sqrt 2*((27/125)*
          (deriv gaussA (gaussP (27/125))/(4*Real.sqrt (1-27/125))))-
        Real.sqrt 2*((27/125)*(48/5)/(4*Real.sqrt (1-27/125)*gaugeK2 (1/64)))*
          gaussA (gaussP (27/125)) := by
      field_simp [hk, hr]
      ring
    _ = _ := by rw [hc]; ring

end Row12GaussGauge

