import Tengoku.Pi2Lean.Row12GaussGauge.Algebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeK1_sq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeK2_sq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP1_product` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP2_product` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP1_pullback_first` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP2_pullback_first` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP1_pullback_constant` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeP2_pullback_constant` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY1_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY2_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY1_second_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY2_second_deriv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.theta_second_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY1_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12GaussGauge.gaugeY2_equation` (it only prints; the queue checks the axioms of every declaration). -/

open Filter Set
open Row12

namespace Row12GaussGauge

/--
@isnad1 id=eq.2h1v.s7.8fa5a1bebee3 from=translated src=- shape=5bd7b618 vocab=02a74876
-/
theorem gaugeK1_sq (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    gaugeK1 z ^ 2 = 746496*z^2/((1+64*z)*(1+16*z)^5) := by
  have hr := gaugeRatio_sq 16 z hS hD
  simp only [gaugeK1, gaugeBase, mul_pow, div_pow]
  rw [hr]
  field_simp [ne_of_gt hS, ne_of_gt hD]
  ring

/--
@isnad1 id=eq.2h1v.s7.2ad0e4cb0da3 from=translated src=- shape=8845e782 vocab=0b61c70b
-/
theorem gaugeK2_sq (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    gaugeK2 z ^ 2 = 186624/((1+64*z)*(1+256*z)^5) := by
  have hr := gaugeRatio_sq 256 z hS hD
  simp only [gaugeK2, gaugeBase, mul_pow, div_pow]
  rw [hr]
  field_simp [ne_of_gt hS, ne_of_gt hD]
  ring

/--
@isnad1 id=eq.2h1v.s7.60eec5c4bb0c from=translated src=- shape=72d4ff6b vocab=67334456
-/
theorem gaugeP1_product (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+16*z) :
    gaugeP1 z*(1-gaugeP1 z) = 432*z^2/(1+16*z)^3 := by
  linear_combination gaugeP1_quadratic z hS hD / 4

/--
@isnad1 id=eq.2h1v.s7.1f75d0ed66e4 from=translated src=- shape=cc668f8c vocab=bd677304
-/
theorem gaugeP2_product (z : ℝ) (hS : 0 < 1+64*z) (hD : 0 < 1+256*z) :
    gaugeP2 z*(1-gaugeP2 z) = 432*z/(1+256*z)^3 := by
  linear_combination gaugeP2_quadratic z hS hD / 4

/--
@isnad1 id=eq.2h1v.s8.dbd004ebe29e from=translated src=- shape=43f1fe84 vocab=d8577247
-/
theorem gaugeP1_pullback_first (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    gaugeP1 z*(1-gaugeP1 z)*
        (z*gaugeK1 z+z^2*(gaugeK1 z*(1/z+gaugeT 16 z))+
          gaugeB1 z*z*gaugeK1 z) =
      z^2*gaugeK1 z^2*(1-2*gaugeP1 z) := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+16*z := by positivity
  have ht : 1-8*z ≠ 0 := by linarith
  rw [gaugeP1_product z hS hD, gaugeK1_sq z hS hD]
  unfold gaugeK1 gaugeBase gaugeT gaugeB1 gaugeP1
  field_simp [ne_of_gt hz, ne_of_gt hS, ne_of_gt hD, ht]
  ring

/--
@isnad1 id=eq.2h1v.s7.746c36f7963e from=translated src=- shape=3ceb2d9b vocab=b04625ec
-/
theorem gaugeP2_pullback_first (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    gaugeP2 z*(1-gaugeP2 z)*
        (z*gaugeK2 z+z^2*(gaugeK2 z*gaugeT 256 z)+
          gaugeB2 z*z*gaugeK2 z) =
      z^2*gaugeK2 z^2*(1-2*gaugeP2 z) := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+256*z := by positivity
  have ht : 1-8*z ≠ 0 := by linarith
  rw [gaugeP2_product z hS hD, gaugeK2_sq z hS hD]
  unfold gaugeK2 gaugeBase gaugeT gaugeB2 gaugeP2
  field_simp [ne_of_gt hz, ne_of_gt hS, ne_of_gt hD, ht]
  ring

/--
@isnad1 id=eq.1h1v.s6.1dc44c175c8b from=translated src=- shape=1f40eff0 vocab=fe9cbefd
-/
theorem gaugeP1_pullback_constant (z : ℝ) (hz : 0 < z) :
    gaugeP1 z*(1-gaugeP1 z)*gaugeC1 z = -(5/36:ℝ)*z^2*gaugeK1 z^2 := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+16*z := by positivity
  rw [gaugeP1_product z hS hD, gaugeK1_sq z hS hD]
  unfold gaugeC1
  field_simp [ne_of_gt hS, ne_of_gt hD]
  ring

/--
@isnad1 id=eq.1h1v.s6.ab466f8beb6d from=translated src=- shape=1f40eff0 vocab=b63d501e
-/
theorem gaugeP2_pullback_constant (z : ℝ) (hz : 0 < z) :
    gaugeP2 z*(1-gaugeP2 z)*gaugeC2 z = -(5/36:ℝ)*z^2*gaugeK2 z^2 := by
  have hS : 0 < 1+64*z := by positivity
  have hD : 0 < 1+256*z := by positivity
  rw [gaugeP2_product z hS hD, gaugeK2_sq z hS hD]
  unfold gaugeC2
  field_simp [ne_of_gt hS, ne_of_gt hD]
  ring

/--
@isnad1 id=hasderiv.2h1v.s6.34e0703a968b from=translated src=- shape=7017ca3e vocab=af02c7ca
-/
theorem gaugeY1_hasDerivAt (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    HasDerivAt gaugeY1 (deriv gaussA (gaugeP1 z)*gaugeK1 z) z := by
  exact (gaussA_analyticAt (gaugeP1 z) (gaugeP1_norm_lt_one z hz hz1)).differentiableAt.hasDerivAt.comp z
      (gaugeP1_hasDerivAt z (by positivity) (by positivity))

/--
@isnad1 id=hasderiv.2h1v.s6.4548b6d93e21 from=translated src=- shape=7017ca3e vocab=f24dd48b
-/
theorem gaugeY2_hasDerivAt (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    HasDerivAt gaugeY2 (deriv gaussA (gaugeP2 z)*gaugeK2 z) z := by
  exact (gaussA_analyticAt (gaugeP2 z) (gaugeP2_norm_lt_one z hz hz1)).differentiableAt.hasDerivAt.comp z
      (gaugeP2_hasDerivAt z (by positivity) (by positivity))

/--
@isnad1 id=eq.2h1v.s8.797ebdc5fb94 from=translated src=- shape=c6f59ca4 vocab=f25bfa3f
-/
theorem gaugeY1_second_deriv (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    deriv (deriv gaugeY1) z =
      deriv (deriv gaussA) (gaugeP1 z)*gaugeK1 z^2+
        deriv gaussA (gaugeP1 z)*(gaugeK1 z*(1/z+gaugeT 16 z)) := by
  have ha := (gaussA_analyticAt (gaugeP1 z) (gaugeP1_norm_lt_one z hz hz1)).deriv.differentiableAt.hasDerivAt
  have hd := (ha.comp z (gaugeP1_hasDerivAt z (by positivity) (by positivity))).mul
    (gaugeK1_hasDerivAt z (ne_of_gt hz) (by positivity) (by positivity))
  have he : deriv gaugeY1 =ᶠ[nhds z]
      (fun x => deriv gaussA (gaugeP1 x)*gaugeK1 x) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Ioo (0:ℝ) (1/8) from ⟨hz,hz1⟩)] with x hx
    exact (gaugeY1_hasDerivAt x hx.1 hx.2).deriv
  rw [(hd.congr_of_eventuallyEq he).deriv]
  simp only [Function.comp_apply]
  ring

/--
@isnad1 id=eq.2h1v.s7.368e0d489a83 from=translated src=- shape=9ead88d2 vocab=11b11492
-/
theorem gaugeY2_second_deriv (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    deriv (deriv gaugeY2) z =
      deriv (deriv gaussA) (gaugeP2 z)*gaugeK2 z^2+
        deriv gaussA (gaugeP2 z)*(gaugeK2 z*gaugeT 256 z) := by
  have ha := (gaussA_analyticAt (gaugeP2 z) (gaugeP2_norm_lt_one z hz hz1)).deriv.differentiableAt.hasDerivAt
  have hd := (ha.comp z (gaugeP2_hasDerivAt z (by positivity) (by positivity))).mul
    (gaugeK2_hasDerivAt z (by positivity) (by positivity))
  have he : deriv gaugeY2 =ᶠ[nhds z]
      (fun x => deriv gaussA (gaugeP2 x)*gaugeK2 x) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show z ∈ Ioo (0:ℝ) (1/8) from ⟨hz,hz1⟩)] with x hx
    exact (gaugeY2_hasDerivAt x hx.1 hx.2).deriv
  rw [(hd.congr_of_eventuallyEq he).deriv]
  simp only [Function.comp_apply]
  ring

/--
@isnad1 id=eq.1h2v.s7.aa78c89e13c7 from=translated src=- shape=e63c2e83 vocab=937fc1bd
-/
theorem theta_second_eq {f : ℝ → ℝ} {z : ℝ} (hf : AnalyticAt ℝ f z) :
    nativeTheta (nativeTheta f) z = z*deriv f z+z^2*deriv (deriv f) z := by
  have hd := (hasDerivAt_id z).mul hf.deriv.differentiableAt.hasDerivAt
  change z*deriv (fun x => x*deriv f x) z = _
  have he : deriv (fun x => x*deriv f x) z = deriv f z+z*deriv (deriv f) z := by
    convert! hd.deriv using 1
    simp only [id_eq, one_mul]
  rw [he]
  ring

/--
@isnad1 id=eq.2h1v.s6.2d82fa4f11fc from=translated src=- shape=f86e5d60 vocab=f555dd57
-/
theorem gaugeY1_equation (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    nativeTheta (nativeTheta gaugeY1) z+gaugeB1 z*nativeTheta gaugeY1 z+
      gaugeC1 z*gaugeY1 z = 0 := by
  have hp : gaugeP1 z*(1-gaugeP1 z) ≠ 0 := by
    rw [gaugeP1_product z (by positivity) (by positivity)]
    positivity
  have he := gaussA_equation (gaugeP1 z) (gaugeP1_norm_lt_one z hz hz1)
  have hl := gaugeP1_pullback_first z hz hz1
  have hc := gaugeP1_pullback_constant z hz
  apply (mul_eq_zero.mp (show gaugeP1 z*(1-gaugeP1 z)*
      (nativeTheta (nativeTheta gaugeY1) z+gaugeB1 z*nativeTheta gaugeY1 z+
        gaugeC1 z*gaugeY1 z) = 0 from ?_)).resolve_left hp
  rw [theta_second_eq (gaugeY1_analyticAt z hz hz1), nativeTheta,
    (gaugeY1_hasDerivAt z hz hz1).deriv, gaugeY1_second_deriv z hz hz1]
  dsimp only [gaugeY1]
  linear_combination (z^2*gaugeK1 z^2)*he+
    deriv gaussA (gaugeP1 z)*hl+gaussA (gaugeP1 z)*hc

/--
@isnad1 id=eq.2h1v.s6.72c2faa613d5 from=translated src=- shape=f86e5d60 vocab=1492f03f
-/
theorem gaugeY2_equation (z : ℝ) (hz : 0 < z) (hz1 : z < 1/8) :
    nativeTheta (nativeTheta gaugeY2) z+gaugeB2 z*nativeTheta gaugeY2 z+
      gaugeC2 z*gaugeY2 z = 0 := by
  have hp : gaugeP2 z*(1-gaugeP2 z) ≠ 0 := by
    rw [gaugeP2_product z (by positivity) (by positivity)]
    positivity
  have he := gaussA_equation (gaugeP2 z) (gaugeP2_norm_lt_one z hz hz1)
  have hl := gaugeP2_pullback_first z hz hz1
  have hc := gaugeP2_pullback_constant z hz
  apply (mul_eq_zero.mp (show gaugeP2 z*(1-gaugeP2 z)*
      (nativeTheta (nativeTheta gaugeY2) z+gaugeB2 z*nativeTheta gaugeY2 z+
        gaugeC2 z*gaugeY2 z) = 0 from ?_)).resolve_left hp
  rw [theta_second_eq (gaugeY2_analyticAt z hz hz1), nativeTheta,
    (gaugeY2_hasDerivAt z hz hz1).deriv, gaugeY2_second_deriv z hz hz1]
  dsimp only [gaugeY2]
  linear_combination (z^2*gaugeK2 z^2)*he+
    deriv gaussA (gaugeP2 z)*hl+gaussA (gaugeP2 z)*hc

end Row12GaussGauge

