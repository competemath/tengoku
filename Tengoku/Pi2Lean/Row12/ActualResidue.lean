import Tengoku.Pi2Lean.Row12.AnalyticSecondUniqueness
import Tengoku.Pi2Lean.Row12.Residue
import Tengoku.Pi2Lean.Row12EulerSupport.Wronskian
import Tengoku.Pi2Lean.Row12GaussGauge.Contact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.nativeF_gaussG_eventually` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeEuler_one_gaussG` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeEuler_two_gaussG` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.gaussG_second_contact` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.actual_native_contact_residue` (it only prints; the queue checks the axioms of every declaration). -/

open Filter Set Metric
open scoped Topology

namespace Row12

/--
@isnad1 id=eventual.1h1v.s5.8e4c26459152 from=translated src=- shape=4ccb8ba2 vocab=0dec1bfe
-/
theorem nativeF_gaussG_eventually (q : ℝ) (hq : ‖q‖ < 1) :
    nativeF =ᶠ[nhds q] (fun z : ℝ => gaussG z^2) := by
  filter_upwards [isOpen_ball.mem_nhds (by simpa using hq : q ∈ ball (0:ℝ) 1)] with z hz
  exact nativeF_eq_gaussG_square z (by simpa using hz)

/--
@isnad1 id=eq.1h1v.s5.58f78831b670 from=translated src=- shape=3d02deca vocab=be00e94d
-/
theorem nativeEuler_one_gaussG (q : ℝ) (hq : ‖q‖ < 1) :
    nativeEuler 1 q = 2*gaussG q*nativeTheta gaussG q := by
  have hqa : -1 < q ∧ q < 1 := by simpa only [Real.norm_eq_abs,abs_lt] using hq
  have ha := (gaussG_analyticAt q (by linarith [hqa.1]) hqa.2).differentiableAt.hasDerivAt
  have he := nativeF_gaussG_eventually q hq
  change nativeEuler (0+1) q = _
  rw [nativeEuler_succ_eq 0 q hq]
  change q*deriv nativeF q = _
  rw [he.deriv_eq,(ha.fun_pow 2).deriv]
  simp only [nativeTheta]
  ring

/--
@isnad1 id=eq.1h1v.s6.2c4881bdd2aa from=translated src=- shape=8e8f03d7 vocab=baa2c4e6
-/
theorem nativeEuler_two_gaussG (q : ℝ) (hq : ‖q‖ < 1) :
    nativeEuler 2 q = 2*(nativeTheta gaussG q)^2+
      2*gaussG q*nativeTheta (nativeTheta gaussG) q := by
  have hqa : -1 < q ∧ q < 1 := by simpa only [Real.norm_eq_abs,abs_lt] using hq
  have ha := gaussG_analyticAt q (by linarith [hqa.1]) hqa.2
  have hta : AnalyticAt ℝ (nativeTheta gaussG) q := analyticAt_id.mul ha.deriv
  have he : nativeEuler 1 =ᶠ[nhds q]
      (fun z : ℝ => 2*gaussG z*nativeTheta gaussG z) := by
    filter_upwards [isOpen_ball.mem_nhds (by simpa using hq : q ∈ ball (0:ℝ) 1)] with z hz
    exact nativeEuler_one_gaussG z (by simpa using hz)
  have hd := (ha.differentiableAt.hasDerivAt.const_mul 2).fun_mul
    hta.differentiableAt.hasDerivAt
  rw [nativeEuler_succ_eq 1 q hq,he.deriv_eq,hd.deriv]
  simp only [nativeTheta]
  ring

/--
@isnad1 id=eq.0h0v.s7.ee62c81e2f75 from=translated src=- shape=52c9aa85 vocab=9170f171
-/
theorem gaussG_second_contact :
    nativeTheta (nativeTheta gaussG) (27/125) =
      (27/196)*nativeTheta gaussG (27/125)+(15/1568)*gaussG (27/125) := by
  have he := gaussG_nativeSecond (27/125) (by norm_num) (by norm_num)
  linear_combination (125/14112:ℝ)*he

/--
@isnad1 id=eq.0h0v.s7.77a7f300dbf5 from=translated src=- shape=f39ad361 vocab=603a53b1
-/
theorem actual_native_contact_residue :
    residueForm (nativeF (27/125)) (nativeEuler 1 (27/125))
      (nativeEuler 2 (27/125)) = 1/(36*Real.pi^2) := by
  have hq : ‖(27/125:ℝ)‖ < 1 := by norm_num
  rw [nativeF_eq_gaussG_square _ hq,nativeEuler_one_gaussG _ hq,
    nativeEuler_two_gaussG _ hq,gaussG_second_contact]
  exact residue_at_wronskian (gaussG (27/125)) (nativeTheta gaussG (27/125))
    (gaussA (1-gaussP (27/125)))
    (nativeTheta (fun q : ℝ => gaussA (1-gaussP q)) (27/125))
    Row12GaussGauge.gauss_contact_value Row12GaussGauge.gauss_contact_nativeTheta
    (Row12EulerSupport.gaussNativeWronskian (27/125) (by norm_num) (by norm_num))

end Row12

