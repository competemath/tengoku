import Tengoku.Pi2Lean.Row12.AngularSourceCertificate
import Tengoku.Pi2Lean.Row12.AngularContourFrame
import Tengoku.Pi2Lean.Row12.OuterPrimitive
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.angular_source_actual_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_polynomial_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_primitive_entry_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_primitive_pair_analyticAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_primitive_deriv_circleIntegrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_primitive_deriv_circleIntegral_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_circleIntegrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_integral_eq_actual` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_coordinates_eq_outer` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_lambda_eq_outer` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.angular_source_integral_eq_outer` (it only prints; the queue checks the axioms of every declaration). -/

open MeasureTheory Set Metric Complex Filter
open scoped Topology

namespace Row12

/--
@isnad1 id=analytic.0h2v.s5.a362f5243074 from=translated src=- shape=ec7338a6 vocab=4669d060
-/
theorem angular_source_polynomial_analyticAt (c : Fin 6 → ℂ) (s : ℂ) :
    AnalyticAt ℂ (angularSourcePolynomial c) s := by
  unfold angularSourcePolynomial
  exact Finset.analyticAt_fun_sum _ (fun k _ =>
    analyticAt_const.mul (analyticAt_id.pow k.val))

/--
@isnad1 id=analytic.4h4v.s7.6ebdfefd948e from=translated src=- shape=3b712f43 vocab=43a2b519
-/
theorem angular_source_primitive_entry_analyticAt (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0) (hs0 : s ≠ 0)
    (i j : Fin 3) :
    AnalyticAt ℂ (fun z => angularLiteralPrimitive x z i j) s := by
  change AnalyticAt ℂ (fun z =>
    angularSourcePolynomial (angularPrimitiveCoefficients x i j) z /
      (angularPrimitiveScale x i j * z ^ angularPrimitivePole i j)) s
  exact (angular_source_polynomial_analyticAt _ s).div
    (analyticAt_const.mul (analyticAt_id.pow (angularPrimitivePole i j)))
    (mul_ne_zero (angular_source_scale_ne_zero x hx0 hx25 hx50 i j)
      (pow_ne_zero _ hs0))

/--
@isnad1 id=analytic.6h2v.s7.f4121b43fa99 from=translated src=- shape=c881abd8 vocab=93e5f963
-/
theorem angular_source_primitive_pair_analyticAt (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0) (hs0 : s ≠ 0)
    (hs : ‖s‖ < 1) (hb : ‖(angularSourceLambda x)/s‖ < 1) :
    AnalyticAt ℂ (angularSourcePrimitivePair x) s := by
  have hdiv : AnalyticAt ℂ (fun z : ℂ => (angularSourceLambda x)/z) s :=
    analyticAt_const.div analyticAt_id hs0
  have hY (i : Fin 3) : AnalyticAt ℂ (fun z => nativeState z i) s :=
    nativeState_entry_analyticAt i s hs
  have hZ (i : Fin 3) :
      AnalyticAt ℂ (fun z => nativeState ((angularSourceLambda x)/z) i) s :=
    (nativeState_entry_analyticAt i ((angularSourceLambda x)/s) hb).fun_comp hdiv
  unfold angularSourcePrimitivePair angularTensorPair
  exact Finset.analyticAt_fun_sum _ (fun i _ =>
    Finset.analyticAt_fun_sum _ (fun j _ =>
      ((angular_source_primitive_entry_analyticAt x s hx0 hx25 hx50 hs0 i j).mul
        (hY i)).mul (hZ j)))

/--
@isnad1 id=circlein.6h2v.s7.de2be76dcba9 from=translated src=- shape=7bf84e05 vocab=bc9bab24
-/
theorem angular_source_primitive_deriv_circleIntegrable (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖angularSourceLambda x‖ < r) :
    CircleIntegrable (deriv (angularSourcePrimitivePair x)) 0 r := by
  have hc : ContinuousOn (deriv (angularSourcePrimitivePair x)) (sphere 0 r) := by
    intro s hs
    obtain ⟨hs0,_,_,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
    exact (angular_source_primitive_pair_analyticAt x s hx0 hx25 hx50 hs0 hsn hbn).deriv.continuousAt.continuousWithinAt
  exact hc.circleIntegrable hr.le

/--
@isnad1 id=eq.6h2v.s7.2aea2536851d from=translated src=- shape=e45a838a vocab=2fc5ccd3
-/
theorem angular_source_primitive_deriv_circleIntegral_zero (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖angularSourceLambda x‖ < r) :
    (∮ s in C(0,r), deriv (angularSourcePrimitivePair x) s) = 0 := by
  apply circleIntegral_exactDerivative (angularSourcePrimitivePair x)
    (deriv (angularSourcePrimitivePair x)) hr.le
  intro s hs
  obtain ⟨hs0,_,_,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
  exact (angular_source_primitive_pair_hasDerivAt x s hx0 hx25 hx50 hs0 hsn hbn).differentiableAt.hasDerivAt

/--
@isnad1 id=circlein.6h2v.s7.3b0c2ea1df69 from=translated src=- shape=992b6228 vocab=8710bf87
-/
theorem angular_source_circleIntegrable (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖angularSourceLambda x‖ < r) :
    CircleIntegrable (angularSourceIntegrand x) 0 r := by
  apply (circleIntegrable_congr (by
    intro s hs
    have hsp : s ∈ sphere (0:ℂ) r := by
      simpa only [abs_of_nonneg hr.le] using hs
    obtain ⟨hs0,hs1,hsl,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hsp
    exact angular_source_actual_identity x s hx0 hx25 hx50 hs0 hs1 hsl hsn hbn)).2
  exact (angular_nf_circleIntegrable (angularSourceCoordinates x)
    (angularSourceLambda x) hr hr1 hl).add
    (angular_source_primitive_deriv_circleIntegrable x hx0 hx25 hx50 hr hr1 hl)

noncomputable def angularSourceIntegral (x : ℂ) (r : ℝ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * ∮ s in C(0,r), angularSourceIntegrand x s

/--
@isnad1 id=eq.6h2v.s7.8029504404d6 from=translated src=- shape=dca76c71 vocab=3a012c96
-/
theorem angular_source_integral_eq_actual (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖angularSourceLambda x‖ < r) :
    angularSourceIntegral x r =
      dotProduct (angularSourceCoordinates x) (sixthNormalState (angularSourceLambda x)) := by
  have hFi := angular_nf_circleIntegrable (angularSourceCoordinates x)
    (angularSourceLambda x) hr hr1 hl
  have hPi := angular_source_primitive_deriv_circleIntegrable x hx0 hx25 hx50 hr hr1 hl
  have hPzero := angular_source_primitive_deriv_circleIntegral_zero x hx0 hx25 hx50 hr hr1 hl
  have he : (∮ s in C(0,r), angularSourceIntegrand x s) =
      (∮ s in C(0,r), angularNFIntegrand (angularSourceCoordinates x)
        (angularSourceLambda x) s) := by
    calc
      _ = ∮ s in C(0,r), angularNFIntegrand (angularSourceCoordinates x)
          (angularSourceLambda x) s + deriv (angularSourcePrimitivePair x) s := by
        apply circleIntegral.integral_congr hr.le
        intro s hs
        obtain ⟨hs0,hs1,hsl,hsn,hbn⟩ := angular_circle_domain hr hr1 hl hs
        exact angular_source_actual_identity x s hx0 hx25 hx50 hs0 hs1 hsl hsn hbn
      _ = _ := by rw [circleIntegral.integral_add hFi hPi, hPzero, add_zero]
  unfold angularSourceIntegral
  rw [he]
  exact angular_nf_integral_eq_actual (angularSourceCoordinates x)
    (angularSourceLambda x) (angular_source_lambda_ne_zero x hx0) hr hr1 hl

/--
@isnad1 id=eq.0h1v.s3.0dfc96c1e7c8 from=translated src=- shape=9a282f00 vocab=1ed654ac
-/
theorem angular_source_coordinates_eq_outer (x : ℂ) :
    angularSourceCoordinates x = outerSourceRow x := by
  rfl

/--
@isnad1 id=eq.0h1v.s3.736792faa36e from=translated src=- shape=0fc427d2 vocab=807db95a
-/
theorem angular_source_lambda_eq_outer (x : ℂ) :
    angularSourceLambda x = outerPrimitiveLambda x := by
  rfl

/--
@isnad1 id=eq.6h2v.s7.6c07dae664ea from=translated src=- shape=dca76c71 vocab=7bbea839
-/
theorem angular_source_integral_eq_outer (x : ℂ) {r : ℝ}
    (hx0 : x ≠ 0) (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hr : 0 < r) (hr1 : r < 1) (hl : ‖outerPrimitiveLambda x‖ < r) :
    angularSourceIntegral x r =
      dotProduct (outerSourceRow x) (sixthNormalState (outerPrimitiveLambda x)) := by
  rw [← angular_source_coordinates_eq_outer, ← angular_source_lambda_eq_outer]
  exact angular_source_integral_eq_actual x hx0 hx25 hx50 hr hr1 hl

end Row12

