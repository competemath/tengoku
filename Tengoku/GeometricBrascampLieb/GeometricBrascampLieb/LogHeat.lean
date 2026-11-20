import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.Trace
import Tengoku.Seed.Analysis.InnerProductSpace.Calculus
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The differential identity behind geometric Brascamp–Lieb

`LogHeatFlow` records the logarithmic heat equation and its actual derivatives.
The results here are pointwise calculus results. They do not assert the
existence of such flows for arbitrary initial data, nor integrability.
-/

noncomputable section
open scoped BigOperators

namespace GeometricBrascampLieb

/-- A positive heat solution represented by its logarithm, gradient, and Hessian.
Only positive times are required.-/
structure LogHeatFlow (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] where
  logValue : ℝ → E → ℝ
  gradient : ℝ → E → E
  hessian : ℝ → E → E →L[ℝ] E
  space_deriv : ∀ t, 0 < t → ∀ x,
    HasFDerivAt (logValue t) (innerSL ℝ (gradient t x)) x
  gradient_deriv : ∀ t, 0 < t → ∀ x,
    HasFDerivAt (gradient t) (hessian t x) x
  time_deriv : ∀ t, 0 < t → ∀ x,
    HasDerivAt (fun s => logValue s x)
      (LinearMap.trace ℝ E (hessian t x).toLinearMap + ‖gradient t x‖ ^ 2) t

namespace Datum

variable {ι E : Type*} {F : ι → Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
  [∀ i, CompleteSpace (F i)]
  [FiniteDimensional ℝ E] [∀ i, FiniteDimensional ℝ (F i)]
  (D : Datum ι E F) (U : ∀ i, LogHeatFlow (F i))

def logProduct (t : ℝ) (x : E) : ℝ := ∑ i, D.weight i * (U i).logValue t (D.map i x)

def heatProduct (t : ℝ) (x : E) : ℝ := Real.exp (D.logProduct U t x)

def score (t : ℝ) (x : E) : E := D.synthesis fun i => (U i).gradient t (D.map i x)

def scoreDerivative (t : ℝ) (x : E) : E →L[ℝ] E :=
  ∑ i, D.weight i • (D.map i).adjoint.comp (((U i).hessian t (D.map i x)).comp (D.map i))

def timeRate (t : ℝ) (x : E) : ℝ :=
  ∑ i, D.weight i * (LinearMap.trace ℝ (F i) ((U i).hessian t (D.map i x)).toLinearMap +
    ‖(U i).gradient t (D.map i x)‖ ^ 2)

def flux (t : ℝ) (x : E) : E := D.heatProduct U t x • D.score U t x

def fluxDerivative (t : ℝ) (x : E) : E →L[ℝ] E :=
  (D.heatProduct U t x • innerSL ℝ (D.score U t x)).smulRight (D.score U t x) +
    D.heatProduct U t x • D.scoreDerivative U t x

omit [FiniteDimensional ℝ E] in
theorem heatProduct_pos (t : ℝ) (x : E) : 0 < D.heatProduct U t x := Real.exp_pos _

omit [FiniteDimensional ℝ E] in
theorem logProduct_hasDerivAt {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => D.logProduct U s x) (D.timeRate U t x) t := by
  exact HasDerivAt.fun_sum fun i _ => ((U i).time_deriv t ht (D.map i x)).const_mul _

omit [FiniteDimensional ℝ E] in
theorem heatProduct_hasDerivAt {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => D.heatProduct U s x)
      (D.heatProduct U t x * D.timeRate U t x) t :=
  (D.logProduct_hasDerivAt U ht x).exp

omit [FiniteDimensional ℝ E] in
theorem logProduct_hasFDerivAt {t : ℝ} (ht : 0 < t) (x : E) :
    HasFDerivAt (D.logProduct U t) (innerSL ℝ (D.score U t x)) x := by
  have h : HasFDerivAt (D.logProduct U t)
      (∑ i, D.weight i • (innerSL ℝ ((U i).gradient t (D.map i x))).comp (D.map i)) x :=
    HasFDerivAt.fun_sum fun i _ =>
      (((U i).space_deriv t ht (D.map i x)).comp x (D.map i).hasFDerivAt).const_mul (D.weight i)
  have he : (innerSL ℝ (D.score U t x)) =
      ∑ i, D.weight i • (innerSL ℝ ((U i).gradient t (D.map i x))).comp (D.map i) := by
    ext z
    simp only [score, innerSL_apply_apply, D.synthesis_inner, sum_apply,
      smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [he]
  exact h

omit [FiniteDimensional ℝ E] in
theorem heatProduct_hasFDerivAt {t : ℝ} (ht : 0 < t) (x : E) :
    HasFDerivAt (D.heatProduct U t)
      (D.heatProduct U t x • innerSL ℝ (D.score U t x)) x :=
  (D.logProduct_hasFDerivAt U ht x).exp

omit [FiniteDimensional ℝ E] in
theorem score_hasFDerivAt {t : ℝ} (ht : 0 < t) (x : E) :
    HasFDerivAt (D.score U t) (D.scoreDerivative U t x) x := by
  exact HasFDerivAt.fun_sum fun i _ =>
    (((D.map i).adjoint.hasFDerivAt.comp (D.map i x)
      ((U i).gradient_deriv t ht (D.map i x))).comp x (D.map i).hasFDerivAt).const_smul _

omit [FiniteDimensional ℝ E] in
theorem flux_hasFDerivAt {t : ℝ} (ht : 0 < t) (x : E) :
    HasFDerivAt (D.flux U t) (D.fluxDerivative U t x) x := by
  change HasFDerivAt (fun y => D.heatProduct U t y • D.score U t y) _ x
  simpa only [fluxDerivative, add_comm] using
    (D.heatProduct_hasFDerivAt U ht x).fun_smul (D.score_hasFDerivAt U ht x)

theorem trace_scoreDerivative (t : ℝ) (x : E) :
    LinearMap.trace ℝ E (D.scoreDerivative U t x).toLinearMap =
      ∑ i, D.weight i * LinearMap.trace ℝ (F i) ((U i).hessian t (D.map i x)).toLinearMap := by
  simp only [scoreDerivative, ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_smul, map_sum, map_smul, smul_eq_mul, D.trace_lift]

theorem trace_fluxDerivative (t : ℝ) (x : E) :
    LinearMap.trace ℝ E (D.fluxDerivative U t x).toLinearMap =
      D.heatProduct U t x * (‖D.score U t x‖ ^ 2 +
        ∑ i, D.weight i * LinearMap.trace ℝ (F i) ((U i).hessian t (D.map i x)).toLinearMap) := by
  simp only [fluxDerivative, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, map_add, map_smul, smul_eq_mul]
  rw [show ((D.heatProduct U t x • innerSL ℝ (D.score U t x)).smulRight
      (D.score U t x)).toLinearMap =
    (D.heatProduct U t x • (innerSL ℝ (D.score U t x)).toLinearMap).smulRight
      (D.score U t x) from rfl]
  rw [LinearMap.trace_smulRight, LinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.toLinearMap_innerSL_apply, innerₛₗ_apply_apply,
    real_inner_self_eq_norm_sq, D.trace_scoreDerivative]
  ring

/-- The local heat-flow defect is exactly the nonnegative geometric quadratic defect.-/
theorem timeRate_sub_divergence (t : ℝ) (x : E) :
    D.heatProduct U t x * D.timeRate U t x -
      LinearMap.trace ℝ E (D.fluxDerivative U t x).toLinearMap =
    D.heatProduct U t x *
      ((∑ i, D.weight i * ‖(U i).gradient t (D.map i x)‖ ^ 2) - ‖D.score U t x‖ ^ 2) := by
  rw [D.trace_fluxDerivative]
  simp only [timeRate, mul_add, Finset.sum_add_distrib]
  ring

theorem divergence_le_time_derivative (t : ℝ) (x : E) :
    LinearMap.trace ℝ E (D.fluxDerivative U t x).toLinearMap ≤
      D.heatProduct U t x * D.timeRate U t x := by
  apply sub_nonneg.mp
  rw [D.timeRate_sub_divergence]
  exact mul_nonneg (D.heatProduct_pos U t x).le (D.defect_nonneg _)

end Datum
end GeometricBrascampLieb
