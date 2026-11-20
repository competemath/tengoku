import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.LogHeat
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit Gaussian logarithmic heat flows

This is an actual family of heat solutions, for arbitrary centers and
normalization constants, in every finite-dimensional real inner product space.
It checks the sign and diffusion normalization used by the abstract calculus.
-/

noncomputable section

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def gaussianLog (a : ℝ) (z : E) (t : ℝ) (x : E) : ℝ :=
  a - (Module.finrank ℝ E : ℝ) / 2 * Real.log t - (4 * t)⁻¹ * ‖x - z‖ ^ 2

def gaussianScore (z : E) (t : ℝ) (x : E) : E := -(2 * t)⁻¹ • (x - z)

def gaussianHessian (t : ℝ) : E →L[ℝ] E := -(2 * t)⁻¹ • ContinuousLinearMap.id ℝ E

omit [FiniteDimensional ℝ E] in
theorem gaussianLog_hasFDerivAt (a : ℝ) (z : E) (t : ℝ) (x : E) :
    HasFDerivAt (gaussianLog a z t) (innerSL ℝ (gaussianScore z t x)) x := by
  have h := ((((hasFDerivAt_id (𝕜 := ℝ) x).sub_const z).norm_sq).const_mul (4 * t)⁻¹).const_sub
    (a - (Module.finrank ℝ E : ℝ) / 2 * Real.log t)
  have he : -((4 * t)⁻¹ • (2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ E))) =
      innerSL ℝ (gaussianScore z t x) := by
    ext y
    simp only [gaussianScore, innerSL_apply_apply, real_inner_smul_left,
      neg_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    field_simp
    ring
  rw [← he]
  exact h

omit [FiniteDimensional ℝ E] in
theorem gaussianScore_hasFDerivAt (z : E) (t : ℝ) (x : E) :
    HasFDerivAt (gaussianScore z t) (gaussianHessian t) x := by
  exact ((hasFDerivAt_id x).sub_const z).fun_const_smul _

theorem gaussianLog_hasDerivAt (a : ℝ) (z : E) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => gaussianLog a z s x)
      (LinearMap.trace ℝ E (gaussianHessian t).toLinearMap + ‖gaussianScore z t x‖ ^ 2) t := by
  have hlog := ((Real.hasDerivAt_log ht.ne').const_mul
    ((Module.finrank ℝ E : ℝ) / 2)).const_sub a
  have hi := (((hasDerivAt_id t).const_mul 4).inv (mul_ne_zero (by norm_num) ht.ne')).mul_const
    (‖x - z‖ ^ 2)
  have h := hlog.sub hi
  apply h.congr_deriv
  simp only [gaussianHessian, gaussianScore, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, map_smul, LinearMap.trace_id, smul_eq_mul,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, id_eq]
  field_simp
  ring

/-- `exp (gaussianLog a z t x)` solves the heat equation `∂t u = Δu`.-/
def gaussianLogHeatFlow (a : ℝ) (z : E) : LogHeatFlow E where
  logValue := gaussianLog a z
  gradient := gaussianScore z
  hessian := fun t _ => gaussianHessian t
  space_deriv := fun t _ => gaussianLog_hasFDerivAt a z t
  gradient_deriv := fun t _ => gaussianScore_hasFDerivAt z t
  time_deriv := fun _ ht => gaussianLog_hasDerivAt a z ht

end GeometricBrascampLieb
