import Tengoku.GeometricBrascampLieb.GeometricBrascampLieb.LogHeat
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Analysis.Calculus.Deriv.Inv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Taking the logarithm of a positive classical heat solution

The constructor requires the actual spatial derivatives and heat equation.
It derives the logarithmic equation by the chain and product rules.
-/

noncomputable section

namespace GeometricBrascampLieb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def logarithmicHessian (v : ℝ) (g : E) (H : E →L[ℝ] E) : E →L[ℝ] E :=
  v⁻¹ • H - (v⁻¹ ^ 2) • (innerSL ℝ g).smulRight g

theorem logarithmicHessian_trace (v : ℝ) (g : E) (H : E →L[ℝ] E) :
    LinearMap.trace ℝ E (logarithmicHessian v g H).toLinearMap + ‖v⁻¹ • g‖ ^ 2 =
      LinearMap.trace ℝ E H.toLinearMap / v := by
  simp only [logarithmicHessian, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_smul, map_sub, map_smul, smul_eq_mul]
  rw [show ((innerSL ℝ g).smulRight g).toLinearMap =
    (innerSL ℝ g).toLinearMap.smulRight g from rfl]
  rw [LinearMap.trace_smulRight, ContinuousLinearMap.toLinearMap_innerSL_apply,
    innerₛₗ_apply_apply, real_inner_self_eq_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_eq_mul_inv]
  ring

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_logarithmicGradient {u : E → ℝ} {g : E → E}
    {H : E →L[ℝ] E} {x : E} (hu : u x ≠ 0)
    (hd : HasFDerivAt u (innerSL ℝ (g x)) x) (hg : HasFDerivAt g H x) :
    HasFDerivAt (fun y => (u y)⁻¹ • g y) (logarithmicHessian (u x) (g x) H) x := by
  have hi := (hasDerivAt_inv hu).comp_hasFDerivAt x hd
  apply (hi.fun_smul hg).congr_fderiv
  ext y
  simp only [logarithmicHessian, add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_smul, smul_eq_mul]
  rw [sub_eq_add_neg, ← neg_smul]
  congr 1
  congr 1
  simp only [inv_pow, neg_mul]

/-- A positive solution of `∂t u = tr(D∇u)` gives a `LogHeatFlow`.-/
def logHeatFlowOfPositiveSolution
    (u : ℝ → E → ℝ) (g : ℝ → E → E) (H : ℝ → E → E →L[ℝ] E)
    (hpos : ∀ t, 0 < t → ∀ x, 0 < u t x)
    (hspace : ∀ t, 0 < t → ∀ x, HasFDerivAt (u t) (innerSL ℝ (g t x)) x)
    (hgrad : ∀ t, 0 < t → ∀ x, HasFDerivAt (g t) (H t x) x)
    (htime : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s => u s x) (LinearMap.trace ℝ E (H t x).toLinearMap) t) :
    LogHeatFlow E where
  logValue := fun t x => Real.log (u t x)
  gradient := fun t x => (u t x)⁻¹ • g t x
  hessian := fun t x => logarithmicHessian (u t x) (g t x) (H t x)
  space_deriv := fun t ht x => by
    simpa only [map_smul] using (hspace t ht x).log (hpos t ht x).ne'
  gradient_deriv := fun t ht x =>
    hasFDerivAt_logarithmicGradient (hpos t ht x).ne' (hspace t ht x) (hgrad t ht x)
  time_deriv := fun t ht x => by
    rw [logarithmicHessian_trace]
    exact (htime t ht x).log (hpos t ht x).ne'

end GeometricBrascampLieb
