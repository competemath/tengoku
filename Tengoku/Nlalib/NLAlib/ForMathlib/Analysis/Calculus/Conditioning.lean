import Tengoku.Seed.Analysis.Calculus.FDeriv.Basic
import Tengoku.Seed.Analysis.Calculus.Deriv.Basic
import Tengoku.Seed.Analysis.Normed.Operator.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Condition numbers of differentiable maps

The absolute condition number of a map between real normed spaces is the operator norm of its
Fréchet derivative, and the normwise relative condition number scales it by `‖x‖/‖f x‖`.
Gautschi 2004, Definitions 2.3–2.6. The matrix consequences (the Euclidean Jacobian, the
componentwise relative condition number and the bound by the matrix condition number) are in
`NLAlib.Matrix.Perturbation.MapConditioning`.
-/

noncomputable section

namespace NLAlib

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The absolute condition number of `f` at `x`: the operator norm of the Fréchet derivative.
Gautschi 2004, Definition 2.3. Mathlib's `fderiv` is zero where `f` is not differentiable, so
the value is `0` there; the theorems about it take `DifferentiableAt ℝ f x`.-/
def mapAbsCondition (f : E → F) (x : E) : ℝ := ‖fderiv ℝ f x‖

/-- The normwise relative condition number of `f` at `x`: the absolute condition number scaled
by `‖x‖ / ‖f x‖`. Gautschi 2004, Definition 2.4 (`0` when `f x = 0`).-/
def mapNormRelativeCondition (f : E → F) (x : E) : ℝ :=
  mapAbsCondition f x * ‖x‖ / ‖f x‖

/-- A specified Fréchet derivative computes the absolute condition number.
Gautschi 2004, Definition 2.3.
@isnad1 id=eq.1h5v.s7.0f6abb558a04 from=translated src=- shape=8871d690 vocab=7100b0fa
-/
theorem mapAbsCondition_eq_norm_of_hasFDerivAt {f : E → F} {x : E}
    {L : E →L[ℝ] F} (hf : HasFDerivAt f L x) : mapAbsCondition f x = ‖L‖ := by
  rw [mapAbsCondition, hf.fderiv]

/-- In one dimension the absolute condition number is the absolute derivative.
Gautschi 2004, Definition 2.5.
@isnad1 id=eq.0h2v.s5.b399a06d330e from=translated src=- shape=57156c0a vocab=b9c72797
-/
theorem mapAbsCondition_eq_abs_deriv (f : ℝ → ℝ) (x : ℝ) :
    mapAbsCondition f x = |deriv f x| := by
  rw [mapAbsCondition, ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]

/-- In one dimension the relative condition number is the absolute logarithmic derivative
`|x f'(x) / f(x)|`. Gautschi 2004, Definition 2.6.
@isnad1 id=eq.0h2v.s6.1207a42941bb from=translated src=- shape=13ed277c vocab=c468bb83
-/
theorem mapNormRelativeCondition_eq_abs_mul_deriv_div (f : ℝ → ℝ) (x : ℝ) :
    mapNormRelativeCondition f x = |x * deriv f x / f x| := by
  rw [mapNormRelativeCondition, mapAbsCondition_eq_abs_deriv]
  simp only [Real.norm_eq_abs, abs_div, abs_mul]
  ring

end NLAlib
