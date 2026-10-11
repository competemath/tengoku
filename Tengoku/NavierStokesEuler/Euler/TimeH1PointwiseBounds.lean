import Tengoku.NavierStokesEuler.Euler.TerminalTimePrimitive

/-!
# Quantitative pointwise bounds for genuine time-H¹ representatives

Absolute continuity and the actual Bochner L² derivative give exact integral
increments, square-root continuity, and initial/terminal trace bounds.
-/

noncomputable section

namespace EulerTimeH1PointwiseBounds

open MeasureTheory Set EulerTimeLp EulerTerminalTimePrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T) (g : TimeLp T E) (η : ℝ → E)
  (hη : AbsolutelyContinuousOnInterval η 0 T)
  (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (g t) t)

include hT hη hder in
/-- The terminal primitive plus the actual terminal value reconstructs any H¹ representative. -/
theorem eq_primitive_add_terminal (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    η t = realPrimitive T g t + η T := by
  have hsub : AbsolutelyContinuousOnInterval (fun r => η r-η T) 0 T :=
    hη.sub ((LipschitzWith.const (η T)).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hdsub : ∀ᵐ r ∂timeMeasure T, HasDerivAt (fun s => η s-η T) (g r) r := by
    filter_upwards [hder] with r hr
    exact hr.sub_const (η T)
  have h := eq_realPrimitive_of_ac_hasDerivAt_ae T hT g (fun r => η r-η T)
    hsub hdsub (sub_self _) t ht
  exact sub_eq_iff_eq_add.mp h

end EulerTimeH1PointwiseBounds
