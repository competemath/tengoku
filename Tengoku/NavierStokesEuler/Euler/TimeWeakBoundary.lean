import Tengoku.NavierStokesEuler.Euler.TimeWeakDerivative

/-!
# Recovering the actual initial trace from a full time weak identity

The terminal primitive and its exact integration-by-parts identity identify
both an absolutely continuous representative and its initial trace.  The
boundary value is a conclusion of testing against all terminal-zero H¹ paths.
-/

noncomputable section

namespace EulerTimeWeakBoundary

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerTerminalTimePrimitive
  EulerTimeWeakDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual AC representative with the boundary value forced by the weak form. -/
def boundaryRepresentative (T : ℝ) (hT : 0 ≤ T) (h : TimeLp T E) (b : E) : ℝ → E :=
  fun t => realPrimitive T h t + (b-initialTrace T hT h)

omit [CompleteSpace E] in
/-- This representative has precisely the initial value appearing in the weak form. -/
@[simp] theorem boundaryRepresentative_initial (T : ℝ) (hT : 0 ≤ T) (h : TimeLp T E) (b : E) :
    boundaryRepresentative T hT h b 0 = b := by
  change initialTrace T hT h + (b-initialTrace T hT h) = b
  abel

end EulerTimeWeakBoundary
