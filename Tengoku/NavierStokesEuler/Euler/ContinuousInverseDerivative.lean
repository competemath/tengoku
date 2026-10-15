import Tengoku

/-! An actual continuous inverse has the inverse Jacobian as its derivative.
This is the easy half of the inverse function theorem; no differentiability
of the inverse is an independent assumption. -/

noncomputable section

open scoped Topology

namespace EulerContinuousInverseDerivative

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
@isnad1 id=hasfderi.4h7v.s9.98f7ea7f2a44 from=translated src=- shape=57b13535 vocab=c9866079
-/
theorem hasFDerivAt_inverse
    (X : F → E) (Y : E → F) (x : E)
    (J : F →L[ℝ] E) (I : E →L[ℝ] F)
    (hY : ContinuousAt Y x) (hX : HasFDerivAt X J (Y x))
    (hXY : ∀ᶠ y in 𝓝 x, X (Y y) = y)
    (hI : Function.LeftInverse I J) : HasFDerivAt Y I x := by
  have h := HasFDerivAt.of_comp_of_leftInverse (f'symm := I)
    hY hX (hasFDerivAt_id x) hXY hI
  simpa only [ContinuousLinearMap.comp_id] using h

end EulerContinuousInverseDerivative
