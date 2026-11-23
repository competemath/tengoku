import Tengoku.NavierStokesEuler.Euler.BoundedFlowContinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Periodicity of the prescribed velocity gives exact translation
equivariance of the constructed global flow, by ODE uniqueness. -/

noncomputable section

namespace EulerBoundedLipschitzFlow.Data

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (V : EulerBoundedLipschitzFlow.Data E)

/--
@isnad1 id=eq.1h6v.s7.c7b1dc1d5b6c from=translated src=- shape=22003512 vocab=c1031b8e
-/
theorem flow_add_eq (c : E) (hc : ∀ t x, V.velocity t (x+c)=V.velocity t x)
    (s t : ℝ) (x : E) : V.flow s t (x+c)=V.flow s t x+c := by
  have h := V.flow_unique s (x+c) (fun r => V.flow s r x+c)
    (fun r => by simpa only [hc] using (V.flow_hasDerivAt s r x).add_const c)
    (by rw [V.flow_initial])
  exact (congrFun h t).symm

end EulerBoundedLipschitzFlow.Data
