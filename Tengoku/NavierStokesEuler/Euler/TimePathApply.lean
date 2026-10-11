import Tengoku.NavierStokesEuler.Euler.TimeLpMultiplier
import Tengoku.NavierStokesEuler.Euler.TimeLpLinearity

/-! Continuous time-path application and its exact Bochner compatibility. -/

noncomputable section

namespace EulerTimeLp

open Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual pointwise action of a continuous operator path on a continuous field path. -/
def timePathApply (T : ℝ) (A : C(Icc (0 : ℝ) T, E →L[ℝ] F))
    (u : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, F) :=
  ⟨fun t => A t (u t), A.continuous.clm_apply u.continuous⟩

end EulerTimeLp
