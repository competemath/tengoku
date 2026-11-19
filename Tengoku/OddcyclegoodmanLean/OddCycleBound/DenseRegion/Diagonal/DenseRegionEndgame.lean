import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.GammaMomentProof
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.GammaSmoothing
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound.DenseRegion

/--
@isnad1 id=diagkern.0h0v.s0.7b96ba202ff4 from=translated src=- shape=45709ebd vocab=7b96ba20
-/
theorem diagKernelPosEll_unconditional : DiagKernelPosEll :=
  diagKernel_nonneg_pos_ell gamma_moment_inequality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

end OddCycleBound.DenseRegion
