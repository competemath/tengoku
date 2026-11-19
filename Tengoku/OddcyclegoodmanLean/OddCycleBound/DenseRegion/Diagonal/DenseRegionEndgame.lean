import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.GammaMomentProof
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.GammaSmoothing
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Diagonal.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound.DenseRegion

theorem diagKernelPosEll_unconditional : DiagKernelPosEll :=
  diagKernel_nonneg_pos_ell gamma_moment_inequality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

end OddCycleBound.DenseRegion
