import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.VarianceLowerBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

noncomputable def leadingEigenvalueSafeRadius (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) : Real :=
  Real.sqrt
    (edgeDensity W mu * (1 - edgeDensity W mu) -
      complementEigenvalue hW i ^ 2)

end OddCycleBound.IntermediateRegion
