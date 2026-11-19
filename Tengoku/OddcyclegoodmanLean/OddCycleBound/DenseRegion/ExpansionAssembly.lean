import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Expansion
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.GraphonReduction
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.GraphonKrylovBridge
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Excursion.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

namespace OddCycleBound.DenseRegion

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → ℝ}
variable {ι : Type*} [Fintype ι]

end OddCycleBound.DenseRegion
