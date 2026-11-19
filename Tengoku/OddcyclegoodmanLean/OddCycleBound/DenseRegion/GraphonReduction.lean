import Tengoku.OddcyclegoodmanLean.OddCycleBound.Necklace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

noncomputable def neckSum (W : Ω → Ω → ℝ) (μ : Measure Ω) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m - 1),
    (-1 : ℝ) ^ j * pairing μ (pathIter (compl W) μ j) (complIter (compl W) μ (m - 1 - j))

end OddCycleBound.DenseRegion
