import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportIndexed
import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportComparison
import Tengoku.Seed.MeasureTheory.Function.SimpleFuncDense
import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite diagrams from simple interior quantizers

A simple function assigns finitely many interior targets to a finite measure.
Its fiber masses give a native coalesced weighted diagram whose atomic measure
is exactly the pushforward of the original measure.
-/

set_option autoImplicit false
noncomputable section

namespace TDA.Persistence.BoundaryTransport

open Set MeasureTheory Filter Topology
open scoped Classical ENNReal NNReal
local infixr:25 " →ₛ " => SimpleFunc

/-- The native diagram of a finite-measure simple interior quantizer.-/
def simpleFuncDiagram (μ : Measure Interior) [IsFiniteMeasure μ]
    (T : Interior →ₛ Interior) : FiniteWeightedDiagram :=
  FiniteWeightedDiagram.ofIndexed
    (fun q : T.range => (μ (T ⁻¹' {q.1})).toNNReal) (fun q => q.1)

@[simp] theorem simpleFuncDiagram_zero (T : Interior →ₛ Interior) :
    simpleFuncDiagram 0 T = 0 := by
  simp [simpleFuncDiagram, FiniteWeightedDiagram.ofIndexed]

/-- A reservoir capacity for an equal-mass quantizer, exceeding the sum of its masses.-/
def quantizerCapacity (μ : Measure Interior) : ℝ≥0∞ :=
  μ Set.univ + μ Set.univ + 1

/-- The graph of a quantizer, padded by a zero-cost boundary–boundary atom.-/
def simpleFuncReservoirPlan (μ : Measure Interior) (T : Interior →ₛ Interior) :
    Measure (Space × Space) :=
  μ.map (fun x => (Space.point x, Space.point (T x))) +
    (quantizerCapacity μ - μ Set.univ) •
      Measure.dirac (Space.boundary, Space.boundary)

end TDA.Persistence.BoundaryTransport
