import Tengoku.TdaLib.TDA.Persistence.BoundaryTransportQuantization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Same-mass finite atomic approximation

Approximation targets lie in the dense range of interior points. Every
quantizer therefore remains interior-valued, and its finite diagram retains
the original measure's total mass. The only integrability assumption is the
collapsed-boundary persistence moment.
-/

set_option autoImplicit false
noncomputable section

namespace TDA.Persistence.BoundaryTransport

open Set MeasureTheory Filter Topology
open scoped Classical ENNReal NNReal
local infixr:25 " →ₛ " => SimpleFunc

/-- A fixed interior point of depth one used by the dense-range approximation.-/
private def approximationBase : Interior := ⟨(0, 2), by norm_num⟩

private def unpointApprox : Space → Interior
  | .boundary => approximationBase
  | .point x => x

private def spaceApprox (n : ℕ) : Interior →ₛ Space :=
  SimpleFunc.approxOn Space.point continuous_point.measurable
    (Set.range Space.point) (Space.point approximationBase)
    ⟨approximationBase, rfl⟩ n

/-- A finite-range interior quantizer, with no boundary values.-/
def interiorQuantizer (n : ℕ) : Interior →ₛ Interior :=
  (spaceApprox n).map unpointApprox

/-- The actual native finite diagram at approximation level `n`.-/
def quantizedDiagram (μ : Measure Interior) [IsFiniteMeasure μ] (n : ℕ) :
    FiniteWeightedDiagram := simpleFuncDiagram μ (interiorQuantizer n)

/--
@isnad1 id=eq.0h1v.s6.f14dc05bc7b0 from=translated src=- shape=fe3f6d8b vocab=955b16f0
-/
@[simp] theorem quantizedDiagram_zero (n : ℕ) :
    quantizedDiagram 0 n = 0 := simpleFuncDiagram_zero _

private def quantizationError (p : ℝ) (n : ℕ) (x : Interior) : ℝ≥0∞ :=
  (edist (Space.point (interiorQuantizer n x)) (Space.point x)) ^ p

private def quantizationBound (p : ℝ) (x : Interior) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal (depth x ^ p))

end TDA.Persistence.BoundaryTransport
