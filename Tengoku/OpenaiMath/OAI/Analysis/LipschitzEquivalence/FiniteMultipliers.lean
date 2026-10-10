import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.FiniteReduction

namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

def outerRadius (R : ℝ≥0) : ℝ≥0 := 2*R+2

def radialMultiplier (R : ℝ≥0) : Space M →L[ℝ] Space M :=
  multiplier (cutoff 0 (outerRadius R))

def finiteCutoff (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) (x : M) : ℝ :=
  setCutoff (A : Set M) (2*δ) x * cutoff 0 (outerRadius R) x

def finiteCutoffLip (R δ : ℝ≥0) : ℝ≥0 := 2/(outerRadius R)+2/(2*δ)

def finiteMultiplier (R : ℝ≥0) (A : Finset M) (δ : ℝ≥0) : Space M →L[ℝ] Space M :=
  multiplier (finiteCutoff R A δ)

def finiteMultiplierBound (R δ : ℝ≥0) : ℝ≥0 := 1+finiteCutoffLip R δ * outerRadius R

end LipschitzCounterexample.FreeSpace

end

end OAI
