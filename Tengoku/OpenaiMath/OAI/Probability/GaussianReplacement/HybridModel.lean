import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.Comparison

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

def blockInput {d m : ℕ} {U : Type*} (z : (Sphere d × U) × Rows m d) :
    U × (Rows m d × (Fin m → ℝ)) :=
  (z.1.2, z.2, label z.2 (z.1.1 : Vector d))

def freshInformation {d : ℕ} {U : Type*} [MeasurableSpace U] [StandardBorelSpace U]
    (P : Measure (Sphere d × U)) [IsFiniteMeasure P] (k : ℕ) : ℝ≥0∞ :=
  exposedInformation (P.prod (gaussianRows k d))

def hybridFirst (d : ℕ) : ℕ := (d+3)/4

def hybridLast (d : ℕ) : ℕ := d/2

def hybridCount (d : ℕ) : ℕ := hybridLast d - hybridFirst d + 1

def averagedFreshInformation {d : ℕ} {U : Type*}
    [MeasurableSpace U] [StandardBorelSpace U]
    (P : Measure (Sphere d × U)) [IsFiniteMeasure P] : ℝ :=
  (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d), (freshInformation P k).toReal) /
    hybridCount d

end CurrentProjection

end

end OAI
