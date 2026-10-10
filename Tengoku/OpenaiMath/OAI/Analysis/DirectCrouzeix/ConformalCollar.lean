import Tengoku.OpenaiMath.OAI.Analysis.DirectCrouzeix.Continuation

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

structure AnalyticBoundaryChart (U : Set ℂ) (p : ℂ) where
  chart : OpenPartialHomeomorph ℂ ℂ
  zero_mem : 0 ∈ chart.source
  at_zero : chart 0 = p
  analytic : AnalyticOnNhd ℂ chart chart.source
  inverse_analytic : AnalyticOnNhd ℂ chart.symm chart.target
  inverse_derivative : deriv chart.symm p ≠ 0
  side : ∀ z ∈ chart.source, chart z ∈ U ↔ 0 < z.im

def HasAnalyticBoundary (U : Set ℂ) : Prop :=
  ∀ p ∈ frontier U, Nonempty (AnalyticBoundaryChart U p)

end Conformal

end DirectCrouzeix

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end OAI
