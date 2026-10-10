import Tengoku.OpenaiMath.OAI.Analysis.DirectCrouzeix.DomainBound

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix

open Set Metric

theorem convex_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Convex ℝ (numericalRange A) :=
  Geometry.convex_quadratic_range (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).toLinearMap

end DirectCrouzeix

end

end

end

end

end

end

end

end

end

end OAI
