import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.Chart
import Tengoku.Seed.Algebra.Ring.GeomSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem chartSigma_eq_one_add (P : AdmissibleParams) : P.chartSigma = 1 + P.chartV := by
  unfold chartV chartSigma; ring

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
