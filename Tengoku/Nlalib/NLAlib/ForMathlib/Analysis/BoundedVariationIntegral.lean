import Tengoku.Seed.Topology.EMetricSpace.VariationOnFromTo
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Tengoku.Seed.Algebra.BigOperators.Module
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Analysis.SpecificLimits.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interval integration for bounded variation functions

Finite variation controls the error of left-endpoint quadrature and
oscillatory integrals. Helpers for `chebyshev-coeff-bv-decay`.
-/

noncomputable section

open Set Finset MeasureTheory
open scoped ENNReal

namespace NLAlib

end NLAlib
