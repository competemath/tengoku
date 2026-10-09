module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection.ThreeBlockFactorization

/-!
# Conditional independence from a three-block product density

This module turns a density whose first two coordinate blocks factor through a
third, conditioning block into `CondIndepFun` for the first two coordinate maps
given the third coordinate. It is the reverse direction of the density-factorization
characterization `DensityIntersection.condIndepFun_threeBlock_iff_factors`, stated in plain
product coordinates.
-/

public section

open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Independence.Conditional
universe uY uZ uC

variable {Y : Type uY} {Z : Type uZ} {C : Type uC}
variable [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace C]
variable [StandardBorelSpace Y] [StandardBorelSpace Z] [StandardBorelSpace C]

end Causalean.Mathlib.Probability.Independence.Conditional
