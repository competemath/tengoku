module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.Splitting

/-!
# Marginal laws for partition cells

This file derives each cell's Poisson count law and its exact conditional
marked sample law from the joint finite-partition splitting theorem.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

namespace FiniteMeasurablePartition

end FiniteMeasurablePartition

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
