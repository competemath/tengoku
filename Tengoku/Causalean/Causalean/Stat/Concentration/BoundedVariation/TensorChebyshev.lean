module
public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorChebyshev
public import Tengoku.Causalean.Causalean.Stat.Concentration.BoundedVariation.WeightedIntegral

/-!
# Tensor Chebyshev expansion of bounded-variation polynomial paths

A continuous polynomial path in four variables whose cube evaluations have bounded variation
and path size at most `B` has a tensor Chebyshev expansion whose coefficient paths are
continuous, of bounded variation, and of size at most `16 B`. The polynomial algebra of the
tensor Chebyshev basis lives in `Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorChebyshev`.
-/

@[expose] public section

noncomputable section

open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open Causalean.Stat.Concentration.BoundedVariation
open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Concentration.BoundedVariation

end Causalean.Stat.Concentration.BoundedVariation
