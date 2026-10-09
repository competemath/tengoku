module
public import Tengoku.Causalean.Causalean.Graph.Density.FiniteDAG.LocalMarkov.Local
public import Tengoku.Causalean.Causalean.Graph.Density.FiniteDAG.Cube

/-!
# Ordered local Markov property for finite DAG density factorizations

This module derives the arbitrary-conditioning-superset form of the local Markov property and
specializes it to predecessor sets from arbitrary and canonical topological rankings.  It also
exports the unit-cube version using the existing unit-cube reference measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

open Causalean.Mathlib.Probability.Independence.Conditional

namespace Causalean.Graph.FiniteDensity

open Causalean.Mathlib.MeasureTheory.FiniteCoordinate

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [mX : ∀ i, MeasurableSpace (X i)]
  [∀ i, StandardBorelSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.Graph.DAG V}

end Causalean.Graph.FiniteDensity
