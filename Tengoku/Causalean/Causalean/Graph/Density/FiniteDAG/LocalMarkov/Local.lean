module
public import Tengoku.Causalean.Causalean.Graph.Density.FiniteDAG.LocalMarkov.Coordinates
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockDensity
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Independence.Conditional
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Kernel.CondDistrib

/-!
# Density-factorization local Markov core

This module isolates the analytic core: under a finite DAG density factorization, a coordinate is
conditionally independent of any parent-closed block omitting it after its parents are removed,
given its parents.  The proof is intended to combine reverse-topological marginalization with a
three-block density factorization and Mathlib's conditional-independence characterization.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

open Causalean.Mathlib.Probability.Independence.Conditional

open Causalean.Mathlib.Probability.Kernel

namespace Causalean.Graph.FiniteDensity

open Causalean.Mathlib.MeasureTheory.FiniteCoordinate

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]
  [∀ i, StandardBorelSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
variable {G : Causalean.Graph.DAG V}

end Causalean.Graph.FiniteDensity
