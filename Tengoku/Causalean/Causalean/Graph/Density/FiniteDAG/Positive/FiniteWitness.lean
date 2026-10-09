module
public import Tengoku.Causalean.Causalean.Graph.Density.FiniteDAG.Positive.Finite

/-!
# Stable finite-state DAG edge witnesses

This module packages nonzero finite-state local contrasts and proves that their nonvanishing,
and therefore edgewise conditional dependence, persists throughout one uniform factor
neighborhood.
-/

@[expose] public section

open scoped ENNReal BigOperators

noncomputable section

namespace Causalean.Graph.FiniteDensity

open Causalean Causalean.Graph Causalean.Graph.FiniteDensity MeasureTheory

universe uV uX

variable {V : Type uV} [Fintype V] [DecidableEq V]
variable {X : V → Type uX} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  [∀ i, Nonempty (X i)]
variable {G : DAG V}

namespace PositiveFiniteDAGMechanism

variable (M : PositiveFiniteDAGMechanism G X)

/-- A local edge witness records four coordinate values at which the child's cross-product
contrast is nonzero. -/
abbrev EdgeWitness (i j : V) := PositiveFactor.EdgeWitness M.factorAccessor i j

/-- Two finite DAG mechanisms are uniformly factor-close when every local factor differs by less
than the prescribed radius at every full assignment. -/
def FactorSupClose (N : PositiveFiniteDAGMechanism G X) (ε : ℝ) : Prop :=
  PositiveFactor.FactorSupClose M.factorAccessor N.factorAccessor ε

/-- A fixed nonzero local contrast remains nonzero for every sufficiently small uniform
perturbation of all local factors. -/
theorem EdgeWitness.eventually_nonzero {i j : V} (w : M.EdgeWitness i j) :
    ∃ ε > 0, ∀ N : PositiveFiniteDAGMechanism G X,
      M.FactorSupClose N ε →
      N.localContrast i j w.base w.child₀ w.child₁ w.parent₀ w.parent₁ ≠ 0 := by
  rcases PositiveFactor.EdgeWitness.eventually_nonzero M.factorAccessor w with
    ⟨ε, hε, hopen⟩
  refine ⟨ε, hε, ?_⟩
  intro N hclose
  exact hopen N.factorAccessor hclose

end PositiveFiniteDAGMechanism

end Causalean.Graph.FiniteDensity
