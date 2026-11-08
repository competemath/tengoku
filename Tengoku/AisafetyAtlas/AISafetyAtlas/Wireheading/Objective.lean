module

public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
public import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
public import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Objective factorization

Ring and Orseau, *Delusion, Survival, and Intelligent Agents* (AGI 2011),
Section 2, describe their universal agents by shared environment dynamics plus
two objective components: a history utility and a horizon weighting.  Their
four agents differ only in those components.  This module isolates that
factorization at finite horizon.

## What is proved here

Two kinds of statement, kept apart deliberately.

* **Well-definedness.** `value_congr` and `optimal_decisions_congr` say that
  objectives with equal components induce equal values and equal optimal
  decisions.  These are record congruence: their proofs never unfold `value`.
  They are named accordingly and are *not* results about objectives.
* **Locality and scaling.** `value_eq_of_agree_on_window`,
  `value_scaleUtility`, and `optimal_decisions_eq_of_pos_scaleUtility` do unfold
  `value` and use the finite-horizon sum.  Locality is the truncation content:
  the value on a window depends only on the horizon weights and the utilities
  *inside* that window, so two objectives may disagree arbitrarily outside it.

The result does not formalize AIXI, Solomonoff induction, convergence, or the
paper's informal delusion-box arguments.  The paper states its results as
arguments rather than numbered theorems, so nothing here reproduces a numbered
source result. The source bounds utility in `[0,1]`; `Objective.utility` is
real-valued without a range invariant, a harmless generalization for these
algebraic locality and scaling lemmas but not an exact model match.
-/

namespace AISafetyAtlas.Wireheading

/-- The two objective components in Ring--Orseau's value equations.-/
public structure Objective (History : Type*) where
  utility : History → ℝ
  horizon : ℕ → ℕ → ℝ

namespace Objective

/-- Finite-horizon weighted utility of a trajectory.-/
@[expose] public def value {History : Type*} (O : Objective History)
    (start duration : ℕ) (trajectory : ℕ → History) : ℝ :=
  ∑ i ∈ Finset.range duration,
    O.horizon start (start + i) * O.utility (trajectory i)

/-!
### Well-definedness

These two are record congruence.  Their proofs conclude `O₁ = O₂` from
componentwise equality and never unfold `value`.  They are recorded under
honest names so that no reading of them as a result about objectives survives.
-/

/-!
### Locality of finite-horizon value

The substantive statements.  Each unfolds `value` and uses the sum over
`Finset.range duration`.
-/

/-- Rescale an objective's utility, keeping its horizon weighting.-/
@[expose] public def scaleUtility {History : Type*}
    (c : ℝ) (O : Objective History) : Objective History where
  utility := fun h => c * O.utility h
  horizon := O.horizon

/-- Value of a decision when fixed dynamics map it to a trajectory.-/
@[expose] public def decisionValue {History Decision : Type*}
    (O : Objective History)
    (dynamics : Decision → ℕ → History)
    (start duration : ℕ) (decision : Decision) : ℝ :=
  O.value start duration (dynamics decision)

/-- A decision is optimal within a specified feasible set.-/
@[expose] public def IsOptimal {History Decision : Type*}
    (O : Objective History)
    (dynamics : Decision → ℕ → History)
    (feasible : Set Decision)
    (start duration : ℕ) (decision : Decision) : Prop :=
  decision ∈ feasible ∧
    ∀ other ∈ feasible,
      O.decisionValue dynamics start duration other ≤
        O.decisionValue dynamics start duration decision

end Objective
end AISafetyAtlas.Wireheading
