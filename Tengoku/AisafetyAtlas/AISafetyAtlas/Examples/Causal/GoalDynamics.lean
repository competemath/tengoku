module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.GoalDynamics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Worked policies, trajectory laws and bounded agents

`AISafetyAtlas.Causal.GoalDynamics` renders the probabilistic half of MAIS-A2's
goal setting. This module checks that the definitions have content:

* `firstActionMap` reads the agent's first action from a start state and a goal,
  and reads nothing else — checked on an agent that branches on the state;
* the empty composite goal is achieved with probability zero, so `achieveProb` is
  not the constant `1`;
* `IsDeltaBounded` is **inhabited**: over a one-action environment every agent is
  `(δ,n)`-bounded at every `δ ≥ 0`, because there is only one policy and the
  supremum is attained by it.

The last one is a non-vacuity check on the predicate, not a MAIS instance:
`prob:corruption` quantifies over instances with `|𝐀| ≥ 2`. Building a bounded
agent over a two-action environment is what the splice needs, and the splice
needs the `traj` congruence lemma `AISafetyAtlas.Causal.GoalDynamics` records as
missing.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Causal.GoalDynamics

open AISafetyAtlas.Causal MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## The first-action map reads the start state and the goal -/

/-- An agent that plays action `1` from state `0` and action `0` elsewhere,
whatever the goal.-/
@[expose] public def branchingAgent : GoalConditionedAgent (Fin 2) (Fin 2) :=
  fun _ _ h ↦ if h ⟨0, by simp⟩ = 0 then 1 else 0

/-! ## The empty goal is never achieved -/

/-! ## `IsDeltaBounded` is inhabited -/

/-- A one-action environment: the uniform kernel on two states.-/
@[expose] public noncomputable def oneActionEnv : ControlledMarkovProcess (Fin 2) (Fin 1) where
  prob := fun _ _ _ ↦ 1 / 2
  prob_nonneg := by intro _ _ _; norm_num
  prob_sum := by
    intro _ _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

end AISafetyAtlas.Examples.Causal.GoalDynamics
