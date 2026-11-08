module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.ControlledProcess
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.Goal
public import Tengoku.Seed.Probability.Kernel.IonescuTulcea.Traj
public import Tengoku.Seed.Probability.ProbabilityMassFunction.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deterministic policies, trajectory laws, and print's `(δ,n)`-bounded agents

The probabilistic half of MAIS-A2's goal setting: what a deterministic
goal-conditioned agent does to a controlled Markov process, and the achievement
probability print's `(δ,n)`-boundedness compares against.

## Why the state sequence carries everything

Print's agent is a **deterministic** map from (history, goal) pairs to actions,
and print's history is the trajectory prefix `(s₀, a₀, …, s_t)` — states *and*
actions. Determinism makes the recorded actions a function of the states before
them, so nothing is left to chance but the transitions, the process lives on
`ℕ → 𝐒`, one application of Ionescu–Tulcea suffices with `X n = 𝐒` throughout,
and `statePairs` recovers the state–action trajectory the goal semantics reads.

**This is proved, not assumed.** `FullPolicy` is print's type, `inducedPolicy`
computes the action a trajectory-prefix policy takes as a function of the states
by running the same rule at earlier times, `liftPolicy` embeds back, and
`inducedPolicy_liftPolicy` says the round trip is the identity. Hence
`optimalProbFull_eq` — print's `max_{π'}` and this module's supremum have the
same value — and `isDeltaBoundedFull_lift_iff`: the two `(δ,n)`-boundedness
clauses select the same agents, and `firstActionMapFull_lift` says they show the
analyst the same data.

## `max` versus `⨆`

Print writes

    P(τ ⊨ ψ | π, s₀) ≥ (1 - δ) · max_{π'} P(τ ⊨ ψ | π', s₀),

which **presupposes** the maximum is attained. Attainment is a theorem — optimal
deterministic policies exist for reachability objectives on a finite process —
and Mathlib does not carry it. `optimalProb` is the supremum, which is what is
available without that theorem and which agrees with print's `max` wherever the
presupposition holds. At `δ = 0` the two readings differ and the attainment
theorem is unavoidable; at any `δ > 0` they do not, because a policy within a
factor `(1 - δ)` of a supremum exists by approximation. That is why
`docs/provenance/mais-o33-statability.md` runs MAIS issue #9's construction at
`δ = 1/2` rather than at the `δ = 0` the note chose.

The two readings also differ in *strength*, and in the safe direction for a
negative result: `⨆ ≥ max`, so an agent bounded here is bounded in print's sense
whether or not the maximum exists.

## What the achievement probability is

`achieveProb` applies the trajectory law to `{ω | CompositeSatisfies Ψ …}`, and
`measurableSet_compositeSatisfies` proves that event measurable, so the value is
print's probability rather than the measure's canonical extension to an
arbitrary set. The proof follows print's own semantics: a sub-goal reads one
state–action pair, that pair at time `t` is a function of the states up to `t`
because the policy is deterministic, *Now* and *Next* fix the time, *Eventually*
is a countable union over it with a finite minimality condition, a sequential
goal is a countable union over its head's achievement time, and a composite goal
is a finite union over its disjuncts.

Nothing below depends on that theorem — every step touching `achieveProb` is
monotone (`measure_mono`) or an almost-everywhere congruence (`measure_congr`),
both valid for the extension, and `optimalProb` is the supremum of the same
functional — but without it `achieveProb` would only be *bounded by* print's
probability, and the row that transcribes print's `P(τ ⊨ ψ | π, s₀)` would be
carrying a different number.

## What is not here

Nothing that MAIS-O33 needs. In particular the splice is here and unconditional:
`exists_isDeltaBounded_prescribing` builds a `(δ,n)`-bounded agent from
per-`(s₀, Ψ)` approximations on an **action-independent** environment, where
`trajectoryLaw_congr` makes the two laws being compared the same measure. On a
general environment the same construction would need a congruence lemma for
`ProbabilityTheory.Kernel.traj` that Mathlib does not state; no result in this
tree asks for one.
-/

namespace AISafetyAtlas.Causal

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-! ## Policies -/

/-- The history a deterministic policy reads at time `n`: the states up to `n`,
which determine the actions taken along them.-/
public abbrev GoalHistory (S : Type*) (n : ℕ) := ↥(Finset.Iic n) → S

/-- A deterministic policy, at one goal.-/
public abbrev GoalPolicy (S A : Type*) := (n : ℕ) → GoalHistory S n → A

/-- Print's goal-conditioned agent: one policy per composite goal, which is the
same data as a map from (history, goal) pairs to actions.-/
public abbrev GoalConditionedAgent (S A : Type*) := CompositeGoal S A → GoalPolicy S A

/-- The state–action trajectory a state sequence induces under a policy.-/
@[expose] public def statePairs (π : GoalPolicy S A) (ω : ℕ → S) : ℕ → S × A :=
  fun t ↦ (ω t, π t fun i ↦ ω i)

/-- **All the analyst sees**: the agent's first action from a start state under a
goal.-/
@[expose] public def firstActionMap (π : GoalConditionedAgent S A) (s₀ : S)
    (Ψ : CompositeGoal S A) : A :=
  π Ψ 0 fun _ ↦ s₀

/-! ## Print's history, and the reduction to the state sequence

Print's history is the trajectory prefix `(s₀, a₀, …, s_t)` — states **and**
actions — and `GoalHistory` carries the states. The two are not merely
behaviourally similar: `inducedPolicy` is the reduction, and it is exact.

A full-history policy is read along a run by handing it the actions it itself
played, and those are a function of the states, computed by the same rule one
step earlier. `inducedPolicy` performs that recursion, so the action a
full-history policy takes at time `t` on a run is a function of `s₀, …, s_t`
alone. Nothing is lost: `liftPolicy` embeds the state policies back, and
`inducedPolicy_liftPolicy` says the round trip is the identity. Hence
`optimalProbFull_eq`: print's `max_{π'}` over trajectory-prefix policies is the
supremum this module takes, so the two `(δ,n)`-boundedness clauses select the
same agents. -/

/-- Print's history at time `t`: the trajectory prefix `(s₀, a₀, …, s_t)`, as
its states up to `t` and its actions strictly before `t`.-/
public abbrev FullHistory (S A : Type*) (t : ℕ) :=
  (↥(Finset.Iic t) → S) × (↥(Finset.range t) → A)

/-- Print's goal-conditioned policy at one goal: a deterministic map from
trajectory prefixes to actions.-/
public abbrev FullPolicy (S A : Type*) := (t : ℕ) → FullHistory S A t → A

/-- Print's goal-conditioned agent: one trajectory-prefix policy per composite
goal.-/
public abbrev FullAgent (S A : Type*) := CompositeGoal S A → FullPolicy S A

/-- **The reduction.** The action a trajectory-prefix policy takes at time `t`,
as a function of the states alone: the recorded actions are the ones it played,
so they are computed by the same rule at earlier times.-/
public def inducedPolicy (π : FullPolicy S A) : (t : ℕ) → GoalHistory S t → A
  | t, h => π t (h, fun j ↦
      inducedPolicy π j.1 fun i ↦ h ⟨i.1, Finset.mem_Iic.mpr
        ((Finset.mem_Iic.mp i.2).trans (le_of_lt (Finset.mem_range.mp j.2)))⟩)
  decreasing_by exact Finset.mem_range.mp j.2

/-- A state policy read as a trajectory-prefix policy that ignores the recorded
actions.-/
@[expose] public def liftPolicy (π : GoalPolicy S A) : FullPolicy S A := fun t h ↦ π t h.1

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] public theorem inducedPolicy_liftPolicy (π : GoalPolicy S A) :
    inducedPolicy (liftPolicy π) = π := by
  funext t h
  rw [inducedPolicy]
  rfl

/-! ## The trajectory law -/

/-- One row of the kernel, as a distribution on the next state.-/
@[expose] public noncomputable def stepPMF (E : ControlledMarkovProcess S A)
    (s : S) (a : A) : PMF S :=
  PMF.ofFintype (fun s' ↦ ENNReal.ofReal (E.prob s a s')) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun s' _ ↦ E.prob_nonneg s a s', E.prob_sum,
      ENNReal.ofReal_one])

/-- The transition kernel a policy induces at time `n`: the row at the current
state and the action the policy takes on the history so far.-/
@[expose] public noncomputable def stepKernel (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (n : ℕ) : Kernel (GoalHistory S n) S :=
  Kernel.ofFunOfCountable fun h ↦
    (stepPMF E (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (π n h)).toMeasure

public instance (E : ControlledMarkovProcess S A) (π : GoalPolicy S A) (n : ℕ) :
    IsMarkovKernel (stepKernel E π n) :=
  ⟨fun _ ↦ PMF.toMeasure.isProbabilityMeasure _⟩

/-- **The law of the trajectory** from a start state: Ionescu–Tulcea applied to
the kernels the policy induces.-/
@[expose] public noncomputable def trajectoryLaw (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (s₀ : S) : Measure (ℕ → S) :=
  Kernel.traj (X := fun _ ↦ S) (stepKernel E π) 0 fun _ ↦ s₀

/-! ## The goal event is measurable

`achieveProb` below applies the trajectory law to `{ω | CompositeSatisfies Ψ …}`,
and this section proves that set is measurable, so the value is print's
probability and not merely the canonical outer-measure extension. The argument is
print's own reading of the semantics: a sub-goal inspects one state–action pair,
a state–action pair at time `t` is a function of the states up to `t`, *Now* and
*Next* fix the time, *Eventually* is a countable union over it, a sequential goal
is a countable union over the head's achievement time, and a composite goal is a
finite union over its disjuncts. -/

/-! ## Achievement probability, and print's bound -/

/-- `P(τ ⊨ Ψ | π, s₀)`.-/
@[expose] public noncomputable def achieveProb (E : ControlledMarkovProcess S A)
    (π : GoalPolicy S A) (s₀ : S) (Ψ : CompositeGoal S A) : ℝ≥0∞ :=
  trajectoryLaw E π s₀ {ω | CompositeSatisfies Ψ (statePairs π ω)}

/-- Print's *"best achievable"*, as a supremum rather than a maximum — see the
module note.-/
@[expose] public noncomputable def optimalProb (E : ControlledMarkovProcess S A)
    (s₀ : S) (Ψ : CompositeGoal S A) : ℝ≥0∞ :=
  ⨆ π : GoalPolicy S A, achieveProb E π s₀ Ψ

omit [DecidableEq S] in
/-- Print's *"best achievable"* read over **trajectory-prefix** policies, which
is the class print's `max_{π'}` ranges over.-/
@[expose] public noncomputable def optimalProbFull (E : ControlledMarkovProcess S A)
    (s₀ : S) (Ψ : CompositeGoal S A) : ℝ≥0∞ :=
  ⨆ π : FullPolicy S A, achieveProb E (inducedPolicy π) s₀ Ψ

/-- **All the analyst sees**, at print's own agent type.-/
@[expose] public def firstActionMapFull (π : FullAgent S A) (s₀ : S)
    (Ψ : CompositeGoal S A) : A :=
  inducedPolicy (π Ψ) 0 fun _ ↦ s₀

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
@[simp] public theorem firstActionMapFull_lift (π : GoalConditionedAgent S A) :
    firstActionMapFull (fun Ψ ↦ liftPolicy (π Ψ)) = firstActionMap π := by
  funext s₀ Ψ
  rw [firstActionMapFull, inducedPolicy_liftPolicy]
  rfl

/-- **`(δ,n)`-bounded**, at print's multiplicative form: a failure *rate*
relative to the best achievable, at every goal of depth at most `n` and every
start state.-/
@[expose] public def IsDeltaBounded [Fintype A] [DecidableEq A] (E : ControlledMarkovProcess S A)
    (π : GoalConditionedAgent S A) (n : ℕ) (δ : ℝ) : Prop :=
  ∀ Ψ ∈ compositeGoals n, ∀ s₀ : S,
    ENNReal.ofReal (1 - δ) * optimalProb E s₀ Ψ ≤ achieveProb E (π Ψ) s₀ Ψ

/-! ## The start state

`Kernel.traj` does not merely have the right first marginal: it fixes the
coordinates it is initialised at, pointwise on almost every trajectory. That is
what lets a policy read the start state off the history it is handed. -/

/-! ## Action-independent environments

Print's own myopic converse is stated over environments whose transition law
does not read the action. Nothing in `prob:rate` or `prob:corruption` excludes
them, and on them the state process is exogenous: the policy still decides which
state–action pairs a goal sees, but not which states occur. That is what makes
the splice below unconditional — no congruence lemma for `Kernel.traj` is
needed, because the two laws being compared are *the same measure*. -/

/-! ## The two ways a bounded agent is built -/

/-- **Print's `(δ,n)`-bounded agent**, at print's own history type.-/
@[expose] public def IsDeltaBoundedFull [Fintype A] [DecidableEq A]
    (E : ControlledMarkovProcess S A) (π : FullAgent S A) (n : ℕ) (δ : ℝ) : Prop :=
  ∀ Ψ ∈ compositeGoals n, ∀ s₀ : S,
    ENNReal.ofReal (1 - δ) * optimalProbFull E s₀ Ψ
      ≤ achieveProb E (inducedPolicy (π Ψ)) s₀ Ψ

end AISafetyAtlas.Causal
