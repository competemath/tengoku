module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Preference
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.Seed.Tactic.Ring
public import Tengoku.Seed.Tactic.Linarith
public import Tengoku.Seed.Order.Bounds.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Overriding human reward functions (source Appendix B)

## Statement intent

- **Objects.** An abstract model of an agent acting alongside a human: a type of
  agent actions, the human policy each action results in, a value assignment for
  policies under rewards, and an optimal value.
- **Assumptions.** Values never exceed the optimum; there is a distinguished
  no-op action; and for each reward there is an action making the resulting human
  policy optimal for it. The source assumes the last of these when it says the
  agent can "make the human into a rational `Ṙ`-maximiser".
- **Quantifier order.** The reward is fixed first; actions are then compared
  against it.
- **Conclusion.** Both an unrelativised regret predicate (`Overrides`) and
  Definition 11 relative to a compatible `(p, R)` (`OverridesFor`); equation
  (2) for the rationalising action; and §B.2's claim that when the human is not
  already optimal, rationalising yields greater value than action `0`. These are
  scalar comparisons; no agent preference or choice rule is defined here.
- **Difference from the source.** §B.2 also argues, informally and with an
  explicit "very plausible", that the agent can often do better still by choosing
  a reward `Rᵃ` that is easy to maximise. That existential claim is not
  formalized. No transition dynamics, discounting, or MDP structure is developed;
  value and optimal value are abstract fields.

## Explicit non-claims

- **Not** an agent preference or choice rule. `rationalise_strictly_better` is a
  value inequality; nothing here says what an agent selects.
- **Not** a full MDP realization of Definition 11. `OverridesFor` restores the
  compatible decomposition, but outcomes and values remain abstract and “high
  regret” is represented by an explicit threshold. `Overrides` is retained only
  as the unrelativised shadow.
- **Not** a claim that any real system overrides human preferences.
- **Not** the source's speculative part of §B.2 about choosing an easily
  maximised `Rᵃ`.
- **Not** a treatment of "mental integrity" or "self-determination", which the
  source's own footnote flags as absent from the formalism.

Survey row: **BY-011**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference

/--
An abstract model of an agent whose actions reshape the human policy.

`resulting a` is the human policy after the agent takes action `a`; `noop` is the
action of leaving the human alone; `rationalise R` is an action making the human
an optimal `R`-maximiser.-/
public structure OverrideModel (S A Act : Type*) where
  /-- The human policy resulting from an agent action.-/
  resulting : Act → Policy S A
  /-- Value of a human policy under a reward.-/
  value : RewardFn S A → Policy S A → ℝ
  /-- The best value attainable under a reward.-/
  optValue : RewardFn S A → ℝ
  /-- No policy beats the optimum.-/
  le_optValue : ∀ R π, value R π ≤ optValue R
  /-- Leaving the human alone.-/
  noop : Act
  /-- An action making the human optimal for the given reward.-/
  rationalise : RewardFn S A → Act
  /-- That action does make the human optimal.-/
  rationalise_optimal : ∀ R, value R (resulting (rationalise R)) = optValue R

namespace OverrideModel

variable {S A Act : Type*} (M : OverrideModel S A Act)

/-- Regret of the human policy resulting from an agent action, under a reward.-/
@[expose] public def regret (R : RewardFn S A) (a : Act) : ℝ :=
  M.optValue R - M.value R (M.resulting a)

/--
**Definition 11.** The agent's action `a` *overrides* the reward `R` at
threshold `θ` when it leaves the human in a situation whose regret for `R` is at
least `θ`.

The source states this with an informal "high regret"; the threshold is made an
explicit parameter here rather than fixed, since the source notes there is no
natural zero.-/
@[expose] public def Overrides (R : RewardFn S A) (θ : ℝ) (a : Act) : Prop :=
  θ ≤ M.regret R a

/-!
### Appendix B in the source's own terms

`Overrides` above drops the source's relativisation to a compatible pair. The
declarations below restore it, and add the two displayed equations.
-/

/--
**Definition 11, relativised.**  The source's definition is given *relative to a
compatible pair* `(p, R)`: the agent's action `a` overrides the human reward
function when it leaves the human in a situation of high regret for `R`, where
`(p, R)` is a decomposition of the resulting human behaviour.

`Overrides` is the unrelativised shadow of this; `overrides_of_overridesFor`
records that this is the stronger notion.-/
@[expose] public def OverridesFor
    (p : Planner (RewardFn S A) (Policy S A)) (R : RewardFn S A)
    (θ : ℝ) (a : Act) : Prop :=
  Explains p R (M.resulting a) ∧ θ ≤ M.regret R a

/-- The relativised notion implies the unrelativised one.-/
public theorem overrides_of_overridesFor
    {p : Planner (RewardFn S A) (Policy S A)} {R : RewardFn S A}
    {θ : ℝ} {a : Act} (h : M.OverridesFor p R θ a) : M.Overrides R θ a := h.2

/--
**Equation (2).**  The value of the action that rationalises the human for
`Ragent`, when the agent gives probability `1 - ε` to `Rtrue` and probability
`ε` to `Ragent`.

Unlike an earlier atlas definition, this does not accept an arbitrary action:
the source's `ε V*_{Ragent}` term is justified specifically because this action
makes the resulting human policy `Ragent`-optimal.-/
@[expose] public def mixtureValue (ε : ℝ)
    (Rtrue Ragent : RewardFn S A) : ℝ :=
  ε * M.optValue Ragent +
    (1 - ε) * M.value Rtrue (M.resulting (M.rationalise Ragent))

/--
The value of action `0` / no-op under the true reward.  It is separate from
equation (2): no-op does not acquire an `ε * optValue` term unless it is itself
known to rationalise the human for the hypothesised reward.-/
@[expose] public def noopValue (Rtrue : RewardFn S A) : ℝ :=
  M.value Rtrue (M.resulting M.noop)

end OverrideModel

end AISafetyAtlas.Preference
