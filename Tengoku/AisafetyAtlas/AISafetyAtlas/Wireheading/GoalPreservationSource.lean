module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Wireheading.GoalPreservation
public import Tengoku.Seed.Data.Fintype.BigOperators
public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-percept Theorem 12 induction step, without surjectivity

`AISafetyAtlas.Wireheading.GoalPreservation` proves a deterministic
specialization of Everitt, Filan, Daswani and Hutter, AGI 2016, LNCS 9782,
Theorem 12 (extended version `arXiv:1605.03142`, Theorem 16), but
only under `names_surjective`: at every history, *every* world-action and
next-policy pair is emitted by some represented policy.  That premise is
stronger than the source's, which introduces a naming map `ι : P → Π` and says
explicitly that not every policy can have a name.

This module removes it from the one-step induction argument.

## What the source's proof actually uses

Reading the proof of Theorem 12, the comparison is never against an arbitrary
policy.  It is against `π₁`, the agent's own initial policy, which *is* named by
assumption, so the action `(ǎ_t, π₁)` is always available.  The proof then
argues:

* if the selected continuation `π_{t+1}` were worse than `π₁` at some percept,
  it would be no better at any percept and strictly worse at that one;
* percepts are drawn from a finite full-support probability mass function, so a
  pointwise inequality that is strict somewhere makes the *expectation*
  strictly worse;
* hence `(ǎ_t, π_{t+1})` would be strictly worse than the available alternative
  `(ǎ_t, π₁)`, contradicting the optimality of `π_t`.

So the two ingredients are **nameability of the initial policy** and **full
support**, not surjectivity of the naming map.  `Model` records exactly those:
`initial` is a name, `initial_dominates` says `π₁` is optimal in the form the
proof uses, and `prob_sum_one` / `prob_pos` make `prob` a full-support finite
probability mass function.

## Explicit non-claims

* **Finitely many percepts.** Expectations are normalized `Finset` sums over a
  `Fintype`, not integrals. No measure theory is used, so this is the
  finite-percept case of the source's `E_{e_t}`.
* **Not the full source theorem.** `initial_dominates` and `contValue`
  are given; the source derives the corresponding facts from
  modification-independent `ρ` and `u₁` together with the optimal-policy-existence
  result the technical report proves as its Theorem 20 in Appendix A — the
  published chapter prints no proofs, so that is the only place it appears — which
  is not reproduced.  What is reproduced is the induction step of Theorem 12, which
  is where `names_surjective` was previously needed.
* **On-policy only**, as in the source: nothing is claimed off the reached path.
* **Not utility modification**, only policy modification.

Landscape entry: `LAND-GOAL-001`.  No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.GoalPreservationSource

/--
A policy self-modification model with stochastic percepts.

`act p h` is `ι(p)` applied at `h`, giving a world action and the *name* of the
next policy.  There is no assumption that every pair arises this way.-/
public structure Model (History WorldAction PolicyName Percept : Type*)
    [Fintype Percept] where
  /-- The named policy's choice: a world action and the next policy's name.-/
  act : PolicyName → History → WorldAction × PolicyName
  /-- History extension by a world action and the percept received.-/
  extend : History → WorldAction → Percept → History
  /-- The initial utility `u₁`.-/
  utility : History → ℝ
  /-- Discount factor.-/
  discount : ℝ
  /-- It is positive.-/
  discount_pos : 0 < discount
  /-- Probability mass assigned to each next percept.-/
  prob : History → WorldAction → Percept → ℝ
  /-- The percept weights are normalized for every history and world action.-/
  prob_sum_one : ∀ h a, ∑ e : Percept, prob h a e = 1
  /-- **Full support**: every percept has positive weight.  This is what turns a
  pointwise strict inequality into a strict inequality of expectations.-/
  prob_pos : ∀ h a e, 0 < prob h a e
  /-- The realistic continuation value of a named policy, evaluated under the
  initial utility.-/
  contValue : PolicyName → History → ℝ
  /-- The initial policy's name.  Nameability of `π₁` is the assumption that
  replaces surjectivity of the naming map.-/
  initial : PolicyName
  /-- `π₁` is optimal, in the form the source's proof uses.-/
  initial_dominates : ∀ p h, contValue p h ≤ contValue initial h

namespace Model

variable {History WorldAction PolicyName Percept : Type*} [Fintype Percept]
variable (M : Model History WorldAction PolicyName Percept)

/-- The realistic `Q` value of a world-action and next-policy pair, as an
expectation over percepts.-/
@[expose] public noncomputable def qValue (h : History)
    (a : WorldAction × PolicyName) : ℝ :=
  ∑ e : Percept, M.prob h a.1 e *
    (M.utility (M.extend h a.1 e) +
      M.discount * M.contValue a.2 (M.extend h a.1 e))

/-- A named policy chooses a `Q`-maximizing action at a history.-/
@[expose] public def OptimalAt (p : PolicyName) (h : History) : Prop :=
  ∀ a, M.qValue h a ≤ M.qValue h (M.act p h)

end Model

end AISafetyAtlas.Wireheading.GoalPreservationSource
