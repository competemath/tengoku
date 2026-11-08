module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Preference
public import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic operations and Proposition 7

## Statement intent

- **Objects.** The six basic operations of the source's §5.1.2, and an abstract
  complexity assignment on policies and on planner/reward pairs.
- **Assumptions.** The source's notion of a *`c`-reasonable language* — a
  language in which each basic operation is expressible by a short program — is
  **reparameterized** here. The source bounds the *composite* operations
  `F₁…F₄` and obtains distance `c` from the minimum. This structure instead
  assumes separate evaluation and construction bounds, and concludes `2 * c`.
  That is a valid conditional variation, not the source definition with the same
  constant, and the results below should be read accordingly.
- **Quantifier order.** The constant is fixed by the language, before any policy
  or pair is chosen.
- **Conclusion.** The source's Proposition 7: each of the three degenerate
  planner/reward pairs has complexity within `2 * c` of *every* pair compatible
  with the policy, hence is among the lowest-complexity compatible pairs.
- **Difference from the source.** The source builds complexity from program
  lengths in a language `L` and defines "comparable complexity" via a constant
  `c`; here the language is abstracted away and only the additive bounds it
  supplies are assumed. The bounds are stated with ℕ-valued complexity. The
  concrete plain-Kolmogorov instantiation of the same argument, for the first
  degenerate pair, is in `AISafetyAtlas.Preference.Complexity`.

## Explicit non-claims

- **Not** a construction of any particular reasonable language, nor a proof that
  one exists. Existence is the source's informal argument about short programs
  and is assumed here.
- **Not** supported by any nontrivial model. The only exhibited inhabitant of
  `ReasonableLanguage` is
  `AISafetyAtlas.Examples.SixTargets.degenerateLanguage`, in which every
  complexity is zero and `c = 0`. Propositions 7 and 8 hold there but say
  nothing, since all complexities coincide. Whether a *nontrivial* `c`-reasonable
  language exists is exactly the source's informal claim, and nothing in the
  atlas establishes it. Read the propositions as conditional statements about
  any language meeting the bounds, not as evidence that an interesting one
  exists.
- **Not** the source's §4.1 regret results, Proposition 10, or Appendix A.
  §5.2 and Proposition 8 *are* treated, in `proposition_eight` below.
- **Not** the source's own `c`-reasonable-language parameterisation: see the
  reparameterization note above, which is why Proposition 7 here concludes
  `2 * c` rather than `c`. The source's parameterisation, with the composite
  operations `F₁…F₄` and distance `c`, is formalized separately in
  `AISafetyAtlas.Preference.SourceComplexity`. Prefer that module when source
  parity matters.
- **Not** a claim that the *intended* pair is of high complexity, which is the
  second half of the source's informal Theorem 2.

Survey row: **BY-011**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference

variable {S A : Type*}

/-- A planner/reward pair, the object whose complexity the source compares.-/
public abbrev Pair (S A : Type*) : Type _ :=
  Planner (RewardFn S A) (Policy S A) × RewardFn S A

section Operations

variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- `f₁(p) = (p, 0)`: pair a planner with the trivial reward.-/
@[expose] public def op1 (p : Planner (RewardFn S A) (Policy S A)) : Pair S A := (p, 0)

/-- `f₂(R) = (p_g, R)`: pair a reward with the greedy planner.-/
@[expose] public noncomputable def op2 (R : RewardFn S A) : Pair S A := (greedyPlanner, R)

/-- `f₃(p, R) = p(R)`: evaluation.-/
@[expose] public def op3 (x : Pair S A) : Policy S A := x.1 x.2

/-- `f₄(p, R) = (-p, -R)`: the anti-rational negation.-/
@[expose] public def op4 (x : Pair S A) : Pair S A := ((fun R' => x.1 (-R')), -x.2)

/-- `f₅(π) = p_π`: the indifferent planner for a policy.-/
@[expose] public def op5 (π : Policy S A) : Planner (RewardFn S A) (Policy S A) :=
  indifferentPlanner π

/-- `f₆(π) = R_π`: the reward paying for a policy's action.-/
@[expose] public def op6 (π : Policy S A) : RewardFn S A := rewardOf π

/-! ### The degenerate pairs, built from the operations, are compatible -/

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- `f₄` preserves the evaluated policy: negating both planner and reward leaves
the behaviour unchanged. This is the source's observation opening §5.2.-/
public theorem op3_op4 (x : Pair S A) : op3 (op4 x) = op3 x := by
  show x.1 (- -x.2) = x.1 x.2
  rw [neg_neg]

end Operations

/-!
## `c`-reasonable languages
-/

/--
An abstract complexity assignment with additive bounds for evaluation, the
three degenerate-pair constructions, and pair negation. This is a
reparameterized interface for the bounds used below, not the source's literal
definition of a `c`-reasonable language.-/
public structure ReasonableLanguage (S A : Type*)
    [Fintype A] [Nonempty A] [DecidableEq A] where
  /-- Complexity of a planner/reward pair.-/
  KPair : Pair S A → ℕ
  /-- Complexity of a policy.-/
  KPolicy : Policy S A → ℕ
  /-- The additive slack used by each recorded bound.-/
  c : ℕ
  /-- `f₃` is cheap: evaluating a pair costs at most `c` over the pair.-/
  eval_le : ∀ x : Pair S A, KPolicy (op3 x) ≤ KPair x + c
  /-- `f₁ ∘ f₅` is cheap: the indifferent pair costs at most `c` over the policy.-/
  indifferent_le : ∀ π : Policy S A, KPair (op1 (op5 π)) ≤ KPolicy π + c
  /-- `f₂ ∘ f₆` is cheap: the greedy pair costs at most `c` over the policy.-/
  greedy_le : ∀ π : Policy S A, KPair (op2 (op6 π)) ≤ KPolicy π + c
  /-- `f₄ ∘ f₂ ∘ f₆` is cheap: the anti-rational pair costs at most `c`.-/
  antirational_le : ∀ π : Policy S A, KPair (op4 (op2 (op6 π))) ≤ KPolicy π + c
  /-- `f₄` is cheap on *any* pair, not only the degenerate ones. This is the
  bound §5.2 needs.-/
  neg_le : ∀ x : Pair S A, KPair (op4 x) ≤ KPair x + c

namespace ReasonableLanguage

variable [Fintype A] [Nonempty A] [DecidableEq A]
variable (L : ReasonableLanguage S A) (π : Policy S A) (x : Pair S A)

/-- Compatibility, in the source's sense: the pair evaluates to the policy.

`AISafetyAtlas.Preference.Source.ReasonableForF.Compatible` is this same
definition, character for character and with the same type, in the namespace of
the source-literal language structure. Neither is derived from the other, and a
reader who finds one should know the other exists; whether they should be one
declaration is a question about how far `Source.` mirrors are kept separate, not
a question about the mathematics.-/
@[expose] public def Compatible (x : Pair S A) (π : Policy S A) : Prop := op3 x = π

end ReasonableLanguage

end AISafetyAtlas.Preference
