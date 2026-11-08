module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.Decision
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Behavioural identifiability, in the shared knowability vocabulary

## Statement intent

- **Objects.** A causal model as the world, its masked gap response as the
  observation, and any model attribute as the hidden property.
- **Conclusion.** `behaviorEq_iff_behavior_eq` says the cluster's own
  `Skeleton.BehaviorEq` *is* an equality of observations, and
  `not_knowable_of_behaviorEq` reads a behaviourally equal pair with a differing
  attribute as a `Knowledge` collision.
- **Mechanism.** `BehaviorEq` is a pointwise equality of `Model.Δmask` over every
  admissible visible set, assignment and mixture. Bundling those arguments makes
  it a function equality, which is what the kernel quantifies over.

## Why this direction

Identifiability *is* factorization: an attribute is identifiable from behaviour
exactly when it is a function of the behaviour. The `Causal` cluster states this
in its own vocabulary — `BehaviorEq`, `InIdentifiedSet`, `modelError` — and
before this module nothing in `AISafetyAtlas.Causal` referred to
`AISafetyAtlas.Knowledge` and nothing outside referred back. The adapter lives
here, so the dependency runs downstream only and the kernel stays free of causal
vocabulary.

## What this adds, and what it does not

- **The generic form is new; the phenomenon is not.**
  `AISafetyAtlas.Examples.Causal` already builds behaviourally equal pairs with
  differing attributes by hand: `margin_class_not_identifiable`,
  `margin_class_not_identifiable_two_graphs`,
  `margin_class_not_identifiable_family`,
  `margin_class_not_identifiable_shared_optimal`, and the construction in
  `AISafetyAtlas.Examples.Causal.BehavioralCollision` that answers MAIS-O23 in
  the negative. What
  those do not supply is the passage *from* a negated knowability *to* such a
  pair. `exists_behaviorEq_pair_of_not_knowable` is that passage, and it is the
  kernel's `exists_witness_of_not_knowable` relabelled.
- **Not new MAIS coverage, and not an audit.** No row's status follows from this
  module. Restating identifiability through `Knowable` checks nothing about the
  printed argument, and grades nothing.
- **Not a statement about `InIdentifiedSet`.** That relation is about admissible
  *policy families* at a regret bound, a strictly weaker separator than
  behavioural equality: `inIdentifiedSet_zero_of_behaviorEq` goes one way and the
  cluster proves no converse. Nothing here claims the identified set is the
  collision set of `behavior`.
- **Not a claim that any attribute is unidentifiable.** Every result here is
  conditional on a supplied `BehaviorEq` pair or a supplied failure. Which
  attributes actually collide is the `Examples.Causal` constructions' business.

## Scope boundary

`behavior` bundles `BehaviorEq`'s bounded quantifier `∀ visible ⊆ sk.observed`
as a dependent function, so the equality is `funext`-equivalent to the original
pointwise statement — `behaviorEq_iff_behavior_eq` proves both directions rather
than asserting the packaging is faithful. The observation is the *masked gap*
family and nothing else: a consumer whose policies read more than `Δmask` is
outside every statement here.
-/

namespace AISafetyAtlas.Causal

universe u

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {C : Type*} [Fintype C] [DecidableEq C] {dim : C → ℕ}

/--
What an admissible policy family may observe of a model: its masked gap response,
over every admissible visible set, assignment and mixture.

This is the observation map. `Skeleton.BehaviorEq` is exactly equality of it.-/
@[expose] public noncomputable def behavior (sk : Skeleton C dim Bool 𝕜)
    (M : Model C dim 𝕜) :
    ∀ visible : Finset C, visible ⊆ sk.observed →
      Assignment C dim → ProbMixture C dim 𝕜 → 𝕜 :=
  fun visible _ w mix => M.Δmask sk.gap visible w mix

end AISafetyAtlas.Causal
