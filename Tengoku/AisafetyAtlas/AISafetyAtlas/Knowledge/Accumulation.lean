module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Ambiguity
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Temporal
public import Tengoku.Seed.Data.Finset.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Accumulation: what a fixed observation loses about a whole window

`Knowledge.Ambiguity` counts what one observation leaves open about **one**
target. Asking about a *window* of times means asking about the tuple of targets
across it, and the question becomes how ambiguity behaves as the window grows.

## The two bounds

Pairing two targets can only make things worse, and at worst multiplies:

```
ambiguity r f i  ≤  ambiguity r ⟨f, g⟩ i  ≤  ambiguity r f i * ambiguity r g i
```

The left bound is the accumulation statement — **widening the window never
reduces ambiguity** — and it is what licenses reading a per-step shortfall as
something that persists rather than washing out. The right bound is its ceiling:
ambiguity about a window is never worse than the product of the per-step
ambiguities, so nothing blows up faster than independently.

The bounds themselves are not time-indexed: a "window" is any finite tuple of
targets, and `f := target s₁`, `g := target s₂` from `Knowledge.Temporal` is one
instantiation among others.

## The other direction: evidence time

Widening the window is one axis. The other is *when the observation is read*.
Under `Knowledge.Temporal.EvidenceMonotone` — later evidence determines earlier —
ambiguity moves the opposite way:

```
ambiguity (observe t') f (observe t' ω)  ≤  ambiguity (observe t) f (observe t ω)      for t ≤ t'
```

So the two axes pull against each other, and
`ambiguity_le_pairTarget_of_evidenceMonotone` states both at once: one step read
late is never more ambiguous than the whole window read early. That inequality is
the module's reason to depend on `Knowledge.Temporal` rather than merely mention
it.

Note what this does **not** give. It bounds ambiguity about a *fixed* target as
evidence accumulates. It says nothing about a target that moves with time, which
is the case an impossibility result cares about and which needs dynamics.

## What is *not* proved here

That ambiguity **grows** — strictly, or exponentially — is not a theorem of this
module and could not be. Growth depends on whether each new step introduces a
distinction the observation cannot see, which is a statement about dynamics, and
there is no transition system anywhere in this layer. What is proved is that
growth is *possible and bounded*: the shortfall never shrinks, and never exceeds
the product.

`AISafetyAtlas.Examples.Knowledge.Accumulation` exhibits a model where the bound
on the left is strict and ambiguity doubles per step, reaching `2 ^ k`. That is an
example, not a general law, and the module says so at the point of statement.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `pairTarget` | The joint target: two questions asked at once |
| **Bound** | `ambiguity_le_pairTarget_left` | Widening the window never reduces ambiguity |
| **Bound** | `ambiguity_le_pairTarget_right` | The same on the other component |
| **Bound** | `ambiguity_pairTarget_le_mul` | A window is never worse than the product of its steps |
| **Boundary** | `not_knowable_pairTarget_of_not_knowable` | An unknowable step makes the whole window unknowable |
| **Bound** | `ambiguity_le_of_evidenceMonotone` | Later evidence never increases ambiguity |
| **Bound** | `ambiguity_le_pairTarget_of_evidenceMonotone` | One step read late ≤ the whole window read early |

## Explicit non-claims

Finite counting only — no probability, no entropy, no rate. In particular this is
not an information-accumulation *rate* result: rates need a distribution, and
this layer commits to none. No AI-system reading follows without a separate
reviewed bridge.

No survey coverage row is claimed here; this is workbench infrastructure.
-/

namespace AISafetyAtlas.Knowledge

universe u v w w'

variable {Ω : Type u} {I : Type v} {Y : Type w} {Z : Type w'}

/-- Two targets asked at once: the joint question a window poses.-/
@[expose] public def pairTarget (f : Ω → Y) (g : Ω → Z) : Ω → Y × Z :=
  fun ω => (f ω, g ω)

/-! ## Widening never helps -/

/-! ## And never blows up faster than independently -/

/-! ## The other axis: reading later

Widening a window costs ambiguity; waiting for evidence recovers it. Both
statements are about the same quantity, so they belong together. -/

/-! ## Consequence for knowability -/

end AISafetyAtlas.Knowledge
