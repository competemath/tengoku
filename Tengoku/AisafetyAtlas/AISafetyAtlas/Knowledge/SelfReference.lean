module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Ambiguity
public import Tengoku.Seed.Data.Fintype.EquivFin
public import Tengoku.Seed.Data.Fintype.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Self-reference: when the model is part of what it models

Every earlier layer treats the observation as an arbitrary map. Each says so in
its non-claims: *nothing here makes `observe` a projection of a state containing
the observer*. This module is where that stops being true.

## The one structural commitment

The observer's model is a **component of the global state**. Write the state as
`Model × Rest`: the observer's current model, together with everything else. The
observer reads `Prod.fst` — its own model, and nothing more. That is what
"embedded" means here, and it is the whole difference from
`Knowledge.Embedded`, where the restriction map is arbitrary data supplied by the
modeller.

Self-reference is then not an extra axiom. It is forced: the target `id` includes
the `Model` component, so a complete self-model must model *itself*.

## The result

`selfComplete_iff_subsingleton_rest`: an embedded observer completely knows the
state it is in **iff there is nothing else in the state**. Finitely,
`card_rest_le_one_of_selfComplete` turns that into a counting statement — a
complete self-model forces `|Rest| ≤ 1`.

Read as a design law: a system whose self-model is part of its own state buys
completeness only by having nothing to be complete about. That is not a
resource-bound argument and does not need one; it is forced by the
map-is-part-of-territory structure alone.

## What this is not

Not Breuer's theorem — that is `Knowledge.Embedded`, which models the apparatus
with an inference map and meshing, grades against the paper, and does not assume
a product decomposition.

Not a regress or hierarchy argument. Nothing here iterates "a model of the model
of the model". The obstruction is one level deep and finite.

Not resource-bounded. `Rest` may be any type; there is no budget, no cost, and no
count of processes.

Not dynamic. There is no transition system, so nothing here says the state
*changes* while being modelled. Composing this with `Knowledge.Temporal` is the
obvious next step and is deliberately not taken here.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `SelfState` | Global state as the observer's model together with the rest |
| **Model** | `selfRead` | What an embedded observer can read: its own model |
| **Model** | `SelfComplete` | The observer knows the whole state it is in |
| **Law** | `selfComplete_iff_subsingleton_rest` | Complete self-knowledge ⟺ nothing else exists |
| **Bound** | `card_rest_le_one_of_selfComplete` | Finitely: a complete self-model forces `|Rest| ≤ 1` |
| **Boundary** | `not_selfComplete_of_two_rest` | Two distinct remainders refute completeness |

## Explicit non-claims

`Model` and `Rest` are arbitrary types; nothing interprets them as memory,
computation, or belief. No AI-system reading — self-monitoring, introspection,
wireheading detection — follows without a separate reviewed bridge. In
particular, nothing here concerns consciousness: incompleteness of a self-model
is a statement about a projection, and every partially observed embedded system
has it, which is exactly why it cannot be evidence of anything phenomenal.

No survey coverage row is claimed here; this is workbench infrastructure.

Not `AISafetyAtlas.SelfAwareness`. That module carries the same registry group
and a different obstruction: a cost law over composites rather than a projection
of the state onto the model component. Neither imports the other.
-/

namespace AISafetyAtlas.Knowledge.SelfReference

universe u v

/-- The global state of a system that contains its own observer: the observer's
model, together with everything else.-/
public abbrev SelfState (Model : Type u) (Rest : Type v) : Type (max u v) :=
  Model × Rest

/-- What an embedded observer can read — its own model, and nothing else.

This is the self-referential step. `selfRead` is not supplied by a modeller; it
is the projection onto the component of the state that *is* the observer.-/
@[expose] public def selfRead {Model : Type u} {Rest : Type v} :
    SelfState Model Rest → Model :=
  Prod.fst

/-- The observer completely knows the state it is embedded in: the whole state
factors through its own model.-/
@[expose] public def SelfComplete (Model : Type u) (Rest : Type v) : Prop :=
  Knowable (selfRead : SelfState Model Rest → Model) id

/-! ## The characterization -/

/-! ## The counting form -/

end AISafetyAtlas.Knowledge.SelfReference
