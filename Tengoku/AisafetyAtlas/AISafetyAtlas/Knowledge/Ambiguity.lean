module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge
public import Tengoku.Seed.Data.Fintype.Card
public import Tengoku.Seed.Data.Finset.Lattice.Fold

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# How much is unknowable — finite fibre ambiguity

`Knowable` is a yes/no question. On finite systems it has a quantitative refinement:
count how many target values remain possible given one observation.

## The trap this module is written around

`Knowable r f ↔ ∀ i, ambiguity r f i ≤ 1` is **not** the content here. It is
`knowable_iff_no_collision` restated in counting form, and a module that stopped
there would be a cardinality wrapper around a theorem the kernel already proves.
It is included as `knowable_iff_ambiguity_le_one` because a bridge to the kernel
belongs in the record, and it is labelled a bridge rather than a result.

The content is the **bounds**:

* `card_image_le_of_knowable` — an observation with fewer outcomes than the
  property has values cannot decode it. A counting obstruction, independent of
  which particular states collide.
* `ambiguity_le_of_comp` — post-processing never lowers ambiguity anywhere. The
  quantitative form of `not_knowable_comp`, which only said the yes/no answer
  could not be repaired.

## Why `≤ 1` and not `= 1`

Ambiguity is `0` at an observation value nothing realizes. Those are exactly the
`i` outside the range of `r`, and requiring `= 1` would make every model with an
unreachable observation value unknowable. The empty fibre carries no ambiguity,
so `≤ 1` is the right exactness condition.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `fibre` | The states an observation value does not separate |
| **Model** | `ambiguity` | How many target values survive one observation |
| **Bridge** | `knowable_iff_ambiguity_le_one` | Exactness ⟺ every fibre carries at most one value |
| **Bound** | `not_knowable_of_one_lt_ambiguity` | One ambiguous fibre refutes knowability |
| **Bound** | `card_image_le_of_knowable` | Knowability needs at least as many observation outcomes as target values |
| **Bound** | `not_knowable_of_card_lt` | Its contrapositive: the counting obstruction |
| **Bound** | `ambiguity_le_of_comp` | Coarsening never decreases ambiguity |

## Constructivity

Every declaration here is classical — `[propext, Classical.choice, Quot.sound]`
— including the two bounds, which are otherwise elementary. That is inherited
from Mathlib's `Finset`/`Fintype` development, not from anything in the
statements. It is a real difference from the kernel, where
`not_knowable_of_collision`, `Knowable.mono` and `not_knowable_comp` depend on no
axioms at all, and it is recorded here so nobody infers constructivity from the
finiteness.

## Explicit non-claims

Finite counting only. There is no probability, no entropy, no rate, and no
measure here: `ambiguity` counts possibilities, it does not weigh them. A
conditional-entropy treatment would need Shannon entropy over general probability
spaces, which Mathlib does not carry at the pinned revision — it has topological
entropy, binary entropy and Kullback–Leibler divergence, and no conditional
Shannon entropy. That is a separate foundation, not an extension of this module.

No survey coverage row is claimed here; this is workbench infrastructure.
-/

namespace AISafetyAtlas.Knowledge

universe u v w

variable {Ω : Type u} {I : Type v} {Y : Type w}

/-! ## Counting what an observation leaves open -/

/-- The states that share one observation value: the fibre `r` cannot see into.-/
@[expose] public def fibre [Fintype Ω] [DecidableEq I]
    (r : Ω → I) (i : I) : Finset Ω :=
  Finset.univ.filter (fun ω => r ω = i)

/--
The **ambiguity** of an observation value: how many distinct target values are
still possible once the observation reads `i`.

`1` is exact knowledge, `0` means nothing realizes `i`, and anything larger is
the shortfall. This is the quantity a yes/no `Knowable` collapses.-/
@[expose] public def ambiguity [Fintype Ω] [DecidableEq I] [DecidableEq Y]
    (r : Ω → I) (f : Ω → Y) (i : I) : ℕ :=
  ((fibre r i).image f).card

/-! ## Bridge to the kernel -/

/-! ## The counting obstruction -/

/-! ## The worst case over all observation values -/

/--
The **worst-case ambiguity**: the largest number of target values any single
observation value leaves open.

One scalar for a whole observation, where `ambiguity` is one number per
observation value. That is what a consumer ranking two observations needs, and
the empty fibres contribute `0` rather than distorting the maximum.-/
@[expose] public def worstAmbiguity [Fintype Ω] [DecidableEq I] [DecidableEq Y]
    (r : Ω → I) (f : Ω → Y) : ℕ :=
  (Finset.univ.image r).sup (ambiguity r f)

/-! ## Ambiguity under coarsening -/

end AISafetyAtlas.Knowledge
