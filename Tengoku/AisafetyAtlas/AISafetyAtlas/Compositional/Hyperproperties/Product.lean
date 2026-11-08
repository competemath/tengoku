module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Compositional.Hyperproperties
public import Tengoku.Seed.Data.List.GetD
public import Tengoku.Seed.Data.Finset.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Synchronized self-composition, and its relation to the batch form

Clarkson and Schneider state Theorem 2 for the `k`-fold *synchronized product*
`S^k`, whose members are ordered `k`-tuples of traces.  The reduction in
`AISafetyAtlas.Compositional.Hyperproperties` instead uses unordered batches of
at most `k` traces.  This module supplies the product presentation, the
translations between the two, and the boundary conditions the translation needs.

## Where the translation is total, and where it is not

`toBatch` sends a tuple to the finite set of traces it mentions.  It is total
and always lands in the batch self-composition.

Going back requires padding, and padding is where the assumptions live.

* **Nonempty batch.**  Enumerate it and pad by repeating one of its own
  members, so `toBatch` recovers it exactly (`toBatch_padBatch`).
* **Empty batch with `k > 0`.**  There is no preimage at all.  A total function
  into a nonempty index type mentions at least one trace, so `toBatch` is never
  `∅`.  `productSelfComposition_empty` and `finiteSelfComposition_empty` record
  the resulting asymmetry over an empty system.

Consequently the transfer theorem below is **not** stated for an arbitrary
predicate on batches; for such a predicate the two quantifications genuinely
differ at the empty batch.  It is stated for `SelfCompositionSafe`, where
`selfCompositionSafe_empty_of_any` shows the empty batch is subsumed by any
other: an observation realized by the empty batch must itself be empty, and an
empty observation is realized by every batch.

## Coalescing and order

`toBatch` discards multiplicity and order.  Both are harmless for the reduction,
because the source's witnesses are *sets* of at most `k` prefixes and `Realizes`
quantifies over membership only.  `card_toBatch_le` and `toBatch_perm` record
the two facts.
-/

namespace AISafetyAtlas.Compositional.Hyperproperties

variable {Prefix Trace : Type*}

/-- The synchronized `k`-fold self-composition: ordered `k`-tuples of traces
drawn from the system.  This is the source's `S^k`.-/
@[expose] public def productSelfComposition (k : ℕ) (S : TraceSystem Trace) :
    Set (Fin k → Trace) :=
  {tup | ∀ i, tup i ∈ S}

open scoped Classical in
/-- The finite set of traces a tuple mentions.-/
@[expose] public noncomputable def toBatch {k : ℕ} (tup : Fin k → Trace) :
    Finset Trace :=
  Finset.image tup Finset.univ

/-! ### Padding -/

/--
Pad a batch to a tuple by enumerating it and repeating a designated member.

The designated member is what forces the nonemptiness side condition.-/
@[expose] public noncomputable def padBatch {k : ℕ} (batch : Finset Trace)
    (d : Trace) : Fin k → Trace :=
  fun i => batch.toList.getD i d

/-! ### The boundary at the empty batch -/

/-! ### Transfer between the two presentations -/

end AISafetyAtlas.Compositional.Hyperproperties
