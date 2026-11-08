module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Compositional.Hyperproperties
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-observation safety, in the shared knowability vocabulary

## Statement intent

- **Objects.** A trace batch as the world, the set of finite observations the
  batch realizes as the observation, and the safety predicate as the hidden
  property.
- **Conclusion.** `knowable_of_isSafetyPredicate`: an ordinary finite-observation
  safety predicate factors through the batch's realized observations. So the
  predicate is `Knowledge.Knowable` from that observation, and the kernel's laws
  apply to it.
- **Mechanism.** `IsSafetyPredicate` gives, for each violating batch, one finite
  observation whose every realizer also violates. Two batches realizing exactly
  the same observations therefore agree, which is the no-collision condition
  `Knowledge.knowable_iff_no_collision` asks for.

## Why this direction

`Hyperproperties` already states its own safety notions and proves the
Clarkson–Schneider reduction over them. What it did not have was any edge to the
rest of the tree: nothing in this cluster referred to `AISafetyAtlas.Knowledge`,
and nothing outside `Compositional` referred to these definitions. The adapter
lives here rather than in `Knowledge`, so the dependency runs downstream only and
the kernel stays free of trace vocabulary.

## Explicit non-claims

- **Not new mathematics.** `IsSafetyPredicate` is unchanged and its consequences
  are unchanged; `knowable_of_isSafetyPredicate` derives nothing the definition
  did not already say. What is new is that it is said in the vocabulary
  `Knowledge` shares with `Oversight`, `Preference` and `Wireheading`.
- **Not a converse.** Knowability from `realizedSet` does **not** give back
  `IsSafetyPredicate`. Factorization says the predicate is constant on batches
  with equal realized-observation sets; safety says more, that each violation is
  witnessed by a *single finite* observation all of whose realizers violate.
  Finiteness and the per-violation witness are lost on the way in, and no attempt
  is made to recover them.
- **Not a trace producer.** This connects the *consumer* side of the trace theory
  to the kernel, and nothing here produces a trace. The producer is
  `AISafetyAtlas.Compositional.NetworkTraces`, which reads one of the four
  execution-generating modules as a `TraceSystem`; the other three —
  `Compositional.Symmetry`, `Wireheading.CRMDP` and
  `Wireheading.GoalPreservation` — still have no trace consumer.
- **Not** a claim about `IsKSafety`, `IsHyperSafety` or `IsHyperLiveness`. Only
  the ordinary batch-predicate notion is routed.

## Scope boundary

The property lands in `Prop`, so `knowable_iff_no_collision`'s `[Nonempty Y]` is
discharged by `Prop` being inhabited, and the collision step closes with
`propext`. Nothing here needs `prefixOf` to be decidable, or `Prefix` and `Trace`
to be finite.
-/

namespace AISafetyAtlas.Compositional.Hyperproperties

universe u v

variable {Prefix : Type u} {Trace : Type v}

/--
The finite observations a batch realizes.

This is the observation map: everything a finite-observation safety argument may
read about a batch, and nothing else. Two batches with the same realized set are
indistinguishable to every such argument.-/
@[expose] public def realizedSet (prefixOf : Prefix → Trace → Prop)
    (batch : Finset Trace) : Set (Observation Prefix) :=
  {M | Realizes prefixOf M (batch : Set Trace)}

end AISafetyAtlas.Compositional.Hyperproperties
