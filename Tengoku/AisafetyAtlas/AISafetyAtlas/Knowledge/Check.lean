module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Devices
public import Tengoku.Seed.Data.Fintype.Prod
public import Tengoku.Seed.Data.Fintype.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Checkers that run, for the knowability kernel and the device transports

`Knowledge` and `Knowledge.Devices` state their obstructions as `Prop`s and prove
them by hand. That is the right form for a theorem and the wrong form for a
question someone wants answered about a particular finite model, which is the
shape most consumers arrive with — an architecture, a monitor, a hazard.

This module supplies the executable half, on the pattern
`Oversight.JointObservation.FiniteDecision` already sets for coverage: a function
that computes, and a theorem saying the function agrees with the `Prop`. Only the
theorem makes the output evidence rather than a report.

## What runs

* `findCollision` searches a finite state space for an indistinguishability
  witness, returning the pair. `none` is not a failure to find one — it is
  `Knowable`, by `knowable_of_findCollision_eq_none`.
* The `Decidable` instances make `WeaklyInfers`, `Realized` and
  `BlockwiseCollision` evaluate on any finite device. `decide` already settles
  them in the kernel at elaboration time; the instances are what lets a program
  settle them at runtime, on a model it read from a file.

`Examples.Inference.Enumerable.FinDevice` carries its own instance for enumerating *all*
devices of a shape, which is a different job — that one quantifies over devices
and needs both types pinned, while these take the device as given.

## What does not run

Nothing here decides anything about an infinite state space, and nothing here
produces a Lean proof term at runtime. A program using these gets the same answer
the kernel would give, with the theorem below as the reason to believe it; it
does not get a certificate the kernel has checked. That distinction is the whole
content of `atlas-check`'s output and is stated there too.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Checker** | `findCollision` | Search a finite state space for an indistinguishability witness |
| **Law** | `not_knowable_of_findCollision_eq_some` | A returned pair refutes knowability |
| **Law** | `knowable_of_findCollision_eq_none` | Returning nothing *is* knowability |
| **Instance** | `decidableRealized` | Setup values a finite device actually takes |
| **Instance** | `decidableWeaklyInfers` | Definition 3 on a finite device |
| **Instance** | `decidableBlockwiseCollision` | The transport hypothesis on a finite device |
-/

namespace AISafetyAtlas.Knowledge.Check

open AISafetyAtlas.Inference
open AISafetyAtlas.Knowledge

universe u v v'

/-! ## Searching for a witness -/

/--
Every ordered pair drawn from an enumeration of the states.

The enumeration is an argument rather than derived from `Fintype`, for the reason
`FiniteDecision` gives about coverage: `Finset.toList` is noncomputable, so a
checker that reaches for it states the search without running it.-/
@[expose] public def collisionPairs {U : Type u} (enum : List U) : List (U × U) :=
  enum.flatMap fun a => enum.map fun b => (a, b)

/--
Search the enumerated states for a pair the observation cannot separate and the
property does. Returns the first such pair.-/
@[expose] public def findCollision {U : Type u} {I : Type v} {Y : Type v'}
    [DecidableEq I] [DecidableEq Y] (enum : List U)
    (observation : U → I) (property : U → Y) : Option (U × U) :=
  (collisionPairs enum).find? fun p =>
    decide (observation p.1 = observation p.2) && !decide (property p.1 = property p.2)

/-! ## The reader's relabelling changes nothing

`atlas-check` does not hand the kernel the numbers a caller wrote. It relabels
them, keeping only **which states share a value**, so that the codomain is finite
without the caller declaring its size. Until now the claim that this cannot change
a verdict was asserted in a comment, and
[`docs/guide/atlas-check.md`](../../docs/guide/atlas-check.md) named it as the one
step between a caller's JSON and a certified predicate that no theorem covered.

These are that theorem. The hypothesis is exactly what the reader guarantees —
two states share a relabelled value precisely when they shared a raw one — and the
conclusion is that knowability is the same question before and after. Neither
direction needs the relabelling to be injective, surjective, order-preserving, or
into any particular type; it needs only that the partition survives.

`knowable_congr_observation` covers the observation side and
`knowable_congr_property` the property side, so a reader that renumbers both is
covered by composing them. `knowable_comp_left_iff` is the special case a caller
is most likely to reason about: post-composing with an injection.
-/

/-! ## Evaluating the device predicates

Each predicate is a `def` over quantifiers that are finite once the state space
and the setup type are, and instance search works at reducible transparency, so
each is unfolded by hand. Without these a program can state the question and not
answer it.
-/

public instance decidableSurjective {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) : Decidable (Function.Surjective f) := by
  unfold Function.Surjective
  infer_instance

public instance decidableRealized {U : Type u} [Fintype U] (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (x : C.Setup) : Decidable (C.Realized x) := by
  unfold InferenceDevice.Realized
  infer_instance

public instance decidableWeaklyInfers {U : Type u} [Fintype U]
    (C : InferenceDevice.{u, v} U) [Fintype C.Setup] [DecidableEq C.Setup]
    {G : Type v'} [Fintype G] [DecidableEq G] (Γ : U → G) :
    Decidable (WeaklyInfers C Γ) := by
  unfold WeaklyInfers InferenceDevice.Realized IsProbe
  infer_instance

public instance decidableBlockwiseCollision {U : Type u} [Fintype U]
    (C : InferenceDevice.{u, v} U) [Fintype C.Setup] [DecidableEq C.Setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) (γ : G) :
    Decidable (Devices.BlockwiseCollision C Γ γ) := by
  unfold Devices.BlockwiseCollision InferenceDevice.Realized
  infer_instance

end AISafetyAtlas.Knowledge.Check
