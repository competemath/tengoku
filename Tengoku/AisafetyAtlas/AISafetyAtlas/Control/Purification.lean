module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Control.OpenLoop

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Purification: every actuation channel is a deterministic map of an exogenous seed

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, §2, the paragraph introducing
Fig. 2 and eq. (7).

The paper sets up its model with an arbitrary transition matrix `p(x'|x,c)` and
then immediately observes that no generality is lost by taking the actuation
channel to be *deterministic* once an extra variable is carried along:

> From a strict mathematical point of view, note that **any** non-deterministic
> channel modeling a source of noise at the level of actuation or estimation can
> be represented abstractly as a **randomly selected deterministic channel** with
> transition matrix containing only zeros and ones. The outcome of a random
> variable undisclosed to the controller can be thought of as being responsible
> for the choice of the channel to use. […] supplementing our original control
> graphs of Fig. 1 with an **exogenous and non-controllable random variable `Z`**
> in order to 'purify' the channel considered.

and states the condition in two printed parts:

> (i) The mapping from `X` to `X'` conditioned on the values `c` and `z`, as
> described by the extended transition matrix `p(x'|x,c,z)`, is deterministic for
> all `c ∈ C` and `z ∈ Z`.
> (ii) When traced out of `Z`, `p(x'|x,c,z)` reproduces the dynamics of
> `p(x'|x,c)`, i.e. `p(x'|x,c) = ∑_z p(x'|x,c,z) p_Z(z)`.   (7)

Part (i) is discharged by *typing*: the atlas writes the purified channel as a
function `F : S → K → N → T`, so it is deterministic by construction and there is
nothing to assume. Part (ii) is `IsPurification` below, one displayed equation.
`p_Z(z)` rather than `p(z|x,c)` is what "exogenous" means, and it is why the
realized seed is independent of the state and the action.

## What this module supplies that the paper does not

The paper **asserts** the representation and does not construct it. This module
constructs it, and the construction is the paper's own phrase read literally: a
*randomly selected deterministic channel* is a random element of the space of
deterministic channels, `S × K → T`. That space is finite when the alphabets are,
so the seed needs no continuum — `purifySeed` is the product measure that draws
the response to every state–action pair independently from its own column of the
kernel, and `purifyMap` reads off the entry that was asked for.

`exists_isPurification` is the resulting statement: **every** Markov kernel on
finite alphabets is purified by some deterministic map with a seed of its own.

## Why it matters here

`AISafetyAtlas.Control.OpenLoop` proves Theorems 9 and 10 for a plant written as
`X' = F(X, C, Z)` with `Z` independent of `(X, C)`. The source states them for an
arbitrary kernel `p(x'|x,c)`. Without a realization theorem those are different
families and the Lean covers the narrower one. With it they are the same family,
and `kernelEntropyReduction_le_kernelOpenLoopMax` states Theorem 10 with no `F`
and no `Z` anywhere in sight — only the printed `ρ` and `κ`.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uS uK uT

variable {S : Type uS} {K : Type uK} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]

/-! ## The purification condition, eq. (7) -/

/--
**Eq. (7), the purification condition.** The seed `η` and the deterministic map
`F` purify the actuation kernel `κ` when tracing out the seed reproduces `κ`:
for every state `x` and action `c`, pushing `η` forward along `F x c` gives the
column `κ (x, c)`.

Printed part (i) — that the extended channel is deterministic — is carried by the
type of `F` rather than by a hypothesis, so this definition is the whole of the
printed condition.-/
@[expose] public def IsPurification {N : Type*} [MeasurableSpace N]
    (F : S → K → N → T) (η : Measure N) (κ : Kernel (S × K) T) : Prop :=
  ∀ x : S, ∀ c : K, η.map (F x c) = κ (x, c)

/-! ## The construction: a randomly selected deterministic channel -/

/--
**The seed space is the space of deterministic channels.** `purifySeed κ` draws a
deterministic channel `S × K → T` at random, choosing the response to each
state–action pair independently from that pair's column of `κ`. This is the
paper's *"random variable … responsible for the choice of the channel to use"*,
built rather than assumed.-/
@[expose] public noncomputable def purifySeed [Fintype S] [Fintype K]
    (κ : Kernel (S × K) T) : Measure (S × K → T) :=
  Measure.pi fun a => κ a

/--
**The purified actuation map.** Having drawn a deterministic channel, apply it.
Zeros and ones only, as the paper asks: the extended transition matrix
`p(x'|x,c,z)` is `1` exactly when `z (x, c) = x'`.-/
@[expose] public def purifyMap : S → K → (S × K → T) → T :=
  fun x c z => z (x, c)

section Instances

variable [Fintype S] [Fintype K]

end Instances

variable [Fintype S] [Fintype K]

/-! ## Reading a purified system off a joint law and a kernel -/

/-- The measurable map that applies a drawn channel to the pair it was drawn for.-/
@[expose] public def applyChannel : (S × K) × (S × K → T) → T := fun p => p.2 p.1

/-! ## The canonical purified system

Given the printed data — a joint law `ρ` for the state and the action, and an
actuation kernel `κ` — this is *a* control system realizing them, with the seed
carried alongside. Nothing is assumed about it: it is built.
-/

/-- The joint law of the canonical purified system: the printed `ρ` on the
state–action pair, and an independently drawn deterministic channel.-/
@[expose] public noncomputable def purifiedLaw (ρ : Measure (S × K)) (κ : Kernel (S × K) T) :
    Measure ((S × K) × (S × K → T)) :=
  ρ.prod (purifySeed κ)

/-- The initial state of the canonical purified system.-/
@[expose] public def purifiedState : (S × K) × (S × K → T) → S := fun p => p.1.1

/-- The control action of the canonical purified system.-/
@[expose] public def purifiedAction : (S × K) × (S × K → T) → K := fun p => p.1.2

/-- The exogenous seed of the canonical purified system.-/
@[expose] public def purifiedSeed : (S × K) × (S × K → T) → (S × K → T) := Prod.snd

section Canonical

variable (ρ : Measure (S × K)) (κ : Kernel (S × K) T)

end Canonical

/-! ## The printed quantities, stated with no plant and no seed -/

/-! ## Transfer: the purified system computes the printed quantities -/

variable [Fintype T]

/-! ## Theorem 10, at the source's own scope -/

/-! ## Theorem 9, at the source's own scope

Theorem 9 is stated for an **open-loop** controller, whose action is drawn
independently of the state — the source's eq. (opd)
*p(x,x',c)ₒₚₑₙ = p_X(x) p_C(c) p(x'|x,c)*. On the printed data that is `ρ = ν ⊗ p_C`
for an input law `ν` and an action law `pC`, and it is the only extra structure the
theorem needs.
-/

section OpenLoopCanonical

variable (ν : Measure S) (pC : Measure K) (κ : Kernel (S × K) T)

/-- Regroup the canonical system so that the action stands alone.-/
@[expose] public def purifiedRegroup :
    (S × K) × (S × K → T) → (S × (S × K → T)) × K :=
  fun p => ((p.1.1, p.2), p.1.2)

end OpenLoopCanonical

end AISafetyAtlas.Control
