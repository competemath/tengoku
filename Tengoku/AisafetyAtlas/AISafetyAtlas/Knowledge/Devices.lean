module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.PhysicalKnowledge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The spine–device joint: transports, not an identification

`Knowledge.Knowable` and `Inference.WeaklyInfers` answer the same informal
question — *what can be recovered from evidence* — and are **not** the same
relation. That is a theorem of this development, witnessed both ways on finite
models, and `Inference/Device.lean` says so at length. Nothing here retracts it.

What was missing is the other half: the conditions under which the two
mechanisms **do** talk to each other, as named lemmas a downstream file can
apply. Without them a theorem proved about devices cannot be used by an
oversight file except by restating it.

## The joint object

A device carries two functions on `U`, and the spine takes one observation. The
transport is to read the device's **own pair** as that observation:

`deviceObservation C w = (C.setup w, C.concl w)`

An `IndistinguishabilityWitness` for this observation is a pair of universes the
device is configured identically in and concludes identically in, on which the
target nevertheless differs. That object is what crosses the joint. Neither
component alone crosses it: a setup collision by itself refutes nothing, because
weak inference may answer the probe from a *different* block, which is exactly
the quantifier alternation the non-identification turns on.

## Direction of travel

* **Spine ⟶ device.** One witness kills one block
  (`not_blockAnswers_of_witness`). A witness in *every* realized block, straddling
  the target value, kills weak inference and physical knowledge outright
  (`BlockwiseCollision`). The physical-knowledge refutation is independent of the
  context `W`, because Definition 11's clause (i) is a condition on the whole
  selected block and not on its trace in `W`.
* **Device ⟶ spine.** A device that answers a probe in every realized block has
  its conclusion function *equal* to the probed target, so the probed target is
  knowable from the joint observation by second projection
  (`knowable_probe_of_forall_blockAnswers`).

## What is deliberately absent

There is **no** `Knowable → WeaklyInfers` lemma and there is no iff between
"no collision in a block" and that block answering. Both fail:

* knowability of the target from the setup gives no answering block, since the
  device's conclusion is fixed data and need not agree with any probe;
* a block on which the conclusion is the *negation* of the probed target is
  collision-free and answers nothing.

The countermodels for the first are `Examples.Inference.Device`, which is where
the non-identification is witnessed in both directions.

## Non-claims

This module is **atlas modelling**, not a claim of either Wolpert paper. Nothing
here is graded against a printed statement and nothing here enters the 2008 or
2018 fidelity tallies. Wolpert states no relation between his devices and a
factorization criterion; the transports below are the atlas's own.

No probability, no dynamics, no AI-system reading.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `deviceObservation` | The device's own setup-and-conclusion pair, as a spine observation |
| **Model** | `BlockAnswers` | Definition 3's inner condition, named |
| **Model** | `BlockwiseCollision` | Every realized block hides the target value from the device |
| **Transport** | `not_blockAnswers_of_witness` | A spine witness inside a block stops that block answering |
| **Transport** | `BlockwiseCollision.not_weaklyInfers` | Blockwise collisions refute Definition 3 |
| **Transport** | `BlockwiseCollision.not_physicallyKnows` | …and Definition 11, for every context |
| **Transport** | `knowable_probe_of_forall_blockAnswers` | A device answering everywhere makes the probed target knowable |
| **Boundary** | `blockAnswers_no_collision` | Answering blocks carry no witness — the converse direction, and all of it that holds |

## Axiom profile

Measured with `#print axioms`, not assumed — the same discipline
`Inference/Device.lean` reports for its own split, and for the same reason.

Every refutation and the positive transport depend on **no axioms at all**:
`not_blockAnswers_of_collision`, `not_blockAnswers_of_witness`,
`BlockwiseCollision.not_weaklyInfers`, `BlockwiseCollision.not_physicallyKnows`,
`knowable_probe_of_forall_blockAnswers`, `blockAnswers_no_collision` and
`weaklyInfers_iff_blockAnswers`.

Two exceptions, both expected. `BlockwiseCollision.witnessAt` reports `propext`,
from assembling the product equality. `BlockwiseCollision.not_weaklyInfers_classical`
reports the full classical three, because it constructs a probe — exactly where
`exists_isProbe` puts the choice. Supplying the probe yourself keeps the
refutation constructive.
-/

namespace AISafetyAtlas.Knowledge.Devices

open AISafetyAtlas.Inference

universe u v v'

variable {U : Type u}

/-! ## The joint observation -/

/--
The device's own pair, read as a spine observation: how it is configured together
with what it concludes.

This is the observation the transports below quantify over. It is *not* proposed
as the canonical observation of a device — `C.setup` alone is the paper's
`X`, and the pair is what the joint needs.-/
@[expose] public def deviceObservation (C : InferenceDevice.{u, v} U) :
    U → C.Setup × Bool :=
  fun w => (C.setup w, C.concl w)

/-! ## The block condition, named -/

/--
The inner condition of Definition 3: the block `x` **answers** the probe `f` of
the target, in the sense that the device's conclusion agrees with the probe
throughout the block.

Naming it is the point — Definition 3 is `∀ probe, ∃ realized block, BlockAnswers`,
and every transport below is about one block.-/
@[expose] public def BlockAnswers (C : InferenceDevice.{u, v} U) {G : Type v'}
    (Γ : U → G) (f : G → Bool) (x : C.Setup) : Prop :=
  ∀ w : U, C.setup w = x → C.concl w = f (Γ w)

/-! ## Spine ⟶ device -/

/--
**Blockwise collision at `γ`.** Every realized block of the device contains a
pair it cannot tell apart, one of which sits at the target value `γ` and one of
which does not.

This is the hypothesis both refutations below need. Requiring the pair to
*straddle* `γ` is not slack: a pair on which the target merely differs leaves
both probes of `γ` satisfied, and refutes nothing.-/
@[expose] public def BlockwiseCollision (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (γ : G) : Prop :=
  ∀ x : C.Setup, C.Realized x → ∃ u u' : U,
    C.setup u = x ∧ C.setup u' = x ∧ C.concl u = C.concl u' ∧ Γ u = γ ∧ Γ u' ≠ γ

/-! ## Device ⟶ spine -/

end AISafetyAtlas.Knowledge.Devices
