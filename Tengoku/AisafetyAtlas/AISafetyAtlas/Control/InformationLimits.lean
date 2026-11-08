module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.InformationTheory.DataProcessing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Information-theoretic limits on control

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004 — the source cited by `BY-005`.

A controller acts on a system whose initial state is `X`. It issues a control
action `C`; an actuation channel, disturbed by noise `Z`, carries the pair to a
final state `X'`. The paper measures a controller by two quantities. The **control loss**, its
eq. (28), is `L_C = min over {p(c|x)} of H(X' | X, C)` — *minimized*, "to ensure
that `L_C` reflects the properties of the actuation channel, and does not depend
on one's choice of control inputs". The **entropy reduction**
`ΔH = H(X) − H(X')` is how much the controller narrows the state.

Both readings of `L_C` are here. `controlLoss` is the loss of the controller at
hand; `minControlLoss` is a generic realized-policy infimum over a set of
controllers sharing one plant. `inputPolicies` supplies the measurable
conditional-independence set realizable on the current sample space; for finite
alphabets its infimum is proved equal to the source's minimum over all kernels
`p(c|x)` in `AISafetyAtlas.Control.PolicyKernel`. The pointwise results come
first because they are the sharper ones: each is proved at *every* controller,
and the corresponding infimum statement is then obtained for the represented
feasible family. `Examples…minControlLoss_lt_controlLoss_gate`
shows the minimization is not a formality.

Four of the paper's results are proved here.

| source | statement | pointwise in the controller | at a represented policy infimum |
|---|---|---|---|
| Theorem 2 | `L_C ≤ H(Z)`, with equality iff `H(Z | X', X, C) = 0` | `entropy_noise_sub_controlLoss` and its two corollaries | `minControlLoss_le_entropy_noise` for the inequality; the equality case needs a minimizer, which `PolicyKernel` constructs |
| Theorem 3 | `L_C = I(X' : Z | X, C)` | `controlLoss_eq_condMutualInfo` | `minControlLoss_eq_sInf_condMutualInfo` |
| Theorem 4 | `L_C = I(X' : X, C, Z) − I(X' : X, C)` | `controlLoss_eq_mutualInfo_sub` | `minControlLoss_eq_sInf_mutualInfo_sub` |
| Theorem 10 | `ΔH_closed ≤ ΔH_open^max + I(X ; C)` | `entropyReduction_le_of_openLoopBound` | — |

Theorem 10 is the paper's main result and the one with the AI-safety reading:
*one bit gathered by the controller is worth at most one bit of extra entropy
reduction*. Feedback is not free, and it is not better than free.

## Where this is stronger than the printed source

* **Theorem 2 is proved as an identity, not an inequality plus a separate
  equality condition.** `entropy_noise_sub_controlLoss` states
  `H(Z) − L_C = H(Z | X', X, C)` exactly. The printed inequality is that
  quantity being nonnegative and the printed equality condition is it being
  zero, so both are corollaries of one statement and neither needs its own
  argument.
* **No assumption on the sample space — and this is *not* one of the ways it is
  stronger.** Everything here holds over an arbitrary measurable space carrying a
  zero-or-probability measure, where the source works with discrete distributions
  on finite alphabets. But the variables are still countable of finite range, so
  they push the measure forward to a pmf on those same finite alphabets, the
  printed theorem applies to that pmf, and the statement here is the printed
  statement at the pushforward. The two are inter-derivable: `Ω` is a
  presentation, not a generality. What it buys a reader is that a model which is
  not born discrete needs no pushforward constructed by hand. See the
  sample-space note in `docs/provenance/source-coverage-audit.md`.
* **Theorems 2, 3 and 4 are proved at every controller, not at a minimizer.**
  The pointwise statements and the arbitrary-`P` infimum statements are both
  available. The latter apply to a represented feasible family on one sample
  space. Identifying that family's infimum with the source's minimum over every
  kernel `p(c|x)` is `AISafetyAtlas.Control.PolicyKernel`, which also constructs
  the minimizer Theorem 2's *equality* case asks for, so nothing here has to
  assume attainment. See `docs/provenance/touchette-lloyd-control.md`.
* **The purification hypothesis is used exactly where it is needed.** It appears
  as an explicit argument on the statements that use it and nowhere else, so a
  reader can see which results survive without it — Theorem 10 does.

## Step (50)

Theorem 10 rests on the paper's step (50), *"a closed-loop controller is formally
equivalent to an ensemble of open-loop controllers acting on the conditional
supports"*. The paper does justify it, in one sentence beneath the proof: *"each
conditional distribution `p(x|c)` is a legitimate input distribution for the
initial state of the controlled system. It is, in any cases, an element of `P`."*
`P` is the set of all input distributions the maximum in (48) ranges over.

Both readings are available here.

* `entropyReduction_le_of_condEntropy_ge` takes the *averaged* form, printed as
  (51), as a hypothesis and claims nothing about the model. This is the
  conservative form: it is exactly what follows *from* the step.
  `condEntropy_ge_of_openLoopBound` delivers the per-action form (50), and
  `condEntropy_le_condEntropy_of_forall` averages one into the other.
* `entropyReduction_le_of_openLoopBound` **derives** it, by mechanizing that
  sentence. `IsPlant` writes the actuation channel as a map `X' = F(X, C, Z)`;
  `OpenLoopBound` says no constant control reduces the entropy of the state by
  more than `Δopen`, on every conditional ensemble of `μ` — which is the
  "each `p(x|c)` is an element of `P`" clause, stated as a hypothesis.

`IsPlant` and `OpenLoopBound` are the atlas's rendering of the paper's model, not
formulas the paper writes. In particular the paper's `ΔH_open^max` is a maximum
over input distributions with the actuation subdynamics held fixed, whereas
conditioning `μ` on an event can also change the joint law of state and noise; the
two families are close but not literally the same, so no instance relation is
claimed in either direction. See `docs/provenance/touchette-lloyd-control.md`.

## Provenance

The published Physica A text has been read. The formalization was carried out
against arXiv:`physics/0104007v2` (May 2003), the authors' own latest preprint;
Theorems 1–11 are numbered identically in the two, and the four formalized here
match statement for statement. Theorem numbers below are
common to both. See `docs/provenance/touchette-lloyd-control.md`.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uΩ uS uK uN uT

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K]
variable [MeasurableSpace N] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K]
variable [MeasurableSingletonClass N] [MeasurableSingletonClass T]
variable [Countable S] [Countable K] [Countable N] [Countable T]
variable {μ : Measure Ω}

/-! ## The two measures of a controller -/

/-! ## Theorem 2: the actuation noise bounds the control loss -/

/-! ## Theorems 3 and 4: the control loss as an information -/

/-! ## Theorem 10: feedback is worth at most what it measures

The paper's main result. The step it rests on — that a closed-loop controller is
an ensemble of open-loop controllers acting on the conditional supports — is
hypothesis, not conclusion; see the module docstring. -/

/-! ### Step (50), derived from an explicit open-loop model

The paper asserts step (50) from the informal equivalence *"a closed-loop
controller is an ensemble of open-loop controllers acting on the conditional
supports `supp(X|c)` instead of `supp(X)`"*. Making that equivalence a
definition rather than a sentence turns the assertion into a proof.

Two ingredients. `IsPlant` says the final state is a fixed function of the
initial state, the control action and the noise — the paper's actuation channel,
written as a map. `OpenLoopBound` says no *constant* control reduces the entropy
of the state by more than `Δopen`, **for every ensemble**, which is exactly the
"instead of `supp(X)`" clause: the conditional ensembles `X | C = c` are not the
one the bound was quoted for, so a bound quantified only over `supp(X)` would not
transfer. -/

/-- **The actuation channel as a map.** The final state is determined by the
initial state, the control action and the noise.-/
@[expose] public def IsPlant (F : S → K → N → T)
    (X : Ω → S) (C : Ω → K) (Z : Ω → N) (X' : Ω → T) : Prop :=
  ∀ ω, X' ω = F (X ω) (C ω) (Z ω)

/-! ## Eq. (28): the control loss minimized over the controller

Everything above is pointwise in the controller. The paper's `L_C` is not: eq.
(28) reads

`L_C = min over {p(c|x)} of H(X' | X, C)`,

and the parenthesis under it says why — *"the minimization over all conditional
distributions for `C` is there to ensure that `L_C` reflects the properties of
the actuation channel, and does not depend on one's choice of control inputs."*
So the minimization ranges over the **controller** while the source law of `X`,
the noise `Z` and the actuation channel are held fixed.

That constraint is what `IsPlant` supplies. Varying the controller varies the
final state too, so the printed quantity is a minimum of `H(X' | X, C)` along a
*family* of pairs `(C, X')` sharing one plant — not a minimum over `C` at a fixed
`X'`, which would be the wrong object. -/

/--
**The state a fixed plant produces under a given controller.** With the actuation
map `F`, the initial state `X` and the noise `Z` all fixed, a choice of
controller `C` determines the final state. `isPlant_plantOutcome` records that
this is a plant, by definition.-/
@[expose] public def plantOutcome (F : S → K → N → T)
    (X : Ω → S) (C : Ω → K) (Z : Ω → N) : Ω → T :=
  fun ω => F (X ω) (C ω) (Z ω)

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace N]
  [MeasurableSpace T] [MeasurableSingletonClass S] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
public theorem isPlant_plantOutcome (F : S → K → N → T)
    (X : Ω → S) (C : Ω → K) (Z : Ω → N) :
    IsPlant F X C Z (plantOutcome F X C Z) := fun _ => rfl

end AISafetyAtlas.Control
