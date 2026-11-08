module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Control.PolicyKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Open-loop control: mixing the control action never helps

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, Lemma 8 and Theorem 9.

An **open-loop** controller does not observe the state: its action is drawn
independently of the initial state, which is the source's eq. (opd)
*p(x,x',c)ₒₚₑₙ = p_X(x) p_C(c) p(x'|x,c)*. The paper measures such a controller
by the entropy it removes from the state,
*ΔH_open = H(X) − H(X')_open*, and asks whether *randomizing* the action can beat
every fixed action. It cannot:

> the maximum decrease of entropy achieved by a particular subdynamics of control
> variable *ĉ = arg max over c of ΔH_open^c* is *open-loop optimal* in the sense that no
> random (i.e., non-deterministic) choice of the controller's state can improve
> upon that decrease

and in the paper's vocabulary: a **pure** controller — one that plays a single
action with probability 1 — is optimal, and every **mixed** one either matches it
or does worse.

## Why this sits next to eq. (28)

It is the same fact twice. `AISafetyAtlas.Control.PolicyKernel` shows the control
loss `L_C` is *linear* in the controller's weights, so its minimum is at a vertex.
Here the quantity is *ΔH_open*, and the mechanism is *concavity* of entropy rather
than linearity of the objective — mixing the action mixes the outcome law, and
mixing never lowers entropy. Different mechanism, identical conclusion, and the
source draws it in both places.

## Where the open-loop model is spent, and where it is not

**Lemma 8 needs no independence at all.** `entropyReduction_le_condEntropy_form`
is `H(X') ≥ H(X'|C)` rearranged, which holds for any controller whatsoever. The
source states it inside the open-loop section, but its proof — reproduced here —
uses only that conditioning does not raise entropy.

**Theorem 9 does.** `openLoopEntropy` is the entropy of the outcome when the
constant action `c` is applied, computed against `μ` itself; the conditional
`H(X'|C = c)` is computed against `μ` restricted to the fibre. Those agree exactly
when the action carries nothing about the state *or the noise*, which is
`IndepFun C ⟨X, Z⟩ μ` — the atlas's rendering of eq. (opd). It is a hypothesis
here rather than a standing assumption, so a reader can see which result consumes
it.
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

/-! ## Lemma 8: the averaged open-loop reduction dominates -/

/-! ## Theorem 9: a pure controller is open-loop optimal -/

/-! ## A supremum rendering of eq. (48)

Eq. (max1) reads

> `ΔH_open^max = max over p_X(x) ∈ P, c ∈ C of ΔH_open^c`

and the sentence beneath it says what `P` is: *"the maximum entropy decrease that
can be obtained by (pure) open-loop control over **any** input distribution
chosen in the set `P` of all probability distributions"*. So the maximum ranges
over two things at once — the input distribution and the control value — with the
actuation subdynamics held fixed.

Declared here as a supremum over all probability measures on the state space,
inside the independent-noise realization `X' = F(X,c,Z)`. `Real.sSup` of an
unbounded set is junk (`0`), so boundedness is not optional: `[Fintype S]`
supplies it, since the reduction never exceeds the entropy of its own input
distribution and that is at most `log |S|`.

**What this buys, and what remains.** The atlas's `OpenLoopBound` quantifies over
the *conditional ensembles of `μ`*, which is a different family: conditioning `μ`
can move the joint law of state and noise together, whereas the printed maximum
moves the input distribution with the actuation channel fixed. Quantifying over
**all** input distributions removes the mismatch, because each conditional law
`p(x|c)` is then simply one of the distributions being maximized over — which is
exactly the source's own one-sentence justification of the step.

This module states the object over a deterministic `F` driven by an independent
seed `Z`, while the source starts from an arbitrary finite transition kernel
`p(x'|x,c)`. Those are the same family, and `AISafetyAtlas.Control.Purification`
is where that is proved: the source's own §2 says any channel is a *randomly
selected deterministic channel*, `isPurification_purifyMap` constructs one, and
`openLoopMax_purifyMap` shows the two renderings generate the **same set** of
reductions. `kernelEntropyReduction_le_kernelOpenLoopMax` is Theorem 10 with no
`F` and no `Z` in the statement.

The source writes a maximum while `openLoopMax` is an `sSup`. Boundedness is
proved below, and attainment over the input-distribution simplex is proved in
`AISafetyAtlas.Control.OpenLoopAttainment`, so the two agree: by
`isGreatest_kernelOpenLoopMax` the supremum is an element of the family it bounds,
which is what eq. (48)'s `max` asserts.
-/

end AISafetyAtlas.Control
