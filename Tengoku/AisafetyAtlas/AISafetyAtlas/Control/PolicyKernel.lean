module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Control.InformationLimits
public import Tengoku.Seed.Probability.Kernel.Composition.MeasureCompProd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Eq. (28) as a minimum over kernels, and why deterministic feedback attains it

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, eq. (28).

`AISafetyAtlas.Control.minControlLoss` is an infimum over controllers
*realizable on one sample space*. The source minimizes over conditional
distributions `{p(c|x)}`, and a fixed `Ω` need not realize every one of them —
a space carrying no auxiliary randomness realizes only some. That leaves the
realized infimum `≥` the source's, with no proved equality, and it is why
Theorem 2's *equality* case — a statement about a minimizer — did not transfer.

This module closes that gap by declaring the source's object and proving the two
agree.

## The argument, and where it comes from

Eq. (28) is displayed in the source in two lines, and the second is the one that
matters:

> `L_C = min over {p(c|x)} of H(X'|X,C)`
> `    = min over {p(c|x)} of ∑_x p_X(x) ∑_c H(X'|x,c) p(c|x)`

The numbers `H(X'|x,c)` are fixed by the actuation channel; only the weights
`p(c|x)` vary. So each inner sum is a weighted average of fixed numbers over
weights of the caller's choosing, and a weighted average is never below the
least number averaged. Putting all the weight on a minimizing `c` is therefore
optimal, and the minimum is

*∑_x p_X(x) · min over c of H(X'|x,c)*,

attained by the **deterministic** rule "at state `x`, play a minimizing `c`".

Deterministic rules are the ones that need no auxiliary randomness: `c ∘ X` is
realizable on *every* sample space. So the realized infimum and the kernel
infimum are attained by the same policies and are equal — and, being attained,
Theorem 2's equality case transfers with no attainment hypothesis.

This is the source's own thesis, transposed. Theorem 9 proves the open-loop half
of it in the paper's own words — *"no random choice of the controller's state
can improve upon that decrease"*, a **pure** controller beating every **mixed**
one. Eq. (28) has the same simplex structure, so `L_C` gets the same conclusion.

## What conditional independence buys

`atomLoss` is well defined — a function of `(x, c)` alone, not of the policy —
only because the controller carries no information about the noise beyond what
the state carries. That is `IsInputPolicy`, and it is exactly what fails for a
noise-reading controller: `Examples…minControlLoss_univ_lt_inputPolicy` exhibits
one that beats every input policy, so the linearity this whole module rests on
is not available on `Set.univ` and the closed form there is false.

## Finiteness

`[Finite K]` is the printed setting — the source's alphabets are finite — and it
is what makes a minimizing action exist rather than merely being approached. It
also supplies `FiniteRange C` for *arbitrary* members of `inputPolicies`, which
a bare `Countable K` does not.
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

/-! ## Independence at one atom -/

/-! ## The actuation loss at a state-action pair -/

/-! ## The closed form

From here the state and action alphabets `S` and `K` are finite. This is what
makes eq. (28)'s policy simplex finite-dimensional and turns the printed `min`
into a value that is *reached*. The noise and outcome types remain countable in
the surrounding general model; the printed all-finite setting is recovered by
specialization.
-/

/-! ## Deterministic state feedback attains it -/

/-! ## Eq. (28)'s own object: a minimum over conditional distributions

`{p(c|x)}` is a set of stochastic kernels `S → K`, not a set of random variables
on `Ω`. Declared here as such, so that the printed minimization is an object in
the tree rather than a reading of one.

A kernel `κ` is realized by pairing the original space with the action drawn from
it: `μ ⊗ₘ κ.comap X hX` on `Ω × K`, where the state and noise are read off the
first coordinate and the action *is* the second. That the action is drawn from
`κ (X ω)` — the state and nothing else — is built into `comap X`, so this
construction can express every `p(c|x)` and nothing more.
-/

/-- **The joint law of state, noise and an action drawn from `p(c|x)`.**-/
@[expose] public noncomputable def kernelMeasure (μ : Measure Ω) {X : Ω → S}
    (hX : Measurable X) (κ : Kernel S K) : Measure (Ω × K) :=
  μ ⊗ₘ κ.comap X hX

end AISafetyAtlas.Control
