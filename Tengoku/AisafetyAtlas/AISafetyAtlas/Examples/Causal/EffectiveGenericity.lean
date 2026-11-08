module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.EffectiveGenericity
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Worked model of MAIS-O24's certificate layer

`AISafetyAtlas.Causal.EffectiveGenericity` renders `prob:effective`'s polynomial
list and the class `𝕄(sk, λ, μ)` it cuts. This module runs both on the
two-variable skeleton, and checks the facts that decide whether the class is the
printed object rather than a shape with the right name:

* `S` really is the number of variables the polynomials range over, so the size
  bounds are bounds in the printed parameter;
* the list a solution supplies at a skeleton depends on the skeleton's **shape**
  and on nothing else — two skeletons that differ only in their numeric utility
  get the same list, which is the quantifier `prob:effective` fixes when it asks
  for a list *"for each diagram shape `(𝐂, 𝐎, 𝐙)`"*;
* both of conclusion (c)'s domains are the printed ones, and every object the
  problem quantifies over lands inside them;
* an **empty** list cuts nothing, so `𝕄(sk, λ, μ)` degenerates to `𝕄(sk, λ)`
  exactly when the certificate is vacuous. That degeneracy is the reason the
  atlas's earlier stand-in needed a hand-added properness clause, and it is not
  a defect of print's class — print's list comes from a solution, and a solution
  must satisfy conclusion (c), which an empty list cannot help with.
-/

namespace AISafetyAtlas.Examples.Causal.EffectiveGenericity

open AISafetyAtlas.Causal AISafetyAtlas.InformationTheory
open AISafetyAtlas.Examples.Causal

/-! ## `S` is the printed parameter -/

/-! ## The list cannot see the utility

`prob:effective` asks for a list *"for each diagram shape `(𝐂, 𝐎, 𝐙)` and each
compatible graph `G`"*, with `u` a **variable** of the polynomials. So a
solution's list is a function of the shape, and two skeletons sharing a shape
share a list however their utilities differ.

An earlier version of this module indexed the list by a whole `Skeleton`, which
carries the numeric utility, and so allowed exactly what print forbids: a
different certificate for each utility it was supposed to treat symbolically. -/

/-- A second skeleton on the same shape as `skel`, with a **different** utility:
`skel`'s gap is negated. Nothing about the shape changes.-/
public noncomputable def skelFlipped : Skeleton (Fin 2) (binaryDim (Fin 2)) Bool ℝ where
  observed := (skel.mapRat ℝ).observed
  utilityParents := (skel.mapRat ℝ).utilityParents
  utility := fun d v ↦ (skel.mapRat ℝ).utility (!d) v
  utility_parents := fun d v w h ↦ (skel.mapRat ℝ).utility_parents (!d) v w h
  utility_mem_unitInterval := fun d v ↦ (skel.mapRat ℝ).utility_mem_unitInterval (!d) v

/-! ## Conclusion (c)'s two domains

Print measures a set of `θ` and quantifies almost-every `u`, and both ranges are
bounded: table entries are probabilities, and `u : {0,1} × dom(𝐙) → [0,1]` makes
the gap coordinates lie in `[-1,1]`. Both bounds are load-bearing, but they fail
in *opposite* directions and it is worth being exact about which is which.

Dropping the `θ` bound makes (c) **weaker**: measured in all of `ℝ^{K(G)}` an
excluded set of infinite measure passes, since `(⊤ : ℝ≥0∞).toReal = 0`.

Dropping the `u` bound makes (c) **stronger**: `utilityBox` has positive measure,
so almost-everywhere on the ambient space implies almost-everywhere on the box, and the
unbounded form demands the estimate at utilities no skeleton realizes. That
admits fewer solutions than print's problem, so a downstream *"for every O24
solution, …"* would come out weaker than print. -/

/-! ## The empty certificate -/

/-! ## The bundle's fields bite

`O24Solution` is a predicate on a construction, and no inhabitant is expected —
`prob:effective` is an open problem. But a predicate can fail to have an
inhabitant for two very different reasons, and only one of them is acceptable
here. If the fields were jointly *contradictory*, then a downstream statement
reading *"for every O24 solution, …"* would be vacuously true, which is the
failure the O26 antecedent package must also rule out, and which is open on
that side too.

The check below is the cheap half of that: conclusion (a) is a real obstruction,
so the degenerate candidate — the assignment that supplies no polynomials at all
— is rejected by the bundle rather than accepted by it. That is evidence the
fields do work, not a claim that a solution exists. -/

/-! ## The variables are named, and the names are readable

The construction clause asks the machine to write polynomials in `(θ, u)`. What
makes that a statement about polynomials rather than about a string is that the
syntax names its variables and the naming is a **definition**: `encodeO24Var` is
fixed by the problem, not supplied by the solution.

The alternative the atlas carried until 2026-08-21 — syntax over `Fin S` plus a
solution-supplied bijection `O24Var Z G ≃ Fin S` — fails here. A bijection is an
encoding, and an unrestricted encoding is advice: it carries `log₂(S!)` bits of
per-instance choice about which coordinate each monomial is about, so a machine
emitting fixed syntax could "construct" a certificate it never computed. -/

end AISafetyAtlas.Examples.Causal.EffectiveGenericity
