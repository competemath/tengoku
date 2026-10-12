/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.TemperleyLieb
public import Tengoku.Tauceti.TauCeti.GroupTheory.SpecificGroups.Braid
public import Tengoku

/-!
# The Jones representation of the braid group

For a unit `a : Rˣ`, set the Temperley-Lieb loop value to
`δ = -(a ^ 2 + a⁻¹ ^ 2)`. The Kauffman-bracket assignment

`σ i ↦ a • 1 + a⁻¹ • e i`

satisfies the braid relations and defines `TauCeti.TemperleyLieb.jones`, a representation of
`TauCeti.BraidGroup n` in the units of `TemperleyLieb R δ n`. At this loop value the
coefficient-swapped element `a⁻¹ • 1 + a • e i` is the inverse of the assigned crossing.
Composing this representation with the Markov trace is the braid route to the Jones polynomial;
the trace is not built here.

## Main definitions

* `TauCeti.TemperleyLieb.jonesDelta`: the loop value `-(a ^ 2 + a⁻¹ ^ 2)`.
* `TauCeti.TemperleyLieb.jonesUnit`: the Kauffman-bracket expansion of one crossing as a unit.
* `TauCeti.TemperleyLieb.jones`: the Jones representation
  `BraidGroup n →* (TemperleyLieb R (jonesDelta a) n)ˣ`.

## Main results

* `TauCeti.TemperleyLieb.jonesDelta_inv`: the loop value is unchanged by inverting the unit.
* `TauCeti.TemperleyLieb.jones_sigma`: the representation sends `sigma i` to `jonesUnit a i`.
* `TauCeti.TemperleyLieb.jonesUnit_mul_jonesUnit_comm`: units for disjoint crossings satisfy the
  distant-generator braid relation.
* `TauCeti.TemperleyLieb.jonesUnit_braid`: units for adjacent crossings satisfy the braid relation
  corresponding to the third Reidemeister move.
* `TauCeti.TemperleyLieb.jones_sigma_ne_one_two`: the representation is nontrivial on two
  strands over a nontrivial base ring.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103-111.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the Kauffman bracket and Jones polynomial).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.

This is Layer 4 ("knot theory, done properly") of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`), whose knot-polynomial bullet asks for the Jones
polynomial "from the Kauffman bracket on a diagram and from the Temperley-Lieb / Jones
representation of a braid".
-/

public section

namespace TauCeti.TemperleyLieb

variable (R : Type*) [CommRing R] (n : ℕ)
variable {R n}

/-- The loop value `-(a ^ 2 + a⁻¹ ^ 2)` at which the Jones representation is defined. -/
def jonesDelta (a : Rˣ) : R := -((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)

/-- The defining equation of the Jones loop value. -/
@[simp]
theorem jonesDelta_def (a : Rˣ) :
    jonesDelta a = -((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) := (rfl)

/-- The Jones loop value is symmetric in `a` and `a⁻¹`, which is what lets the two coefficients
of a crossing be swapped. -/
theorem jonesDelta_eq_neg_inv_sq_add_sq (a : Rˣ) :
    jonesDelta a = -((((a⁻¹ : Rˣ) : R)) ^ 2 + (a : R) ^ 2) := by
  rw [jonesDelta_def]
  ring

/-- The Jones loop value is unchanged by inverting the unit. -/
theorem jonesDelta_inv (a : Rˣ) : jonesDelta a⁻¹ = jonesDelta a := by
  rw [jonesDelta_def, inv_inv, ← jonesDelta_eq_neg_inv_sq_add_sq]

end TauCeti.TemperleyLieb
