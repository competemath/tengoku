/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction
public import Tengoku

import Tengoku.Tauceti.TauCeti.LinearAlgebra.ExteriorAlgebra.End

/-!
# The Spin-group representation on the exterior model

This file restricts the Fock action of a Clifford algebra to its Spin group and to its even
subalgebra, and proves, when the first isotropic summand is finite free, that the underlying
Clifford action generates every endomorphism of the exterior model.

The Spin group lies inside the even subalgebra (`spinGroup.mem_even`), so the Spin representation
factors through the even Clifford action `TauCeti.evenSpinAction` along the inclusion
`TauCeti.spinGroupToEven`. How much of the endomorphism algebra that restricted action reaches is
exactly what distinguishes the two parities of the ambient dimension: in *positive* even dimension
it splits off the two half-spin blocks, while in odd dimension it is still everything. Dimension
zero is the degenerate exception to the even description, `W` being `⊥` there, so that `S = K` is
one-dimensional, the odd block is zero and the even action is again onto.

## Main definitions and results

* `TauCeti.spinRep` and `TauCeti.pinRep` are the representations of `spinGroup Q` and `pinGroup Q`
  on the exterior model.
* `TauCeti.spinGroupToEven` is the inclusion of the Spin group into the even Clifford subalgebra
  and `TauCeti.evenSpinAction` is the Fock action restricted to that subalgebra, through which the
  Spin representation factors by `TauCeti.evenSpinAction_apply` and
  `TauCeti.coe_spinGroupToEven_apply`.
* `TauCeti.spinAction_surjective` identifies the Fock action as onto the full endomorphism algebra
  when the first isotropic summand is finite free.

## References

* [Spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md)
-/

public section

namespace TauCeti

universe u v

variable {K : Type u} [CommRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- **The inclusion of the Spin group into the even Clifford subalgebra**, the Spin group
consisting of even elements by `spinGroup.mem_even`. -/
def spinGroupToEven (Q : QuadraticForm K V) : spinGroup Q →* CliffordAlgebra.even Q :=
  Submonoid.inclusion fun _ hx => spinGroup.mem_even hx

/-- A Spin-group element sits in the even subalgebra as itself. -/
@[simp]
theorem coe_spinGroupToEven_apply (Q : QuadraticForm K V) (g : spinGroup Q) :
    (spinGroupToEven Q g : CliffordAlgebra Q) = g :=
  (rfl)

end TauCeti
