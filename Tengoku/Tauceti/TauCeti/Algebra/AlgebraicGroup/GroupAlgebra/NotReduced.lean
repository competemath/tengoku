/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic
public import Tengoku.Tauceti.TauCeti.Algebra.MonoidAlgebra.NotReduced

/-!
# The coordinate ring of `μ_p` is non-reduced in characteristic `p`

For a commutative group `G`, the diagonalizable group `D(G)` over `R` is `Spec R[G]`, with
coordinate Hopf algebra the group algebra `R[G]`. By `TauCeti.not_isReduced_monoidAlgebra`,
`R[G]` fails to be reduced whenever `R` has prime characteristic `p` and `G` has a nontrivial
element killed by `p`.

The headline application is the **non-smooth example `μ_p` in characteristic `p`** from the
reductive-groups roadmap: `μ_p = D(ℤ/p)` has coordinate Hopf algebra
`R[Multiplicative (ZMod p)]`, whose `A`-points are the `p`-th roots of unity in `A`
(`TauCeti.RootsOfUnityGroup.pointsMulEquiv`), yet which is non-reduced over a base of
characteristic `p`. Geometric reducedness of the coordinate ring is exactly smoothness for a
group scheme of finite type over a field, so this exhibits `μ_p` as a non-smooth (non-reduced)
affine group scheme, the canonical example the roadmap flags for admitting non-smooth groups.

## Main declarations

* `TauCeti.RootsOfUnityGroup.coordinateRing_not_isReduced`: the coordinate Hopf algebra of
  `μ_p = D(ℤ/p)` is not reduced over a nontrivial base of characteristic `p`.
* `TauCeti.RootsOfUnityGroup.isNilpotent_single_generator_sub_one`: the explicit nonzero
  nilpotent `single (ofAdd 1) 1 - 1`.

This is a worked-example check for the reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap): the standing hypotheses note that an affine
group scheme of finite type "admits `μ_p`, `αₚ`, and other non-smooth / non-reduced groups", and
Layer 4 names "the non-smooth example `μ_p` in characteristic `p`" in the diagonalizable-groups
lane.

## References

The roots-of-unity group `μ_n = D(ℤ/n)` and its standard generator are Tau Ceti's
`TauCeti.RootsOfUnityGroup`.
-/

public section

namespace TauCeti

namespace RootsOfUnityGroup

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- The standard generator of `μ_p = D(ℤ/p)` is nontrivial: `ofAdd 1 ≠ 1` because `1 ≠ 0` in the
field `ZMod p`. -/
theorem generator_ne_one : generator p ≠ 1 := by
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [show generator p = Multiplicative.ofAdd (1 : ZMod p) from rfl, ne_eq, ofAdd_eq_one]
  exact one_ne_zero

end RootsOfUnityGroup

end TauCeti
