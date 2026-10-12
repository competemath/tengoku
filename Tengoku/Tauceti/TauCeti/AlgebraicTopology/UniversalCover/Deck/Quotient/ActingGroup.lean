/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected.Basic

/-!
# The acting group of a quotient covering map is its deck group

Let `f : E → X` be a quotient covering map for a group `G` acting on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`. Every group element then acts on `E` by a homeomorphism
over `X`, so translation gives a group homomorphism `G →* deck f`.

This homomorphism is injective as soon as `E` is nonempty, because the action of a quotient
covering map is free. It is surjective when `E` is preconnected: a deck transformation agrees
at one point with some translation, and two deck transformations of a preconnected covering
that agree at a point agree everywhere (and if `E` is empty there is nothing to prove). So
for preconnected nonempty `E` the acting group *is* the deck group, `G ≃* deck f`.

Neither hypothesis is needed to see that the deck action of a quotient covering map is
regular; that consequence is recorded in
`TauCeti/AlgebraicTopology/UniversalCover/deck/Quotient/Covering.lean`, where it generalizes
the previous statement for the acting group `deck f` itself.

## Main declarations

* `TauCeti.Deck.IsQuotientCoveringMap.toDeckHom`: translation by a group element, as a
  homomorphism from the acting group to the deck group.
* `TauCeti.Deck.IsQuotientCoveringMap.toDeckHom_injective`: it is injective on a nonempty
  total space.
* `TauCeti.Deck.IsQuotientCoveringMap.toDeckHom_surjective`: it is surjective on a
  preconnected total space.
* `TauCeti.Deck.IsQuotientCoveringMap.toDeckHom_bijective`: it is bijective on a preconnected
  nonempty total space.
* `TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv`: for a preconnected nonempty total space,
  the acting group is isomorphic to the deck group.

## References

A cover presented as a quotient by a group action has that group as its deck group, which is
how the deck group of a concrete cover such as `Sⁿ → RPⁿ` is computed. The quotient covering
map API it consumes (`Mathlib/Topology/Covering/Quotient.lean`) is due to Junyan Xu.
Surjectivity rests on uniqueness of lifts through a covering map,
`IsCoveringMap.eq_of_comp_eq` in `Mathlib/Topology/Covering/Basic.lean`, due to Thomas
Browning after Hatcher, *Algebraic Topology*, Proposition 1.34; it is used here through the
Tau Ceti wrapper `TauCeti.Deck.eq_of_apply_eq`.
-/

public section

namespace TauCeti

namespace Deck

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}
variable [Group G] [MulAction G E]

namespace IsQuotientCoveringMap

variable (hf : IsQuotientCoveringMap f G)
include hf

end IsQuotientCoveringMap

end Deck

end TauCeti
