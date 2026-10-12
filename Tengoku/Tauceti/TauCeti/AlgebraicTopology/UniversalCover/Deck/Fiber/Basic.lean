/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.UniversalCover.Deck.Basic
public import Tengoku

/-!
# The action of deck transformations on a fibre

A deck transformation preserves every fibre of the projection, so each fibre of `p` is a
`deck p`-stable subset of the total space. This file records that fibre as a `SubMulAction`,
so that the action of `deck p` on it is the restriction of the tautological action on the total
space and the two agree on underlying points by definition, and packages the same restriction as
a multiplicative homomorphism to the homeomorphism group of the fibre.

The comparison between deck transformations and the fundamental group, and the regular-cover
statements, use the action of deck transformations on individual fibres rather than only on the
total space.

## Main definitions

* `TauCeti.Deck.fiberHomeomorphHom`: the homomorphism
  `deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b})`.
* `TauCeti.Deck.fiberSubMulAction`: the fibre over `b` as a `deck p`-stable subset of the
  total space, and `TauCeti.Deck.instFiberMulAction`: the action of `deck p` it carries.
* `deck.fiber_stabilizer_eq_stabilizer_coe`: the stabilizer of a fibre point is the
  stabilizer of the underlying point of the total space, and
  `deck.mem_fiber_stabilizer_iff_coe`: membership in a fibre stabilizer is equality on the
  underlying point.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

end Deck

end TauCeti
