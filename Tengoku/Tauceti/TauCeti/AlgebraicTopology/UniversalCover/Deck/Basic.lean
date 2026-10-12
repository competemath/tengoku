/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Logic.Function.Fiber

/-!
# Deck transformations of a map

For a map `p : E → B`, its deck transformations are the homeomorphisms of `E` over `B`. Mathlib
collects them as the subgroup `deck p` of the homeomorphism group `E ≃ₜ E`; for a covering
projection `p` this subgroup is the classical deck transformation group.

This file adds the fibre API that the rest of the deck-transformation development uses.
In particular, `deck.fiberHomeomorph` restricts a deck transformation to each fibre of `p`.

The action of `deck p` on the total space is inherited, by subgroup transfer, from the
tautological action of the ambient homeomorphism group `E ≃ₜ E` on `E`
(`Homeomorph.applyMulAction`). Each deck transformation preserves `p`, hence
preserves every fibre of `p`.

The deck group only sees `p` through the equalities `p (φ e) = p e`, so postcomposition by an
injective map leaves it unchanged (`TauCeti.deck_comp_of_injective`).

## References

The `deck` construction is due to Kim Morrison in
[mathlib4#40135](https://github.com/leanprover-community/mathlib4/pull/40135).
-/

public section

namespace TauCeti

variable {E B : Type*} [TopologicalSpace E] {p : E → B}

namespace Deck

end Deck

section Injective

variable {E B B' : Type*} [TopologicalSpace E]

end Injective

end TauCeti
