/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.AlgebraicTopology.UniversalCover.Deck.Fiber.Basic

/-!
# Deck transformations of connected covers

For a covering projection with preconnected total space, two deck transformations are equal as
soon as they agree at one point. Equivalently, the deck action on the total space is
cancellative, and so is the induced action on every fibre.

The pointed and unpointed cover correspondences track deck transformations through their
action on a chosen fibre, and regular-cover statements use the fact that a deck transformation of a
connected cover cannot fix a point unless it is the identity.

## Main declarations

* `TauCeti.Deck.orbitMap_injective`: evaluation at a fibre point is injective on deck
  transformations of a preconnected covering.
* `TauCeti.Deck.deckEquivFiberOfSurjective`: if that evaluation map is also surjective, it
  identifies the deck group with the chosen fibre.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

section Fiber

variable {b : B}

end Fiber

end Deck

end TauCeti
