module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Embedded.Composition
public import Tengoku.Seed.Data.Fintype.Card
public import Tengoku.Seed.Data.Fintype.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite operational cardinality bridges

When apparatus and global state spaces are finite, a strict cardinality gap

\[
  |A| < |\Omega|
\]

forces the restriction `Ω → A` to be non-injective (pigeonhole), hence
`ProperInclusion`, hence Breuer Proposition 1 under meshing.

This is **not** the universal physical theorem. It is the operational corollary
for finite hardware abstractions, bounded controllers, and discretized
environments. Infinite or continuous models should use
`Embedded.Composition` (nontrivial remainder) instead of inventing a cardinality
comparison they do not have.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `properInclusion_of_card_lt` | Pigeonhole: `card A < card Ω` forces the restriction to collide |
| **Boundary** | `no_meshing_measures_all_of_card_lt` | Breuer Proposition 1 under a finite cardinality gap |
| **Law** | `properInclusion_product_of_card_rest_ge_two` | Product form, when only `2 ≤ card R` is known rather than two named remainders |

All three are classical: they route through `properInclusion_iff_not_injective`,
whose backward direction pushes a negation through a binder and so pulls
`Classical.choice`. Constructivity does not follow from the finiteness.

## Bekenstein

Entropy/energy bounds (Bekenstein and related literature) can **motivate**
finite operational models in provenance notes. They do **not** automatically
yield `|A| < |Ω|` for every physical subsystem, and this module does not encode
any such implication. See `docs/provenance/self-measurement-kernel.md`.

## Explicit non-claims

* Not “every physical containment has a cardinality gap.”
* Not a quantum / continuum result.
* Not Breuer’s paper theorem (that remains `Knowledge.Embedded`).
-/

namespace AISafetyAtlas.Knowledge.Embedded.Finite

open AISafetyAtlas.Knowledge.Embedded
open AISafetyAtlas.Knowledge.Embedded.Composition

universe u v

end AISafetyAtlas.Knowledge.Embedded.Finite
