/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.RingTheory.Artinian.Ring
import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.TensorProduct.Quotient
import Tengoku.Seed.RingTheory.TensorProduct.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fibrewise finiteness of a quotient

`Module.Finite R (A ⧸ I)` says the closed subscheme `V(I) ⊆ Spec A` is **finite over the
base**. For a relative effective Cartier divisor `D ⊂ C` on a relative curve `C/S` this is
true *globally* (`D ⟶ S` is finite) but **false on a general chart**: a chart cuts `D` down
to an open piece, and an open piece of a finite scheme is only *clopen*-locally finite. The
standard counterexample is `ℤ[1/2]` over `ℤ`, which is `Γ` of a basic open of the finite
`ℤ`-scheme `Spec ℤ`, and is not a finite `ℤ`-module.

What survives — and what every consumer actually uses — is the **fibrewise** statement:

* `ModularCurves.HasFiniteFibres R A I` — for every field `K` over `R`, the base change
  `K ⊗[R] (A ⧸ I)` is a finite `K`-module.

This is exactly "every fibre of `V(I) ⟶ Spec R` is a finite scheme", and unlike finiteness
it *is* inherited by charts: `K ⊗[ℤ] ℤ[1/2]` is `K` or `0`. The mechanism is
`module_finite_tensor_of_localizationAway`: after base change to `K` the ambient finite
algebra becomes Artinian, and a localization of an Artinian ring is a quotient of it
(`IsArtinianRing.localization_surjective`), hence still finite.
-/

universe u

open TensorProduct

namespace ModularCurves

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- `A ⧸ I` **has finite fibres** over `R`: for every field `K` over `R` the base change
`K ⊗[R] (A ⧸ I)` is a finite `K`-module, i.e. every fibre of `V(I) ⟶ Spec R` is a finite
scheme. Weaker than `Module.Finite R (A ⧸ I)`, and — unlike it — stable under passing to a
chart.-/
def HasFiniteFibres (I : Ideal A) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K], Module.Finite K (K ⊗[R] (A ⧸ I))

end ModularCurves
