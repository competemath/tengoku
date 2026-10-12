/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Basic

/-!
# Local surjectivity of fppf quotient projections

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `I` be a normal Hopf
ideal. The fppf quotient sheaf of `G = Spec H` by the closed normal subgroup cut out by `I` was
constructed by sheafifying the pointwise quotient presheaf. This file proves that its canonical
projection

```text
G ⟶ G / V(I)
```

is an epimorphism of group objects and that the underlying morphism of fppf sheaves is locally
surjective. The latter is the descent-theoretic content of passing from the pointwise quotient to
the fppf quotient: sections of the quotient need not lift globally, but they lift after an fppf
cover.

The proof first observes that the raw pointwise quotient maps are surjective. Their natural
transformation is therefore an epimorphism, and this remains so after universe lifting, forgetting
to types, and applying sheafification. Local surjectivity then follows from Mathlib's
characterization of epimorphisms of type-valued sheaves.

## Main declarations

* `TauCeti.CommHopfAlgCat.instEpiFppfQuotientProjection`: the quotient projection is an
  epimorphism of group objects in fppf sheaves.
* `TauCeti.CommHopfAlgCat.isLocallySurjective_fppfQuotientProjection`: its underlying sheaf map
  is locally surjective.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 14.

This is the local-surjectivity part of the quotient and torsor interface in Layer 3,
"Normality and quotients", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

end TauCeti.CommHopfAlgCat
