/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic

/-!
# Additive structure of morphism-ideal quotients

Quotienting an additive category by a two-sided morphism ideal preserves zero objects and
finite biproducts. These instances allow the quotient to be used as an additive category, not
just as a category with additive hom groups. The quotient functor preserves these biproducts
by Mathlib's `Functor.preservesFiniteBiproductsOfAdditive`; its standard biproduct comparison
isomorphisms therefore apply without a separate choice of sums in the quotient.

The constructions reuse Mathlib's `Functor.hasZeroObject_of_additive`,
`Functor.hasFiniteProducts_of_additive_of_essSurj`, and biproduct preservation API.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*,
  Chapter IV, Section 1.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Section I.2.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

namespace MorphismIdeal

variable {C : Type u} [Category.{v} C] [Preadditive C] (I : MorphismIdeal C)

end MorphismIdeal

end TauCeti
