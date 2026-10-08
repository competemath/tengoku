/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Hom.Ring
public import Tengoku.Seed.Algebra.Order.Ring.InjSurj
public import Tengoku.Seed.Algebra.Ring.Subring.Defs

/-!
# Subrings of ordered rings

We study subrings of ordered rings and prove their basic properties.

## Main definitions and results

* `Subring.orderedSubtype`: the inclusion `S → R` of a subring as an ordered ring homomorphism
* various ordered instances: a subring of an `IsOrderedRing` or an `IsStrictOrderRing` is again
  the respective kind of ordered ring.
-/

@[expose] public section

namespace Subring

variable {R S : Type*} [Ring R] [PartialOrder R] [SetLike S R] [SubringClass S R]

/-- A subring of an ordered ring is an ordered ring.
@isnad1 id=isordere.0h3v.s6.e2b6b29915b0 from=seed src=0 shape=e9abec18 vocab=7b9aaa7c
-/
instance toIsOrderedRing [IsOrderedRing R] (s : S) : IsOrderedRing s :=
  Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

/-- A subring of a strict ordered ring is a strict ordered ring.
@isnad1 id=isstrict.0h3v.s6.8a7d4da58d54 from=seed src=0 shape=e9abec18 vocab=d392a754
-/
instance toIsStrictOrderedRing [IsStrictOrderedRing R] (s : S) : IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

/-- The inclusion `S → R` of a subring, as an ordered ring homomorphism. -/
def orderedSubtype (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h

/--
@isnad1 id=eq.0h2v.s8.eb32d33fe2f4 from=seed src=0 shape=9f7032dc vocab=9187255f
-/
lemma orderedSubtype_coe (s : Subring R) : Subring.orderedSubtype s = Subring.subtype s := rfl

end Subring
