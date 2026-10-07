/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Monoid.Submonoid
public import Tengoku.Seed.Algebra.Order.Ring.InjSurj
public import Tengoku.Seed.Algebra.Ring.Subsemiring.Defs
public import Tengoku.Seed.Order.Interval.Set.Defs
public import Tengoku.Seed.Tactic.FastInstance

/-!
# `Order`ed instances for `SubsemiringClass` and `Subsemiring`.
-/

@[expose] public section

namespace SubsemiringClass
variable {R S : Type*} [SetLike S R] (s : S)

/-- A subsemiring of an ordered semiring is an ordered semiring.
@isnad1 id=isordere.0h3v.s6.8bac28d4ef91 from=seed src=0 shape=613b611e vocab=a7c661ab
-/
instance toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] [SubsemiringClass S R] :
    IsOrderedRing s :=
  Function.Injective.isOrderedRing Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl

/-- A subsemiring of a strict ordered semiring is a strict ordered semiring.
@isnad1 id=isstrict.0h3v.s6.2a1020716736 from=seed src=0 shape=613b611e vocab=5789d4c0
-/
instance toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [SubsemiringClass S R] : IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing Subtype.val
    rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

end SubsemiringClass

namespace Subsemiring

variable {R : Type*}

/-- A subsemiring of an ordered semiring is an ordered semiring.
@isnad1 id=isordere.0h2v.s6.89127e7ef63f from=seed src=0 shape=7b0ce5ef vocab=c4f8ba33
-/
instance toIsOrderedRing [Semiring R] [PartialOrder R] [IsOrderedRing R] (s : Subsemiring R) :
    IsOrderedRing s :=
  SubsemiringClass.toIsOrderedRing _

/-- A subsemiring of a strict ordered semiring is a strict ordered semiring.
@isnad1 id=isstrict.0h2v.s6.1146a5ff6bc5 from=seed src=0 shape=7b0ce5ef vocab=005971a9
-/
instance toIsStrictOrderedRing [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    (s : Subsemiring R) : IsStrictOrderedRing s :=
  SubsemiringClass.toIsStrictOrderedRing _

section nonneg

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]

variable (R) in
/-- The set of nonnegative elements in an ordered semiring, as a subsemiring. -/
@[simps]
def nonneg : Subsemiring R where
  __ := AddSubmonoid.nonneg R
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one

/--
@isnad1 id=iff.0h2v.s5.bf4392b7375b from=seed src=0 shape=ea0a7987 vocab=d20a2a57
-/
@[simp] lemma mem_nonneg {x : R} : x ∈ nonneg R ↔ 0 ≤ x := .rfl

variable (R) in
/--
@isnad1 id=eq.0h1v.s5.3af94261c819 from=seed src=0 shape=fbb2e310 vocab=2f970a86
-/
@[simp]
theorem nonneg_toAddSubmonoid : (nonneg R).toAddSubmonoid = AddSubmonoid.nonneg R := rfl

end nonneg

end Subsemiring
