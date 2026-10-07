/-
Copyright (c) 2024 Raghuram Sundararajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raghuram Sundararajan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Ring.Defs
public import Tengoku.Seed.Algebra.Group.Ext

/-!
# Extensionality lemmas for rings and similar structures

In this file we prove extensionality lemmas for the ring-like structures defined in
`Mathlib/Algebra/Ring/Defs.lean`, ranging from `NonUnitalNonAssocSemiring` to `CommRing`. These
extensionality lemmas take the form of asserting that two algebraic structures on a type are equal
whenever the addition and multiplication defined by them are both the same.

## Implementation details

We follow `Mathlib/Algebra/Group/Ext.lean` in using the term `(letI := i; HMul.hMul : R → R → R)` to
refer to the multiplication specified by a typeclass instance `i` on a type `R` (and similarly for
addition). We abbreviate these using some local notations.

Since `Mathlib/Algebra/Group/Ext.lean` proved several injectivity lemmas, we do so as well — even if
sometimes we don't need them to prove extensionality.

## Tags
semiring, ring, extensionality
-/

public section

local macro:max "local_hAdd[" type:term ", " inst:term "]" : term =>
  `(term| (letI := $inst; HAdd.hAdd : $type → $type → $type))
local macro:max "local_hMul[" type:term ", " inst:term "]" : term =>
  `(term| (letI := $inst; HMul.hMul : $type → $type → $type))

universe u

variable {R : Type u}

/-! ### Distrib -/
namespace Distrib

/--
@isnad1 id=eq.2h3v.s5.8a52baeea2e9 from=seed src=0 shape=af00b9c8 vocab=f4c62258
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Distrib R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `add` and `mul` functions and properties.
  rcases inst₁ with @⟨⟨⟩, ⟨⟩⟩
  rcases inst₂ with @⟨⟨⟩, ⟨⟩⟩
  -- Prove equality of parts using function extensionality.
  congr

end Distrib

/-! ### NonUnitalNonAssocSemiring -/
namespace NonUnitalNonAssocSemiring

/--
@isnad1 id=eq.2h3v.s6.8c8dfd94d799 from=seed src=0 shape=af00b9c8 vocab=af7bc523
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `AddMonoid` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩
  rcases inst₂ with @⟨_, ⟨⟩⟩
  -- Prove equality of parts using already-proved extensionality lemmas.
  congr; ext : 1; assumption

/--
@isnad1 id=injectiv.0h1v.s3.c8c4bbbd42af from=seed src=0 shape=fc766b23 vocab=c6471d71
-/
theorem toDistrib_injective : Function.Injective (@toDistrib R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocSemiring

/-! ### NonUnitalSemiring -/
namespace NonUnitalSemiring

/--
@isnad1 id=injectiv.0h1v.s3.5b190858dcfe from=seed src=0 shape=fc766b23 vocab=42534130
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
@isnad1 id=eq.2h3v.s6.25901d5d5511 from=seed src=0 shape=af00b9c8 vocab=4ee88921
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalSemiring

/-! ### NonAssocSemiring and its ancestors

This section also includes results for `AddMonoidWithOne`, `AddCommMonoidWithOne`, etc.
as these are considered implementation detail of the ring classes.
TODO consider relocating these lemmas.
-/
/--
@isnad1 id=eq.2h3v.s5.bfc16ce358b5 from=seed src=0 shape=cef77652 vocab=bab69a46
-/
@[ext] theorem AddMonoidWithOne.ext ⦃inst₁ inst₂ : AddMonoidWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one : R)) :
    inst₁ = inst₂ := by
  have h_monoid : inst₁.toAddMonoid = inst₂.toAddMonoid := by ext : 1; exact h_add
  have h_zero' : inst₁.toZero = inst₂.toZero := congrArg (·.toZero) h_monoid
  have h_one' : inst₁.toOne = inst₂.toOne :=
    congrArg One.mk h_one
  have h_natCast : inst₁.toNatCast.natCast = inst₂.toNatCast.natCast := by
    funext n; induction n with
    | zero => rewrite [inst₁.natCast_zero, inst₂.natCast_zero]
              exact congrArg (@Zero.zero R) h_zero'
    | succ n h => rw [inst₁.natCast_succ, inst₂.natCast_succ, h_add]
                  exact congrArg₂ _ h h_one
  rcases inst₁ with @⟨⟨⟩⟩; rcases inst₂ with @⟨⟨⟩⟩
  congr

/--
@isnad1 id=injectiv.0h1v.s3.28feedc5adbd from=seed src=0 shape=fc766b23 vocab=b331f9fd
-/
theorem AddCommMonoidWithOne.toAddMonoidWithOne_injective :
    Function.Injective (@AddCommMonoidWithOne.toAddMonoidWithOne R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
@isnad1 id=eq.2h3v.s6.773488e3dcb2 from=seed src=0 shape=cef77652 vocab=912b99c9
-/
@[ext] theorem AddCommMonoidWithOne.ext ⦃inst₁ inst₂ : AddCommMonoidWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one : R)) :
    inst₁ = inst₂ :=
  AddCommMonoidWithOne.toAddMonoidWithOne_injective <|
    AddMonoidWithOne.ext h_add h_one

namespace NonAssocSemiring

/-! The best place to prove that the `NatCast` is determined by the other operations is probably in
an extensionality lemma for `AddMonoidWithOne`, in which case we may as well do the typeclasses
defined in `Mathlib/Algebra/GroupWithZero/Defs.lean` as well. -/
/--
@isnad1 id=eq.2h3v.s6.c217265cf037 from=seed src=0 shape=af00b9c8 vocab=4330860e
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have h : inst₁.toNonUnitalNonAssocSemiring = inst₂.toNonUnitalNonAssocSemiring := by
    ext : 1 <;> assumption
  have h_zero : (inst₁.toMulZeroClass).toZero.zero = (inst₂.toMulZeroClass).toZero.zero :=
    congrArg (fun inst => (inst.toMulZeroClass).toZero.zero) h
  have h_one' : (inst₁.toMulZeroOneClass).toMulOneClass.toOne
                = (inst₂.toMulZeroOneClass).toMulOneClass.toOne := by
    congr 2; ext : 1; exact h_mul
  have h_one : (inst₁.toMulZeroOneClass).toMulOneClass.toOne.one
               = (inst₂.toMulZeroOneClass).toMulOneClass.toOne.one :=
    congrArg (@One.one R) h_one'
  have : inst₁.toAddCommMonoidWithOne = inst₂.toAddCommMonoidWithOne := by
    ext : 1 <;> assumption
  have : inst₁.toNatCast = inst₂.toNatCast :=
    congrArg (·.toNatCast) this
  -- Split into `NonUnitalNonAssocSemiring`, `One` and `natCast` instances.
  cases inst₁; cases inst₂
  congr

/--
@isnad1 id=injectiv.0h1v.s3.b42c23c36f92 from=seed src=0 shape=fc766b23 vocab=cafa68f7
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ _
  ext <;> congr

end NonAssocSemiring

/-! ### NonUnitalNonAssocRing -/
namespace NonUnitalNonAssocRing

/--
@isnad1 id=eq.2h3v.s6.8fc9a1b59905 from=seed src=0 shape=af00b9c8 vocab=10af9691
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Split into `AddCommGroup` instance, `mul` function and properties.
  rcases inst₁ with @⟨_, ⟨⟩⟩; rcases inst₂ with @⟨_, ⟨⟩⟩
  congr; (ext : 1; assumption)

/--
@isnad1 id=injectiv.0h1v.s3.27b5e8cec130 from=seed src=0 shape=fc766b23 vocab=71795f0e
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end NonUnitalNonAssocRing

/-! ### NonUnitalRing -/
namespace NonUnitalRing

/--
@isnad1 id=eq.2h3v.s6.ee3db0d820ab from=seed src=0 shape=af00b9c8 vocab=c0d5a2dc
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr

/--
@isnad1 id=injectiv.0h1v.s3.29bbf0400022 from=seed src=0 shape=fc766b23 vocab=80961092
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
@isnad1 id=injectiv.0h1v.s3.5190332958b7 from=seed src=0 shape=fc766b23 vocab=3f4abb72
-/
theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

end NonUnitalRing

/-! ### NonAssocRing and its ancestors

This section also includes results for `AddGroupWithOne`, `AddCommGroupWithOne`, etc.
as these are considered implementation detail of the ring classes.
TODO consider relocating these lemmas. -/
/--
@isnad1 id=eq.2h3v.s6.a12f75025620 from=seed src=0 shape=cef77652 vocab=b0ce8b46
-/
@[ext] theorem AddGroupWithOne.ext ⦃inst₁ inst₂ : AddGroupWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one)) :
    inst₁ = inst₂ := by
  have : inst₁.toAddMonoidWithOne = inst₂.toAddMonoidWithOne :=
    AddMonoidWithOne.ext h_add h_one
  have : inst₁.toNatCast = inst₂.toNatCast := congrArg (·.toNatCast) this
  have h_group : inst₁.toAddGroup = inst₂.toAddGroup := by ext : 1; exact h_add
  -- Extract equality of necessary substructures from h_group
  injection h_group with h_group; injection h_group
  have : inst₁.toIntCast.intCast = inst₂.toIntCast.intCast := by
    funext n; cases n with
    | ofNat n => rewrite [Int.ofNat_eq_natCast, inst₁.intCast_ofNat, inst₂.intCast_ofNat]; congr
    | negSucc n => rewrite [inst₁.intCast_negSucc, inst₂.intCast_negSucc]; congr
  rcases inst₁ with @⟨⟨⟩⟩; rcases inst₂ with @⟨⟨⟩⟩
  congr

/--
@isnad1 id=eq.2h3v.s6.ccc2d1bba9b7 from=seed src=0 shape=cef77652 vocab=1e2029e4
-/
@[ext] theorem AddCommGroupWithOne.ext ⦃inst₁ inst₂ : AddCommGroupWithOne R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_one : (letI := inst₁; One.one : R) = (letI := inst₂; One.one)) :
    inst₁ = inst₂ := by
  have : inst₁.toAddCommGroup = inst₂.toAddCommGroup :=
    AddCommGroup.ext h_add
  have : inst₁.toAddGroupWithOne = inst₂.toAddGroupWithOne :=
    AddGroupWithOne.ext h_add h_one
  injection this with _ h_addMonoidWithOne; injection h_addMonoidWithOne
  cases inst₁; cases inst₂
  congr

namespace NonAssocRing

/--
@isnad1 id=eq.2h3v.s6.bbc852090a39 from=seed src=0 shape=af00b9c8 vocab=e64b1f37
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonAssocRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  have h₁ : inst₁.toNonUnitalNonAssocRing = inst₂.toNonUnitalNonAssocRing := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  -- Mathematically non-trivial fact: `intCast` is determined by the rest.
  have h₃ : inst₁.toAddCommGroupWithOne = inst₂.toAddCommGroupWithOne :=
    AddCommGroupWithOne.ext h_add (congrArg (·.toOne.one) h₂)
  cases inst₁; cases inst₂
  congr <;> solve | injection h₁ | injection h₂ | injection h₃

/--
@isnad1 id=injectiv.0h1v.s3.0065fa2eed79 from=seed src=0 shape=fc766b23 vocab=43d6ed91
-/
theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
@isnad1 id=injectiv.0h1v.s3.89aa226c3d48 from=seed src=0 shape=fc766b23 vocab=f70228d8
-/
theorem toNonUnitalNonAssocring_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  intro _ _ _
  ext <;> congr

end NonAssocRing

/-! ### Semiring -/
namespace Semiring

/--
@isnad1 id=eq.2h3v.s6.db71662735c4 from=seed src=0 shape=af00b9c8 vocab=f5fe30e7
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Semiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₀ : inst₁.toAddCommMonoid = inst₂.toAddCommMonoid := by
    ext : 1 <;> assumption
  have h₁ : inst₁.toNonUnitalSemiring = inst₂.toNonUnitalSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocSemiring = inst₂.toNonAssocSemiring := by
    ext : 1 <;> assumption
  have h₃ : (inst₁.toMonoidWithZero).toMonoid = (inst₂.toMonoidWithZero).toMonoid := by
    ext : 1; exact h_mul
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₁ | injection h₂

/--
@isnad1 id=injectiv.0h1v.s3.f0ac5aa1b77a from=seed src=0 shape=fc766b23 vocab=383e15cb
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
@isnad1 id=injectiv.0h1v.s3.36d0b43f7327 from=seed src=0 shape=fc766b23 vocab=0aa1441d
-/
theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Semiring

/-! ### Ring -/
namespace Ring

/--
@isnad1 id=eq.2h3v.s6.98ab08dcac5b from=seed src=0 shape=af00b9c8 vocab=309b5614
-/
@[ext] theorem ext ⦃inst₁ inst₂ : Ring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ := by
  -- Show that enough substructures are equal.
  have h₁ : inst₁.toSemiring = inst₂.toSemiring := by
    ext : 1 <;> assumption
  have h₂ : inst₁.toNonAssocRing = inst₂.toNonAssocRing := by
    ext : 1 <;> assumption
  /- We prove that the `SubNegMonoid`s are equal because they are one
  field away from `Sub` and `Neg`, enabling use of `injection`. -/
  have h₃ : (inst₁.toAddCommGroup).toAddGroup.toSubNegMonoid
            = (inst₂.toAddCommGroup).toAddGroup.toSubNegMonoid :=
    congrArg (@AddGroup.toSubNegMonoid R) <| by ext : 1; exact h_add
  -- Split into fields and prove they are equal using the above.
  cases inst₁; cases inst₂
  congr <;> solve | injection h₂ | injection h₃

/--
@isnad1 id=injectiv.0h1v.s3.2c3962db5dcd from=seed src=0 shape=fc766b23 vocab=ef1ae346
-/
theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
@isnad1 id=injectiv.0h1v.s3.a6f2d6781153 from=seed src=0 shape=fc766b23 vocab=1b4652c4
-/
theorem toNonAssocRing_injective :
    Function.Injective (@toNonAssocRing R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

/--
@isnad1 id=injectiv.0h1v.s3.f2af88cd2183 from=seed src=0 shape=fc766b23 vocab=b08350ae
-/
theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

end Ring

/-! ### NonUnitalNonAssocCommSemiring -/
namespace NonUnitalNonAssocCommSemiring

/--
@isnad1 id=injectiv.0h1v.s3.b00f29d10392 from=seed src=0 shape=fc766b23 vocab=85754437
-/
theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
@isnad1 id=eq.2h3v.s6.9a7026a4179c from=seed src=0 shape=af00b9c8 vocab=760cd164
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocCommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocSemiring_injective <|
    NonUnitalNonAssocSemiring.ext h_add h_mul

end NonUnitalNonAssocCommSemiring

/-! ### NonUnitalCommSemiring -/
namespace NonUnitalCommSemiring

/--
@isnad1 id=injectiv.0h1v.s3.0e7c4efa44fa from=seed src=0 shape=fc766b23 vocab=ecbc614a
-/
theorem toNonUnitalSemiring_injective :
    Function.Injective (@toNonUnitalSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
@isnad1 id=eq.2h3v.s6.1fa6babbe727 from=seed src=0 shape=af00b9c8 vocab=d4878312
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalCommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalSemiring_injective <|
    NonUnitalSemiring.ext h_add h_mul

end NonUnitalCommSemiring

-- At present, there is no `NonAssocCommSemiring` in Mathlib.

/-! ### NonUnitalNonAssocCommRing -/
namespace NonUnitalNonAssocCommRing

/--
@isnad1 id=injectiv.0h1v.s3.5ee2782d722d from=seed src=0 shape=fc766b23 vocab=f21f5b2e
-/
theorem toNonUnitalNonAssocRing_injective :
    Function.Injective (@toNonUnitalNonAssocRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
@isnad1 id=eq.2h3v.s6.fa2145af07d6 from=seed src=0 shape=af00b9c8 vocab=21f983a5
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocCommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalNonAssocRing_injective <|
    NonUnitalNonAssocRing.ext h_add h_mul

end NonUnitalNonAssocCommRing

/-! ### NonUnitalCommRing -/
namespace NonUnitalCommRing

/--
@isnad1 id=injectiv.0h1v.s3.a54f6f40531d from=seed src=0 shape=fc766b23 vocab=c7326d62
-/
theorem toNonUnitalRing_injective :
    Function.Injective (@toNonUnitalRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
@isnad1 id=eq.2h3v.s6.54bb93bfccb8 from=seed src=0 shape=af00b9c8 vocab=a1cb5d64
-/
@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalCommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toNonUnitalRing_injective <|
    NonUnitalRing.ext h_add h_mul

end NonUnitalCommRing

-- At present, there is no `NonAssocCommRing` in Mathlib.

/-! ### CommSemiring -/
namespace CommSemiring

/--
@isnad1 id=injectiv.0h1v.s3.0eaab67f6d5b from=seed src=0 shape=fc766b23 vocab=15b8f210
-/
theorem toSemiring_injective :
    Function.Injective (@toSemiring R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
@isnad1 id=eq.2h3v.s6.2c3f1244dd7d from=seed src=0 shape=af00b9c8 vocab=0047e306
-/
@[ext] theorem ext ⦃inst₁ inst₂ : CommSemiring R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toSemiring_injective <|
    Semiring.ext h_add h_mul

end CommSemiring

/-! ### CommRing -/
namespace CommRing

/--
@isnad1 id=injectiv.0h1v.s3.c5082808de35 from=seed src=0 shape=fc766b23 vocab=7fd42721
-/
theorem toRing_injective : Function.Injective (@toRing R) := by
  rintro ⟨⟩ ⟨⟩ _; congr

/--
@isnad1 id=eq.2h3v.s6.efe44f656c7e from=seed src=0 shape=af00b9c8 vocab=7bb0ab33
-/
@[ext] theorem ext ⦃inst₁ inst₂ : CommRing R⦄
    (h_add : local_hAdd[R, inst₁] = local_hAdd[R, inst₂])
    (h_mul : local_hMul[R, inst₁] = local_hMul[R, inst₂]) :
    inst₁ = inst₂ :=
  toRing_injective <| Ring.ext h_add h_mul

end CommRing
