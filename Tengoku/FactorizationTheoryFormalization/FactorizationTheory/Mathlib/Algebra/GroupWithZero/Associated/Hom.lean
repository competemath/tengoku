/-
Copyright (c) 2026 Arav Paladiya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arav Paladiya
-/
module

public import Tengoku.Seed.Algebra.GroupWithZero.Associated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maps on associate classes

A monoid homomorphism between commutative monoids descends to their associate classes.
-/

public section

assert_not_exists IsOrderedMonoid Multiset Ring

variable {M N P F : Type*}

namespace Associates

variable [CommMonoid M] [CommMonoid N]
variable [FunLike F M N] [MonoidHomClass F M N]

/-- The map on associate classes induced by a monoid homomorphism.-/
def map (f : F) : Associates M →* Associates N where
  toFun := Quotient.map f fun _ _ h ↦ h.map f
  map_one' := Quotient.sound (Associated.of_eq (map_one f))
  map_mul' x y := by
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y => exact Quotient.sound (Associated.of_eq (map_mul f x y))

/--
@isnad1 id=eq.0h5v.s7.1a91bfacd8fa from=translated src=- shape=8354ba08 vocab=7a8a9e33
-/
@[simp]
theorem map_mk (f : F) (x : M) : map f (Associates.mk x) = Associates.mk (f x) := by
  rfl

variable [CommMonoid P]

/--
@isnad1 id=eq.0h5v.s8.0b6c8aaf4c33 from=translated src=- shape=dbba98ab vocab=bf0f1a66
-/
@[simp]
theorem map_comp (f : M →* N) (g : N →* P) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  induction x using Quotient.inductionOn with
  | _ x => rfl

/--
@isnad1 id=eq.0h1v.s7.9e2704a4d218 from=translated src=- shape=977cf3a5 vocab=2fe0d144
-/
@[simp]
theorem map_id : map (MonoidHom.id M) = MonoidHom.id (Associates M) := by
  ext x
  induction x using Quotient.inductionOn with
  | _ x => rfl

end Associates
