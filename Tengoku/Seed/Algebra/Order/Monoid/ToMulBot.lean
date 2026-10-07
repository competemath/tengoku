/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.GroupWithZero.Canonical
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.TypeTags
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.WithTop

/-!
Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/

@[expose] public section


universe u

variable {α : Type u}

namespace WithZero

variable [Add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _

/--
@isnad1 id=eq.0h1v.s7.80a1722ce07d from=seed src=0 shape=cef9506a vocab=4363903c
-/
@[simp]
theorem toMulBot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.5145a9f8a15e from=seed src=0 shape=4cbca02a vocab=454f733d
-/
@[simp]
theorem toMulBot_coe (x : Multiplicative α) :
    toMulBot ↑x = Multiplicative.ofAdd (↑x.toAdd : WithBot α) :=
  rfl

/--
@isnad1 id=eq.0h1v.s7.965bb30e8795 from=seed src=0 shape=807c3c39 vocab=a024b8bb
-/
@[simp]
theorem toMulBot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl

/--
@isnad1 id=eq.0h2v.s7.e8877a905904 from=seed src=0 shape=fb49b203 vocab=b3264084
-/
@[simp]
theorem toMulBot_coe_ofAdd (x : α) :
    toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl

variable [Preorder α] (a b : WithZero (Multiplicative α))

/--
@isnad1 id=strictmo.0h1v.s6.7fa5def7f90d from=seed src=0 shape=9f95d3dd vocab=11eb1472
-/
theorem toMulBot_strictMono : StrictMono (@toMulBot α _) := fun _ _ => id

/--
@isnad1 id=iff.0h3v.s7.401b85f63890 from=seed src=0 shape=89035a35 vocab=d15bda33
-/
@[simp]
theorem toMulBot_le : toMulBot a ≤ toMulBot b ↔ a ≤ b :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s7.2c2cc99ad379 from=seed src=0 shape=89035a35 vocab=71fbedde
-/
@[simp]
theorem toMulBot_lt : toMulBot a < toMulBot b ↔ a < b :=
  Iff.rfl

end WithZero
