/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Tengoku

/-!
# Bounded functions
-/

public section

variable {α X : Type*} [Bornology X]

namespace Bornology
variable {x : X} {f : α → X}

@[expose, fun_prop] def IsBddFun (f : α → X) : Prop := IsBounded (.range f)

-- TODO: Move the `attribute [local push] Function.const_def` from `Mathlib.Order.ScottContinuity`
-- to an earlier file.
/--
@isnad1 id=isbddfun.0h3v.s4.c8d8ab34710d from=translated src=- shape=2ca1014d vocab=1d17cfca
-/
@[to_fun (attr := simp, fun_prop)]
protected lemma IsBddFun.const : IsBddFun (Function.const α x) := (Set.finite_range_const).isBounded

/--
@isnad1 id=isbddfun.0h2v.s4.8626577c943e from=translated src=- shape=bd2e3389 vocab=4233080e
-/
@[to_additive (attr := simp, fun_prop)]
protected lemma IsBddFun.one [One X] : IsBddFun (1 : α → X) := .const

/--
@isnad1 id=isbddfun.0h3v.s4.924d2e85f90b from=translated src=- shape=4c0451f3 vocab=1ab4c30c
-/
@[simp, fun_prop]
protected lemma IsBddFun.natCast [NatCast X] {n : ℕ} : IsBddFun (n : α → X) := .const

/--
@isnad1 id=isbddfun.0h3v.s5.3e1e1cd388e3 from=translated src=- shape=4aa8709e vocab=1dd8756b
-/
@[simp, fun_prop]
protected lemma IsBddFun.ofNat [NatCast X] {n : ℕ} [n.AtLeastTwo] : IsBddFun (ofNat(n) : α → X) :=
  .const

/--
@isnad1 id=isbddfun.0h3v.s4.cbf9dee58e56 from=translated src=- shape=4c0451f3 vocab=a49fcdb3
-/
@[simp, fun_prop]
protected lemma IsBddFun.intCast [IntCast X] {n : ℤ} : IsBddFun (n : α → X) := .const

/--
@isnad1 id=isbddfun.0h3v.s4.30456b42bbd4 from=translated src=- shape=b86edad9 vocab=f4fd434a
-/
@[fun_prop] lemma IsBddFun.of_finite [Finite α] : IsBddFun f := (Set.finite_range _).isBounded

end Bornology
