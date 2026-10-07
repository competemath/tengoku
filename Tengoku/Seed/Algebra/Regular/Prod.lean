/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Notation.Prod
public import Tengoku.Seed.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and `Prod`
-/

public section

variable {α R S : Type*}

section
variable [Mul R] [Mul S]

/--
@isnad1 id=iff.0h4v.s5.23bab068b41b from=seed src=0 shape=4930448e vocab=445e1bb4
-/
@[to_additive (attr := simp)]
theorem Prod.isLeftRegular_mk {a : R} {b : S} :
    IsLeftRegular (a, b) ↔ IsLeftRegular a ∧ IsLeftRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Prod.map_injective

/--
@isnad1 id=iff.0h4v.s5.005e6eebd156 from=seed src=0 shape=4930448e vocab=92c83a47
-/
@[to_additive (attr := simp)]
theorem Prod.isRightRegular_mk {a : R} {b : S} :
    IsRightRegular (a, b) ↔ IsRightRegular a ∧ IsRightRegular b :=
  have : Nonempty R := ⟨a⟩; have : Nonempty S := ⟨b⟩; Iff.symm <| Prod.map_injective |>.symm

/--
@isnad1 id=iff.0h4v.s5.1942be2fb368 from=seed src=0 shape=4930448e vocab=52fc019a
-/
@[to_additive (attr := simp)]
theorem Prod.isRegular_mk {a : R} {b : S} : IsRegular (a, b) ↔ IsRegular a ∧ IsRegular b := by
  simp [isRegular_iff, and_and_and_comm]

/--
@isnad1 id=isleftre.2h4v.s5.8caeb78f4eb5 from=seed src=0 shape=ab1cd48f vocab=445e1bb4
-/
@[to_additive]
theorem IsLeftRegular.prodMk {a : R} {b : S} (ha : IsLeftRegular a) (hb : IsLeftRegular b) :
    IsLeftRegular (a, b) := Prod.isLeftRegular_mk.2 ⟨ha, hb⟩

/--
@isnad1 id=isrightr.2h4v.s5.d4cdf0eee778 from=seed src=0 shape=ab1cd48f vocab=92c83a47
-/
@[to_additive]
theorem IsRightRegular.prodMk {a : R} {b : S} (ha : IsRightRegular a) (hb : IsRightRegular b) :
    IsRightRegular (a, b) := Prod.isRightRegular_mk.2 ⟨ha, hb⟩

/--
@isnad1 id=isregula.2h4v.s5.0aae91c7da20 from=seed src=0 shape=ab1cd48f vocab=52fc019a
-/
@[to_additive]
theorem IsRegular.prodMk {a : R} {b : S} (ha : IsRegular a) (hb : IsRegular b) :
    IsRegular (a, b) := Prod.isRegular_mk.2 ⟨ha, hb⟩

end

/--
@isnad1 id=iff.0h4v.s5.7c8b64b70c23 from=seed src=0 shape=a5b44faf vocab=6d4965d2
-/
@[simp]
theorem Prod.isSMulRegular_iff [SMul α R] [SMul α S] {r : α} [Nonempty R] [Nonempty S] :
    IsSMulRegular (R × S) r ↔ IsSMulRegular R r ∧ IsSMulRegular S r :=
  Prod.map_injective
