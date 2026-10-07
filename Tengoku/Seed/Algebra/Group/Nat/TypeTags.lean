/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Nat.Defs
public import Tengoku.Seed.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about `Multiplicative ℕ`
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open Multiplicative

namespace Nat

/--
@isnad1 id=eq.0h2v.s6.a2db94eeefb9 from=seed src=0 shape=78d38ee2 vocab=3cab16c1
-/
lemma toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

/--
@isnad1 id=eq.0h2v.s6.9528c4d17f70 from=seed src=0 shape=07f8ada2 vocab=ddf2ed7f
-/
@[simp] lemma ofAdd_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_pow _ _).symm

end Nat
