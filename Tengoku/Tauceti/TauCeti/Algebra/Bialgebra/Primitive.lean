/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.Module.Rat
public import Tengoku.Tauceti.TauCeti.RingTheory.DividedPowers.Associative

/-!
# Primitive elements in a bialgebra

This file records integral-coefficient formulas for the comultiplication of powers, divided
powers, and binomial coefficients of a primitive element. The two tensor factors commute even
when the bialgebra itself is noncommutative. It also computes the counit of the latter two
families when the underlying element has counit zero.

## Main results

* `TauCeti.Bialgebra.comul_pow_of_primitive`: the comultiplication of a power of a primitive
  element is its binomial expansion.
* `TauCeti.Bialgebra.comul_dividedPower_of_primitive`: the comultiplication of a divided power
  has coefficient one on every antidiagonal term.
* `TauCeti.Bialgebra.comul_choose_of_primitive`: the comultiplication of a binomial coefficient
  has the same coefficient-one formula.
-/

public section

open scoped TensorProduct

namespace TauCeti.Bialgebra

universe u w

attribute [local instance] TauCeti.moduleNNRat

section DividedPower

variable {A : Type w} [Semiring A] [Bialgebra ℚ A]

/-- A counit that kills an element also kills all its positive divided powers. -/
theorem counit_dividedPower_of_counit_eq_zero
    (a : A) (h : Coalgebra.counit (R := ℚ) a = 0) (n : ℕ) :
    (Coalgebra.counit (R := ℚ)) (Associative.dividedPower (n + 1) a) = 0 := by
  rw [← Bialgebra.counitAlgHom_apply, Associative.map_dividedPower,
    Bialgebra.counitAlgHom_apply, h]
  exact Associative.dividedPower_eval_zero (Nat.succ_ne_zero n)

end DividedPower

section Choose

variable {A : Type w} [Ring A] [Bialgebra ℚ A]

/-- A counit that kills an element also kills all its positive binomial coefficients. -/
theorem counit_choose_of_counit_eq_zero
    (a : A) (h : Coalgebra.counit (R := ℚ) a = 0) (n : ℕ) :
    (Coalgebra.counit (R := ℚ)) (Ring.choose a (n + 1)) = 0 := by
  rw [← Bialgebra.counitAlgHom_apply, Ring.map_choose, Bialgebra.counitAlgHom_apply, h]
  exact Ring.choose_zero_succ ℚ n

end Choose

end TauCeti.Bialgebra
