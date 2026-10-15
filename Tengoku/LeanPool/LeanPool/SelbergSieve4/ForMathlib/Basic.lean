/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Tengoku
/-!
# LeanPool.SelbergSieve4.ForMathlib.Basic
-/

@[expose] public section

namespace Aux

open BigOperators ArithmeticFunction
/- Lemmas in this file are singled out as suitable for addition to Mathlib with minor
modifications. -/

variable {R : Type*}

/--
@isnad1 id=eq.2h4v.s7.ddbe03c8edd9 from=translated src=- shape=b8df1f00 vocab=d0bb99a4
-/
theorem mult_lcm_eq_of_ne_zero [CommGroupWithZero R] (f : ArithmeticFunction R)
    (h_mult : f.IsMultiplicative) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [←h_mult.lcm_apply_mul_gcd_apply]
  field_simp

/--
@isnad1 id=eq.2h2v.s5.f1e2f2d127b6 from=translated src=- shape=52d19bd4 vocab=02fb114e
-/
theorem prod_factors_of_mult (f : ArithmeticFunction ℝ)
    (h_mult : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [←IsMultiplicative.map_prod_of_subset_primeFactors h_mult l _ Finset.Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hl]

end Aux
