/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.Arithmetic
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
import Tengoku.Seed.Data.Int.WithZero
import Tengoku.Seed.RingTheory.Valuation.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer valuations induced by `ℤᵐ⁰`-valued valuations

This file constructs the sign-normalized integer valuation on field units and
proves the elementary formulas for powers and natural-number denominators.
-/

noncomputable section

universe u

open WithZero
open scoped NNReal WithZero

namespace LocalFieldTheory.DiscreteValuationField

namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The integer-valued multiplicative valuation attached to a
`ℤᵐ⁰`-valued field valuation.  The sign convention is normalized so that a
uniformizer of value `exp (-1)` has integer value `1`.-/
noncomputable def ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    MultiplicativeIntegerValuation Kˣ where
  val x := -WithZero.log (v (x : K))
  map_one := by
    change -WithZero.log (v 1) = 0
    rw [v.map_one, WithZero.log_one, neg_zero]
  map_mul x y := by
    have hx : v (x : K) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 x.ne_zero
    have hy : v (y : K) ≠ 0 :=
      (_root_.Valuation.ne_zero_iff v).2 y.ne_zero
    change
      -WithZero.log (v ((x : K) * (y : K))) =
        -WithZero.log (v (x : K)) + -WithZero.log (v (y : K))
    rw [v.map_mul, WithZero.log_mul hx hy]
    ring

/-- Establishes the identity `(ofWithZeroValuation v).val x = -WithZero.log (v (x : K))`.-/
@[simp] theorem ofWithZeroValuation_val
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ) :
    (ofWithZeroValuation v).val x = -WithZero.log (v (x : K)) :=
  rfl

/--
`ofWithZeroValuation_val_eq_of_valuation_eq_exp` satisfies the negation formula
`(ofWithZeroValuation v).val x = n`.-/
theorem ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ) {n : ℤ}
    (hx : v (x : K) = WithZero.exp (-n)) :
    (ofWithZeroValuation v).val x = n := by
  rw [ofWithZeroValuation_val, hx, WithZero.log_exp]
  ring

/-- Natural-number denominator form of the attached integer valuation.

This is the denominator input for the logarithm-series term
`x^n / n` in the field-unit logarithm theorem.-/
theorem ofWithZeroValuation_val_natCast
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (hnK : (n : K) ≠ 0)
    (hnval : v (n : K) = WithZero.exp (-(padicValNat p n : ℤ))) :
    (ofWithZeroValuation v).val (Units.mk0 (n : K) hnK) =
      (padicValNat p n : ℤ) :=
  ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg
    v (Units.mk0 (n : K) hnK) (by simpa using hnval)

/-- Valuation of the exponential-series term `x^n / n!`, assuming the
factorial denominator has the expected `p`-adic value.-/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ))) :
    (ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) =
      (n : ℤ) * (ofWithZeroValuation v).val x -
        (padicValNat p n.factorial : ℤ) := by
  rw [(ofWithZeroValuation v).val_div, (ofWithZeroValuation v).val_pow,
    ofWithZeroValuation_val_natCast v hnK hnval]

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
