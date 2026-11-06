/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
import Tengoku.Seed.Order.Filter.AtTopBot.Tendsto

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation estimates for logarithm and exponential series

This file proves lower bounds and divergence-to-infinity statements for the
integer valuations of the logarithm and exponential series terms.
-/

noncomputable section

universe u

open Filter WithZero
open scoped NNReal Filter WithZero

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Positive-degree exponential terms have positive integer valuation when
the input has valuation strictly bigger than one.
@isnad1 id=lt.4h5v.s8.69c9831c5b26 from=translated src=- shape=49f46732 vocab=6ccb533b
-/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_pos_of_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < (ofWithZeroValuation v).val x)
    (hn : n ≠ 0) :
    0 <
      (ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_factorial
      (v := v) (p := p) (n := n) x hnK hnval
  have hxge : (2 : ℤ) ≤ (ofWithZeroValuation v).val x := by
    omega
  have hnnonneg : (0 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hlin :
      (n : ℤ) * 2 ≤
        (n : ℤ) * (ofWithZeroValuation v).val x :=
    mul_le_mul_of_nonneg_left hxge hnnonneg
  have hden :
      (padicValNat p n.factorial : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast padicValNat_factorial_le (p := p) n
  have hnpos : (0 : ℤ) < (n : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [hterm]
  linarith

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
