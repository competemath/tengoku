/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.MassProduction.LowDegree
public import Tengoku

/-!
# Polynomial support after Frobenius powers

In characteristic two, every exponent appearing in a `2^r`-th power is
divisible by `2^r`. Multiplication by a low-degree polynomial therefore
leaves the residue of each supported exponent bounded by that low degree.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2]

/-- Frobenius powers have support only at multiples of the power. -/
theorem dvdOfMemSupportPowTwo
    (polynomial : Polynomial K) (width exponent : Nat)
    (inSupport : exponent ∈ (polynomial ^ 2 ^ width).support) :
    2 ^ width ∣ exponent := by
  classical
  have nonzero := Polynomial.mem_support_iff.mp inSupport
  rw [← Polynomial.map_iterateFrobenius_expand 2 polynomial width,
    Polynomial.coeff_map, Polynomial.coeff_expand (by positivity)] at nonzero
  by_contra notDivisible
  simp only [ite_eq_right notDivisible, map_zero, ne_eq, not_true_eq_false] at nonzero

end Algebraic.MassProduction.HighRate
