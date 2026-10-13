/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Defs
public import Tengoku

/-!
# Degree and the base quadratic of the binary modulus family

The leading exponent is strictly larger than the two remaining exponents.
At exponent zero, the quadratic has no root in the two-element field.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

/--
@isnad1 id=monic.0h1v.s5.92361365754b from=translated src=- shape=f5b4d083 vocab=68304833
-/
theorem binaryModulus_monic (s : Nat) : (binaryModulus s).Monic := by
  have positive : 0 < 3 ^ s := by positivity
  have small : (Polynomial.X ^ (3 ^ s) + (1 : Polynomial (ZMod 2))).degree <
      ((2 * 3 ^ s : Nat) : WithBot Nat) := by
    rw [← Polynomial.C_1, Polynomial.degree_X_pow_add_C positive]
    exact_mod_cast (show 3 ^ s < 2 * 3 ^ s by lia)
  simpa only [binaryModulus, add_assoc] using Polynomial.monic_X_pow_add small

/--
@isnad1 id=eq.0h1v.s6.8ac26347500c from=translated src=- shape=ede5f45b vocab=33debace
-/
theorem binaryModulus_natDegree (s : Nat) : (binaryModulus s).natDegree = 2 * 3 ^ s := by
  have positive : 0 < 3 ^ s := by positivity
  rw [binaryModulus, add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow _
  · rw [Polynomial.natDegree_X_pow, ← Polynomial.C_1, Polynomial.natDegree_X_pow_add_C]
    lia

/--
@isnad1 id=irreduci.0h0v.s6.18a89bb4a6ed from=translated src=- shape=42598d2a vocab=0132e3fa
-/
theorem binaryModulus_zero_irreducible : Irreducible (binaryModulus 0) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [binaryModulus_natDegree]
  · intro x
    simp only [binaryModulus, pow_zero, mul_one, pow_one, Polynomial.IsRoot,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

end Algebraic.Cutwidth.Extractor.Internal
