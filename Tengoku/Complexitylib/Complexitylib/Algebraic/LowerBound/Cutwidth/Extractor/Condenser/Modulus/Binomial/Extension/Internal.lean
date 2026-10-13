/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial

/-!
# The binomial root has the original coefficient as its norm

The power basis of the supplied binomial quotient computes the root norm.
Odd degree cancels the sign of the constant coefficient. Norm multiplicativity
then transfers the noncube property to the adjoined root.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

/--
@isnad1 id=eq.0h3v.s8.b83cca324ad6 from=translated src=- shape=e6583f9e vocab=a6ade270
-/
theorem norm_root_binomialModulus {F : Type*} [Field F] (a : F) (s : Nat) :
    Algebra.norm F (AdjoinRoot.root (binomialModulus a s)) = a := by
  have odd : Odd (3 ^ s) := (by decide : Odd 3).pow
  change Algebra.norm F (AdjoinRoot.powerBasis (binomialModulus_monic a s).ne_zero).gen = a
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    AdjoinRoot.minpoly_powerBasis_gen_of_monic (binomialModulus_monic a s),
    AdjoinRoot.powerBasis_dim, binomialModulus_natDegree, odd.neg_one_pow]
  simp [binomialModulus, Polynomial.coeff_X_pow]
  positivity

/--
@isnad1 id=ne.1h4v.s7.3775c9fdf4b8 from=translated src=- shape=609dbe5a vocab=8ab312ed
-/
theorem root_binomialModulus_noncube {F : Type*} [Field F] (a : F) (s : Nat)
    (noncube : ∀ b : F, b ^ 3 ≠ a) :
    ∀ b : AdjoinRoot (binomialModulus a s),
      b ^ 3 ≠ AdjoinRoot.root (binomialModulus a s) := by
  intro b cube
  apply noncube (Algebra.norm F b)
  rw [← map_pow, cube, norm_root_binomialModulus]

end Algebraic.Cutwidth.Extractor.Internal
