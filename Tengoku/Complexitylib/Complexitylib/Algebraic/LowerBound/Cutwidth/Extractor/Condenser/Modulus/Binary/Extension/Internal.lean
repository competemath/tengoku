/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial
public import Tengoku

/-!
# Flattening a binomial tower into one binary quotient

Polynomial composition multiplies the power-of-three exponents. Mathlib's
`AdjoinRoot.compAlgEquiv` then supplies the tower equivalence and its generator
laws, with only equality transports on the two defining polynomials.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem binaryModulus_comp_pow_three (s v : Nat) :
    (binaryModulus s).comp (Polynomial.X ^ (3 ^ v)) = binaryModulus (s + v) := by
  simp only [binaryModulus, Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.one_comp, ← pow_mul, Nat.pow_add]
  congr 2 <;> congr 1 <;> ring

theorem extensionModulus_monic (s v : Nat) : (extensionModulus s v).Monic :=
  binomialModulus_monic _ v

theorem root_extensionModulus_pow (s v : Nat) :
    AdjoinRoot.root (extensionModulus s v) ^ (3 ^ v) =
      AdjoinRoot.of (extensionModulus s v) (AdjoinRoot.root (binaryModulus s)) := by
  have vanishes := AdjoinRoot.mk_self (f := extensionModulus s v)
  change AdjoinRoot.mk (extensionModulus s v)
    (Polynomial.X ^ (3 ^ v) - Polynomial.C (AdjoinRoot.root (binaryModulus s))) = 0 at vanishes
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] using vanishes

end Algebraic.Cutwidth.Extractor.Internal
