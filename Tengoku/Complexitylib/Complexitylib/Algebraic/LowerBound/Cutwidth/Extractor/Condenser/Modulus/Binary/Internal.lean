/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Internal.Basic
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Internal.Irreducible

/-!
# Binary quotient size and the noncube root

The monic power basis gives the quotient cardinality. Cubing in the defining
polynomial passes from `M_s` to `M_(s+1)`. A cube root of the quotient root
would therefore have minimal polynomial degree larger than the quotient's
dimension, contradicting the finite-module degree bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem card_adjoinRoot_binaryModulus (s : Nat) :
    Nat.card (AdjoinRoot (binaryModulus s)) = 2 ^ (2 * 3 ^ s) := by
  let pb := AdjoinRoot.powerBasis (binaryModulus_monic s).ne_zero
  let : Module.Finite (ZMod 2) (AdjoinRoot (binaryModulus s)) := pb.finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    PowerBasis.finrank pb, AdjoinRoot.powerBasis_dim, binaryModulus_natDegree]

theorem binaryModulus_comp_cube (s : Nat) :
    (binaryModulus s).comp (Polynomial.X ^ 3) = binaryModulus (s + 1) := by
  simp only [binaryModulus, Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.one_comp, ← pow_mul]
  rw [Nat.pow_succ]
  congr 2 <;> congr 1 <;> ring

end Algebraic.Cutwidth.Extractor.Internal
