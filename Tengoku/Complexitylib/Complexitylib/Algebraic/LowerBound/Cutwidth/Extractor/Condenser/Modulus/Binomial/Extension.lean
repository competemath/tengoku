/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Extension.Internal

/-!
# The binomial quotient supplies the next noncube coefficient

The adjoined root of `X^(3^s) - a` has norm `a`. If `a` is a noncube, norm
multiplicativity shows that the root is also a noncube. It therefore gives
another monic irreducible binomial of every power-of-three degree.

The norm computation reuses Mathlib's power-basis norm formula
`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` and its monic
`AdjoinRoot` power basis:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Norm/Basic.html.
The next irreducibility step uses the Kummer theorem documented in `Binomial`.
These are semantic algebraic facts about supplied data; no encoded field
representation, coefficient-selection algorithm, or runtime bound is asserted.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Odd degree makes the quotient root's norm equal to the supplied coefficient.
This identity does not require irreducibility.
@isnad1 id=eq.0h3v.s8.b83cca324ad6 from=translated src=- shape=e6583f9e vocab=a6ade270
-/
theorem norm_root_binomialModulus {F : Type*} [Field F] (a : F) (s : Nat) :
    Algebra.norm F (AdjoinRoot.root (binomialModulus a s)) = a :=
  Internal.norm_root_binomialModulus a s

/-- A cube root of the adjoined root would have norm a cube root of `a`.
@isnad1 id=ne.1h4v.s7.3775c9fdf4b8 from=translated src=- shape=609dbe5a vocab=8ab312ed
-/
theorem root_binomialModulus_noncube {F : Type*} [Field F] (a : F) (s : Nat)
    (noncube : ∀ b : F, b ^ 3 ≠ a) :
    ∀ b : AdjoinRoot (binomialModulus a s),
      b ^ 3 ≠ AdjoinRoot.root (binomialModulus a s) :=
  Internal.root_binomialModulus_noncube a s noncube

end Algebraic.Cutwidth.Extractor
