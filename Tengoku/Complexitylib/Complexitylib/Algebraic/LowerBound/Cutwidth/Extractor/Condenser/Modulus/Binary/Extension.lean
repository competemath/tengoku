/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension.Internal

/-!
# A binomial extension is one larger binary quotient

Write `t` for the root of the binary modulus `M_s`. Adjoining `u` with
`u^(3^v) = t` gives the same binary algebra as the quotient by `M_(s+v)`.
The equivalence sends the larger binary root to `u`; its inverse sends an
embedded base polynomial `p(t)` to `p(u^(3^v))`. The polynomial image laws
identify coefficient packing and evaluation in these two representations.

The construction reuses Mathlib's `AdjoinRoot.compAlgEquiv`, with equality
transports on the supplied defining polynomials:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdjoinRoot.html.
Irreducibility uses the binary root's proved noncube property and the Kummer
result documented in `Binomial`. These are semantic algebraic identifications;
no runtime claim on abstract quotient objects or global field instances is added.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Substitution by a power of three stays within the explicit binary family.
@isnad1 id=eq.0h2v.s8.aba2bbb21400 from=translated src=- shape=4f5d09a3 vocab=0d20e63d
-/
theorem binaryModulus_comp_pow_three (s v : Nat) :
    (binaryModulus s).comp (Polynomial.X ^ (3 ^ v)) = binaryModulus (s + v) :=
  Internal.binaryModulus_comp_pow_three s v

/-- The extension modulus is monic, including its linear case at `v = 0`.
@isnad1 id=monic.0h2v.s6.309d90085264 from=translated src=- shape=32548949 vocab=daf45752
-/
theorem extensionModulus_monic (s v : Nat) : (extensionModulus s v).Monic :=
  Internal.extensionModulus_monic s v

/-- The defining extension relation identifies its generator power with the base root.
@isnad1 id=eq.0h2v.s10.501013bff30e from=translated src=- shape=0c30768f vocab=8f63d180
-/
theorem root_extensionModulus_pow (s v : Nat) :
    AdjoinRoot.root (extensionModulus s v) ^ (3 ^ v) =
      AdjoinRoot.of (extensionModulus s v) (AdjoinRoot.root (binaryModulus s)) :=
  Internal.root_extensionModulus_pow s v

end Algebraic.Cutwidth.Extractor
