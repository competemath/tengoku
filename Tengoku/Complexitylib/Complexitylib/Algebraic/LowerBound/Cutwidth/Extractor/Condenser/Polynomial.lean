/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
public import Tengoku
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Internal

/-!
# The concrete polynomial map underlying the linear GUV condenser

For `h = 2^r`, coordinate `i` is `(f^(h^i) mod E)(y)`. The defining iteration
reduces after each squaring, keeping its state degree below that of monic `E`.
For every seed the map is linear over `ZMod 2` in characteristic two.

This is the map of Guruswami, Umans, and Vadhan, *Unbalanced Expanders and
Randomness Extractors from Parvaresh--Vardy Codes* (2009), Section 3.1,
https://salil.seas.harvard.edu/sites/g/files/omnuum4266/files/salil/files/acm2009.pdf,
with the characteristic-power exponent from Cheraghchi, *Applications of
Derandomization Theory in Coding* (2010), Section 2.3.3,
https://arxiv.org/abs/1107.4709. The resulting strong linear lossless condenser
is an input to Chattopadhyay, Goodman, and Liao (2021), Lemma 4.7 and Section 5.
https://eccc.weizmann.ac.il/report/2021/075/

This module supplies the polynomial map, degree invariant, and linearity.
`Condenser.Expansion` and `Condenser.Lossless.Polynomial` prove finite expansion
and flat-source guarantees for a supplied irreducible modulus. The explicit
binary field family is in `Condenser.Modulus.Binary`; its extension equivalence
justifies the coefficient packing. `Condenser.Encoding.Correctness` proves that
the uniform bitstring evaluator computes this map for those explicit fields.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Modular iteration has the power-and-remainder formula used by GUV.
@isnad1 id=eq.0h4v.s6.e5fa200fc11e from=translated src=- shape=7c00f609 vocab=94b07d1f
-/
theorem modularFrobenius_eq_pow_modByMonic {F : Type*} [CommRing F]
    (E f : Polynomial F) (j : Nat) :
    modularFrobenius E j f = f ^ (2 ^ j) %ₘ E :=
  Internal.modularFrobenius_eq_pow_modByMonic E f j

/-- Every stored polynomial has degree below that of the supplied monic modulus.
@isnad1 id=lt.1h4v.s6.c343787874b2 from=translated src=- shape=0017f91a vocab=9d7e08aa
-/
theorem modularFrobenius_degree_lt {F : Type*} [CommRing F] [Nontrivial F]
    (E f : Polynomial F) (monic : E.Monic) (j : Nat) :
    (modularFrobenius E j f).degree < E.degree :=
  Internal.modularFrobenius_degree_lt E f monic j

/-- Coordinate `i` agrees with `(f^(h^i) mod E)(y)` for `h = 2^r`.
@isnad1 id=eq.0h7v.s7.efe023b04848 from=translated src=- shape=156d38a5 vocab=15d2d68f
-/
theorem polynomialCondenser_apply {F : Type*} [CommRing F]
    (E f : Polynomial F) (r m : Nat) (y : F) (i : Fin m) :
    polynomialCondenser E r m f y i = (f ^ ((2 ^ r) ^ i.val) %ₘ E).eval y :=
  Internal.polynomialCondenser_apply E f r m y i

/-- For the bounded-degree sources in the construction, coordinate zero is
the source polynomial evaluated at the seed.
@isnad1 id=eq.2h6v.s7.e0ca649ecb62 from=translated src=- shape=ba3764e3 vocab=b0f8c576
-/
theorem polynomialCondenser_zero_coordinate {F : Type*} [CommRing F] [Nontrivial F]
    (E f : Polynomial F) (monic : E.Monic) (source : f.degree < E.degree)
    (r m : Nat) (y : F) : polynomialCondenser E r (m + 1) f y 0 = f.eval y :=
  Internal.polynomialCondenser_zero_coordinate E f monic source r m y

/-- The zero source gives the zero output for every seed.
@isnad1 id=eq.0h5v.s6.a782d45d8b33 from=translated src=- shape=aea79716 vocab=75cdac2a
-/
theorem polynomialCondenser_zero {F : Type*} [CommRing F]
    (E : Polynomial F) (r m : Nat) (y : F) : polynomialCondenser E r m 0 y = 0 :=
  Internal.polynomialCondenser_zero E r m y

/-- In characteristic two, the map preserves source addition for every seed.
@isnad1 id=eq.0h7v.s7.03e93c407401 from=translated src=- shape=46e5abff vocab=c4d19622
-/
theorem polynomialCondenser_add {F : Type*} [CommRing F] [CharP F 2]
    (E f g : Polynomial F) (r m : Nat) (y : F) :
    polynomialCondenser E r m (f + g) y =
      polynomialCondenser E r m f y + polynomialCondenser E r m g y :=
  Internal.polynomialCondenser_add E f g r m y

/-- Source additivity gives actual `ZMod 2` scalar linearity. The scalar action
on polynomials is coefficientwise, and that on the output is coordinatewise.
@isnad1 id=eq.0h7v.s8.4b2ca3d0184b from=translated src=- shape=171a2def vocab=c4ef25f1
-/
theorem polynomialCondenser_smul {F : Type*} [CommRing F] [CharP F 2]
    [Module (ZMod 2) F] (E f : Polynomial F) (r m : Nat) (y : F) (c : ZMod 2) :
    polynomialCondenser E r m (c • f) y = c • polynomialCondenser E r m f y :=
  Internal.polynomialCondenser_smul E f r m y c

end Algebraic.Cutwidth.Extractor
