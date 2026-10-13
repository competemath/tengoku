/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
public import Tengoku

/-!
# Modular iteration and source linearity of the polynomial condenser map

The induction reduces after each squaring, so the degree bound is independent
of the potentially exponential exponent. Characteristic two makes each
squaring additive; remaindering and evaluation preserve that additivity.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor.Internal

/--
@isnad1 id=eq.0h4v.s6.e5fa200fc11e from=translated src=- shape=7c00f609 vocab=94b07d1f
-/
theorem modularFrobenius_eq_pow_modByMonic {F : Type*} [CommRing F]
    (E f : Polynomial F) (j : Nat) :
    modularFrobenius E j f = f ^ (2 ^ j) %ₘ E := by
  induction j with
  | zero => simp [modularFrobenius]
  | succ j ih =>
      rw [modularFrobenius, ih, show 2 ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul]
      simpa only [pow_two] using
        (Polynomial.mul_modByMonic (f ^ (2 ^ j)) (f ^ (2 ^ j)) E).symm

/--
@isnad1 id=lt.1h4v.s6.c343787874b2 from=translated src=- shape=0017f91a vocab=9d7e08aa
-/
theorem modularFrobenius_degree_lt {F : Type*} [CommRing F] [Nontrivial F]
    (E f : Polynomial F) (monic : E.Monic) (j : Nat) :
    (modularFrobenius E j f).degree < E.degree := by
  rw [modularFrobenius_eq_pow_modByMonic]
  exact Polynomial.degree_modByMonic_lt _ monic

/--
@isnad1 id=eq.0h3v.s6.fb4f6208d25a from=translated src=- shape=06605404 vocab=888c8dfc
-/
theorem modularFrobenius_zero {F : Type*} [CommRing F]
    (E : Polynomial F) (j : Nat) : modularFrobenius E j 0 = 0 := by
  induction j with
  | zero => simp [modularFrobenius]
  | succ j ih => simp [modularFrobenius, ih]

/--
@isnad1 id=eq.0h5v.s7.88b30b4f375d from=translated src=- shape=ae0b892c vocab=b720bc17
-/
theorem modularFrobenius_add {F : Type*} [CommRing F] [CharP F 2]
    (E f g : Polynomial F) (j : Nat) :
    modularFrobenius E j (f + g) = modularFrobenius E j f + modularFrobenius E j g := by
  induction j with
  | zero => exact Polynomial.add_modByMonic f g
  | succ j ih =>
      simp only [modularFrobenius, ih, add_pow_char, Polynomial.add_modByMonic]

/--
@isnad1 id=eq.0h7v.s7.efe023b04848 from=translated src=- shape=156d38a5 vocab=15d2d68f
-/
theorem polynomialCondenser_apply {F : Type*} [CommRing F]
    (E f : Polynomial F) (r m : Nat) (y : F) (i : Fin m) :
    polynomialCondenser E r m f y i = (f ^ ((2 ^ r) ^ i.val) %ₘ E).eval y := by
  simp only [polynomialCondenser, modularFrobenius_eq_pow_modByMonic, pow_mul]

/--
@isnad1 id=eq.2h6v.s7.e0ca649ecb62 from=translated src=- shape=ba3764e3 vocab=b0f8c576
-/
theorem polynomialCondenser_zero_coordinate {F : Type*} [CommRing F] [Nontrivial F]
    (E f : Polynomial F) (monic : E.Monic) (source : f.degree < E.degree)
    (r m : Nat) (y : F) : polynomialCondenser E r (m + 1) f y 0 = f.eval y := by
  simp only [polynomialCondenser, Fin.val_zero, Nat.mul_zero, modularFrobenius]
  rw [(Polynomial.modByMonic_eq_self_iff monic).mpr source]

/--
@isnad1 id=eq.0h5v.s6.a782d45d8b33 from=translated src=- shape=aea79716 vocab=75cdac2a
-/
theorem polynomialCondenser_zero {F : Type*} [CommRing F]
    (E : Polynomial F) (r m : Nat) (y : F) : polynomialCondenser E r m 0 y = 0 := by
  funext i
  simp only [polynomialCondenser, modularFrobenius_zero, Polynomial.eval_zero, Pi.zero_apply]

/--
@isnad1 id=eq.0h7v.s7.03e93c407401 from=translated src=- shape=46e5abff vocab=c4d19622
-/
theorem polynomialCondenser_add {F : Type*} [CommRing F] [CharP F 2]
    (E f g : Polynomial F) (r m : Nat) (y : F) :
    polynomialCondenser E r m (f + g) y =
      polynomialCondenser E r m f y + polynomialCondenser E r m g y := by
  funext i
  simp only [polynomialCondenser, modularFrobenius_add, Polynomial.eval_add, Pi.add_apply]

/--
@isnad1 id=eq.0h7v.s8.4b2ca3d0184b from=translated src=- shape=171a2def vocab=c4ef25f1
-/
theorem polynomialCondenser_smul {F : Type*} [CommRing F] [CharP F 2]
    [Module (ZMod 2) F] (E f : Polynomial F) (r m : Nat) (y : F) (c : ZMod 2) :
    polynomialCondenser E r m (c • f) y = c • polynomialCondenser E r m f y := by
  let map : Polynomial F →+ (Fin m → F) :=
    { toFun := fun g => polynomialCondenser E r m g y
      map_zero' := polynomialCondenser_zero E r m y
      map_add' := fun g h => polynomialCondenser_add E g h r m y }
  exact ZMod.map_smul map c f

end Algebraic.Cutwidth.Extractor.Internal
