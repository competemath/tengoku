/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer exponents on a root of unity

An `N`-th root of unity `u` in a monoid has `u ^ m` depending only on `m mod N`, so integer
exponents make sense. Two spellings of "reduce the exponent mod `N`" occur in this
repository:

* `u ^ x.val` for `x : ZMod N` — the descent's `rootSplitting` uses this, because the
  determinant of a `ZMod N`-matrix is a `ZMod N`;
* `u ^ (m % (N : ℤ)).toNat` for `m : ℤ` — the Weil-pairing register uses this, because the
  symplectic law is stated with integer scalars `a b c d : ℤ`.

`toNat_emod_eq_val` identifies the two, and the arithmetic laws are then stated once in the
`ZMod`-spelling (`pow_val_add`, `pow_val_mul`) and transported (`pow_toNat_emod_add`,
`pow_toNat_emod_mul`). `pow_toNat_emod_neg` handles the inverse, which is what turns the
antisymmetry `e(x,y)·e(y,x) = 1` of a pairing into a statement about negated exponents.

Nothing here is specific to the Weil pairing; the file exists so that the register in
`WeilPairing/Basic.lean` and the field-level determinant law in
`WeilPairing/FieldPairingDet.lean` can share it without either importing the other.
-/

namespace ModularCurves

variable {M : Type*} [Monoid M] {u : M} {N : ℕ}

/-- For an `N`-th root of unity the exponent only matters modulo `N`.
@isnad1 id=eq.2h5v.s6.b95a30895e94 from=translated src=- shape=147ae94d vocab=87c448d2
-/
theorem pow_eq_pow_of_nat_modEq (hu : u ^ N = 1) {m n : ℕ} (h : m % N = n % N) :
    u ^ m = u ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m N]
  conv_rhs => rw [← Nat.div_add_mod n N]
  rw [pow_add, pow_add, pow_mul, pow_mul, hu, one_pow, one_pow, one_mul, one_mul, h]

/-- Powers of an `N`-th root of unity indexed by `ZMod N` are additive.
@isnad1 id=eq.1h5v.s7.6ee4d08922ca from=translated src=- shape=4473e6c0 vocab=2cbc250f
-/
theorem pow_val_add [NeZero N] (hu : u ^ N = 1) (x y : ZMod N) :
    u ^ x.val * u ^ y.val = u ^ (x + y).val := by
  rw [← pow_add]
  refine pow_eq_pow_of_nat_modEq hu ?_
  rw [ZMod.val_add, Nat.mod_mod]

/-- Powers of an `N`-th root of unity indexed by `ZMod N` are multiplicative in the
exponent.
@isnad1 id=eq.1h5v.s6.f3b9a67312cc from=translated src=- shape=0afc195a vocab=51a24239
-/
theorem pow_val_mul [NeZero N] (hu : u ^ N = 1) (x y : ZMod N) :
    u ^ (x * y).val = u ^ (x.val * y.val) := by
  refine pow_eq_pow_of_nat_modEq hu ?_
  rw [ZMod.val_mul, Nat.mod_mod]

/-- The two spellings of a reduced exponent agree: `(m % N).toNat` is the `ZMod N`-value of
`m`.
@isnad1 id=eq.0h2v.s5.971452cfa248 from=translated src=- shape=bc86eb8a vocab=a714ba2e
-/
theorem toNat_emod_eq_val (N : ℕ) [NeZero N] (m : ℤ) :
    (m % (N : ℤ)).toNat = ((m : ZMod N)).val := by
  rw [← ZMod.val_intCast (n := N) m, Int.toNat_natCast]

/-- Integer exponents on an `N`-th root of unity are additive.
@isnad1 id=eq.1h5v.s7.86e727405592 from=translated src=- shape=4e79558d vocab=5e342938
-/
theorem pow_toNat_emod_add [NeZero N] (hu : u ^ N = 1) (m n : ℤ) :
    u ^ (m % (N : ℤ)).toNat * u ^ (n % (N : ℤ)).toNat =
      u ^ ((m + n) % (N : ℤ)).toNat := by
  rw [toNat_emod_eq_val, toNat_emod_eq_val, toNat_emod_eq_val, pow_val_add hu, Int.cast_add]

/-- Iterating integer exponents on an `N`-th root of unity multiplies them.
@isnad1 id=eq.1h5v.s7.d2163801a294 from=translated src=- shape=1bdf1706 vocab=f754fa16
-/
theorem pow_toNat_emod_mul [NeZero N] (hu : u ^ N = 1) (m n : ℤ) :
    (u ^ (n % (N : ℤ)).toNat) ^ (m % (N : ℤ)).toNat =
      u ^ ((m * n) % (N : ℤ)).toNat := by
  rw [← pow_mul, toNat_emod_eq_val, toNat_emod_eq_val, toNat_emod_eq_val, Int.cast_mul,
    pow_val_mul hu, mul_comm ((n : ZMod N)).val]

/-- The reduced power at exponent `0` is `1`.
@isnad1 id=eq.0h3v.s5.fb3db7992eb0 from=translated src=- shape=5c9e4fab vocab=a24bb8f4
-/
@[simp] theorem pow_toNat_emod_zero [NeZero N] : u ^ ((0 : ℤ) % (N : ℤ)).toNat = 1 := by
  rw [toNat_emod_eq_val]
  simp

/-- A mutually-inverse pair stays mutually inverse under a common power. This is the shape
an antisymmetric pairing produces — `u = e(x,y)`, `v = e(y,x)` — and is what lets the two
off-diagonal terms of the symplectic law cancel without ever forming an inverse.
@isnad1 id=eq.1h4v.s6.da4fe18c0731 from=translated src=- shape=2fe8d7f1 vocab=0877a651
-/
theorem pow_mul_pow_eq_one {M : Type*} [CommMonoid M] {u v : M} (huv : u * v = 1) (k : ℕ) :
    u ^ k * v ^ k = 1 := by
  rw [← mul_pow, huv, one_pow]

/-- A root of unity is a unit — the cancellation the symplectic derivation needs.
@isnad1 id=isunit.1h3v.s5.527f813834d6 from=translated src=- shape=e3c9ec08 vocab=d64ca8c6
-/
theorem isUnit_of_pow_eq_one [NeZero N] (hu : u ^ N = 1) : IsUnit u :=
  IsUnit.of_pow_eq_one hu (NeZero.ne N)

end ModularCurves
