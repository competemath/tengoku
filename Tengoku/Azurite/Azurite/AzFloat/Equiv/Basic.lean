/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzFloat.Basic
import Tengoku.Azurite.Azurite.AzInt.Equiv.Basic
import Tengoku.Seed.Data.EReal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The value model of `AzFloat`

`toVal : AzFloat → Option EReal` is the specification every `AzFloat` operation is proven
against: `none` for `NaN`, `⊤`/`⊥` for `±∞`, and otherwise the exact real value.  `NaN`
propagation is `Option.bind`; the exceptional cases of the arithmetic (`∞ − ∞`, `0 · ∞`, …)
are spelled out by the specification functions of the operations, not by `EReal`'s own
conventions (Mathlib sets `⊤ + ⊥ = ⊥`).

This file: `toVal` itself, its values on the constructors and on `mkFinite`, and the sign
operations.
-/

namespace Azurite.AzFloat

/-- The real value of the finite representation `(sign, exponent, significand)`:
`(−1)^(¬sign) · m · 2^(exponent − m.size)`.-/
noncomputable def finiteVal (s : Bool) (e : AzInt) (m : AzNat) : ℝ :=
  (if s then 1 else -1) * (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - m.size)

/-- The value model: `none` for `NaN`, `⊤`/`⊥` for `±∞`, the exact real otherwise.-/
noncomputable def toVal : AzFloat → Option EReal
  | nan => none
  | infinity s => some (if s then ⊤ else ⊥)
  | zero => some 0
  | finite s e _ m _ => some ((finiteVal s e m : ℝ) : EReal)

/--
@isnad1 id=eq.0h0v.s2.b156e89b44bb from=translated src=- shape=0a817633 vocab=eb226a2b
-/
@[simp] theorem toVal_nan : toVal nan = none := rfl
/--
@isnad1 id=eq.0h1v.s4.4795f2cd4ae2 from=translated src=- shape=0bd18626 vocab=1ea69381
-/
@[simp] theorem toVal_infinity (s : Bool) :
    toVal (infinity s) = some (if s then ⊤ else ⊥) := rfl
/--
@isnad1 id=eq.0h0v.s3.839f67673b32 from=translated src=- shape=dcbb534e vocab=3804f053
-/
@[simp] theorem toVal_zero : toVal zero = some 0 := rfl
/--
@isnad1 id=eq.1h4v.s4.bd88d405a07e from=translated src=- shape=e0ba3902 vocab=bae0079b
-/
@[simp] theorem toVal_finite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat)
    (h : FiniteValid p m) : toVal (finite s e p m h) = some ((finiteVal s e m : ℝ) : EReal) :=
  rfl

/-- On a valid representation the value is `± m · 2^(e − alignedBits p)`.
@isnad1 id=eq.1h4v.s6.23438eee27a6 from=translated src=- shape=777665d3 vocab=a8a78c7b
-/
theorem finiteVal_eq_aligned (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat} (h : FiniteValid p m) :
    finiteVal s e m
      = (if s then 1 else -1) * (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - alignedBits p) := by
  unfold finiteVal
  rw [h.size_eq]

/--
@isnad1 id=ne.1h1v.s4.e725e05633c6 from=translated src=- shape=20a1293d vocab=e3edac28
-/
theorem toNat_ne_zero_of_ne_zero {m : AzNat} (hm : m ≠ 0) : m.toNat ≠ 0 :=
  fun h => hm (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))

/--
@isnad1 id=lt.1h1v.s4.3c5c3e0ea054 from=translated src=- shape=c87724ab vocab=a318e335
-/
theorem size_pos_of_ne_zero {m : AzNat} (hm : m ≠ 0) : 0 < m.size := by
  rw [← AzNat.size_toNat]
  exact Nat.size_pos.mpr (Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hm))

/--
@isnad1 id=eq.0h0v.s3.495d7b345225 from=translated src=- shape=1ac31801 vocab=c0b63398
-/
@[simp] theorem size_zero : (0 : AzNat).size = 0 := by
  rw [← AzNat.size_toNat, AzNat.toNat_zero, Nat.size_zero]

/--
@isnad1 id=ne.1h1v.s4.ce36a126327f from=translated src=- shape=2154ac66 vocab=a318e335
-/
theorem ne_zero_of_size_pos {m : AzNat} (h : 0 < m.size) : m ≠ 0 := by
  rintro rfl
  simp at h

/--
@isnad1 id=eq.1h4v.s4.251ac841dc63 from=translated src=- shape=9fc796ea vocab=05dc1039
-/
theorem finiteVal_shiftLeft (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) (k : ℕ) :
    finiteVal s e (m.shiftLeft k) = finiteVal s e m := by
  unfold finiteVal
  have hm0 := toNat_ne_zero_of_ne_zero hm
  have hsize : (m.shiftLeft k).size = m.size + k := by
    rw [← AzNat.size_toNat, AzNat.toNat_shiftLeft, ← Nat.shiftLeft_eq, Nat.size_shiftLeft hm0,
      AzNat.size_toNat]
  rw [hsize, AzNat.toNat_shiftLeft]
  push_cast
  rw [show e.toInt - ((m.size : ℤ) + k) = (e.toInt - m.size) - k by ring,
    zpow_sub₀ (by norm_num), zpow_natCast]
  field_simp

/-- `mkFinite` does not change the value.
@isnad1 id=eq.1h4v.s5.85c5a5580771 from=translated src=- shape=1afe2e11 vocab=6c4100c4
-/
theorem toVal_mkFinite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hm : m ≠ 0) :
    toVal (mkFinite s e p m) = some ((finiteVal s e m : ℝ) : EReal) := by
  unfold mkFinite
  rw [dite_eq_right hm]
  simp only [toVal, finiteVal_shiftLeft s e m hm]

/--
@isnad1 id=eq.0h3v.s4.d9453f87338a from=translated src=- shape=504e0b99 vocab=1511ded5
-/
@[simp] theorem mkFinite_zero (s : Bool) (e : AzInt) (p : ℕ) : mkFinite s e p 0 = zero := by
  unfold mkFinite
  rw [dite_eq_left rfl]

/--
@isnad1 id=eq.2h4v.s5.b270ffb6a310 from=translated src=- shape=4566e191 vocab=1cdadf2e
-/
theorem precision?_mkFinite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hm : m ≠ 0)
    (h : m.size ≤ p) : precision? (mkFinite s e p m) = some p := by
  unfold mkFinite
  rw [dite_eq_right hm]
  simp only [precision?, Nat.max_eq_left h]

/--
@isnad1 id=eq.1h4v.s4.dbad9713f33c from=translated src=- shape=f43fe15f vocab=92e53fd4
-/
theorem exponent?_mkFinite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hm : m ≠ 0) :
    exponent? (mkFinite s e p m) = some e := by
  unfold mkFinite
  rw [dite_eq_right hm]
  rfl

/--
@isnad1 id=eq.1h4v.s4.091ae0e1b779 from=translated src=- shape=21be9325 vocab=67876da4
-/
theorem sign?_mkFinite (s : Bool) (e : AzInt) (p : ℕ) (m : AzNat) (hm : m ≠ 0) :
    sign? (mkFinite s e p m) = some s := by
  unfold mkFinite
  rw [dite_eq_right hm]
  rfl

/-! ### `AzInt` helpers -/
/--
@isnad1 id=iff.0h1v.s4.a9e0f84c33b0 from=translated src=- shape=eec6a9b8 vocab=69ae47af
-/
theorem AzInt.sign_eq_true_iff (z : AzInt) : z.sign = true ↔ 0 ≤ z.toInt := by
  unfold AzInt.toInt
  cases hz : z.sign
  · simp only [Bool.false_eq_true, ↓reduceIte, false_iff, not_le, Left.neg_neg_iff, Nat.cast_pos]
    have : z.abs ≠ 0 := fun h => by have := z.zero_sign h; rw [hz] at this; cases this
    exact Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero this)
  · simp

/--
@isnad1 id=eq.1h1v.s4.9f3756a553d5 from=translated src=- shape=393f36d7 vocab=57544089
-/
theorem AzInt.mkNorm_sign_abs (z : AzInt) (h : z.abs ≠ 0) : AzInt.mkNorm z.sign z.abs = z := by
  unfold AzInt.mkNorm
  rw [dite_eq_right h]

/--
@isnad1 id=eq.0h1v.s4.29c6566fc7d7 from=translated src=- shape=cff37dbe vocab=afc591ed
-/
theorem AzInt.abs_toNat_eq (z : AzInt) : (z.abs.toNat : ℤ) = |z.toInt| := by
  unfold AzInt.toInt; cases z.sign <;> simp

/-! ### Sign operations -/

/--
@isnad1 id=eq.0h3v.s4.5c426f06c9b3 from=translated src=- shape=b99d7670 vocab=806793a8
-/
theorem finiteVal_not (s : Bool) (e : AzInt) (m : AzNat) :
    finiteVal (!s) e m = -finiteVal s e m := by
  unfold finiteVal
  cases s <;> simp

/--
@isnad1 id=eq.0h1v.s4.b3e5ebe7f7e2 from=translated src=- shape=168dc0d9 vocab=34e76577
-/
theorem toVal_neg (x : AzFloat) : toVal (-x) = (toVal x).map fun v => -v := by
  show toVal x.neg = _
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [neg, toVal]
  | zero => simp [neg, toVal]
  | finite s e p m h => simp [neg, toVal, finiteVal_not]

/--
@isnad1 id=eq.0h3v.s4.6128d76a3eab from=translated src=- shape=78b74894 vocab=0b0295d3
-/
theorem finiteVal_true_eq_abs (s : Bool) (e : AzInt) (m : AzNat) :
    finiteVal true e m = |finiteVal s e m| := by
  unfold finiteVal
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - m.size) := zpow_pos (by norm_num) _
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, abs_neg]
    rw [abs_of_nonneg (by positivity)]
  · simp only [↓reduceIte, one_mul]
    rw [abs_of_nonneg (by positivity)]

/--
@isnad1 id=eq.0h1v.s5.a74f82e4d7b2 from=translated src=- shape=4e3e4287 vocab=cc354207
-/
theorem toVal_abs (x : AzFloat) : toVal x.abs = (toVal x).map fun v => max v (-v) := by
  cases x with
  | nan => rfl
  | infinity s => cases s <;> simp [abs, toVal]
  | zero => simp [abs, toVal]
  | finite s e p m h =>
    simp only [abs, toVal, Option.map_some, Option.some.injEq]
    rw [finiteVal_true_eq_abs s, abs_eq_max_neg, EReal.coe_strictMono.monotone.map_max,
      EReal.coe_neg]

end Azurite.AzFloat
