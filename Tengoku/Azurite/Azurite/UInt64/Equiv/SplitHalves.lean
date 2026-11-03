/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.Data.Nat.Bitwise
import Tengoku.Seed.Tactic.Ring
import Tengoku.Azurite.Azurite.UInt64.SplitHalves

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace UInt64

/--
@isnad1 id=eq.0h2v.s5.a556c00d4500 from=translated src=- shape=46294351 vocab=c1d48703
-/
theorem toNat_joinHalves (hi lo : UInt32) :
    (joinHalves hi lo).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  unfold joinHalves
  rw [_root_.UInt64.toNat_or, _root_.UInt64.toNat_shiftLeft,
      _root_.UInt32.toNat_toUInt64, _root_.UInt32.toNat_toUInt64]
  rw [show ((32 : UInt64).toNat = 32) from rfl]
  rw [show ((32 : Nat) % 64 = 32) from by decide]
  have hhi : hi.toNat < 2 ^ 32 := _root_.UInt32.toNat_lt hi
  have hlo : lo.toNat < 2 ^ 32 := _root_.UInt32.toNat_lt lo
  have hshift : hi.toNat <<< 32 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    calc hi.toNat * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos 32)).mpr hhi
      _ = 2 ^ 64 := by rw [← Nat.pow_add]
  rw [Nat.mod_eq_of_lt hshift]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  rw [show hi.toNat * 2 ^ 32 + lo.toNat = 2 ^ 32 * hi.toNat + lo.toNat from by ring]
  rw [Nat.testBit_two_pow_mul_add hi.toNat hlo j]
  by_cases hj : j < 32
  · simp [hj, show ¬ j ≥ 32 from by omega]
  · have hj' : j ≥ 32 := by omega
    simp [hj, hj',
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by omega) hj'))]

/--
@isnad1 id=eq.0h1v.s3.f02788000b8e from=translated src=- shape=5e260e4c vocab=8b4573cc
-/
theorem splitInHalf_eq (u : UInt64) : splitInHalf u = (hiHalf u, loHalf u) := rfl

/--
@isnad1 id=eq.0h1v.s3.122aa86caca4 from=translated src=- shape=9aeca154 vocab=d2913445
-/
theorem hiHalf_eq_fst (u : UInt64) : hiHalf u = (splitInHalf u).1 := rfl

/--
@isnad1 id=eq.0h1v.s3.b5e99b345e58 from=translated src=- shape=9aeca154 vocab=e7520bef
-/
theorem loHalf_eq_snd (u : UInt64) : loHalf u = (splitInHalf u).2 := rfl

/--
@isnad1 id=eq.0h1v.s3.643dbbf2d642 from=translated src=- shape=5dad4736 vocab=84cb1490
-/
theorem wideLoHalf_eq_toUInt64 (u : UInt64) : wideLoHalf u = (loHalf u).toUInt64 := rfl

/--
@isnad1 id=eq.0h1v.s3.6b8ea8527551 from=translated src=- shape=7718e021 vocab=ac86c550
-/
theorem toUInt32_wideHiHalf (u : UInt64) : (wideHiHalf u).toUInt32 = hiHalf u := rfl

/--
@isnad1 id=eq.0h1v.s3.80909ad21fd9 from=translated src=- shape=7718e021 vocab=241b65f3
-/
theorem toUInt32_wideLoHalf (u : UInt64) : (wideLoHalf u).toUInt32 = loHalf u := by
  apply _root_.UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  rw [_root_.UInt32.toNat_toBitVec, _root_.UInt32.toNat_toBitVec]
  unfold wideLoHalf loHalf
  rw [_root_.UInt64.toNat_toUInt32, _root_.UInt32.toNat_toUInt64]
  have h : u.toUInt32.toNat < 2 ^ 32 := _root_.UInt32.toNat_lt _
  exact Nat.mod_eq_of_lt h

/--
@isnad1 id=eq.0h1v.s3.8a22cd54d452 from=translated src=- shape=5dad4736 vocab=32d073e9
-/
theorem wideHiHalf_eq_toUInt64 (u : UInt64) : wideHiHalf u = (hiHalf u).toUInt64 := by
  apply _root_.UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  rw [_root_.UInt64.toNat_toBitVec, _root_.UInt64.toNat_toBitVec]
  unfold wideHiHalf hiHalf
  rw [_root_.UInt32.toNat_toUInt64, _root_.UInt64.toNat_toUInt32,
      _root_.UInt64.toNat_shiftRight]
  rw [show ((32 : UInt64).toNat = 32) from rfl]
  rw [show ((32 : Nat) % 64 = 32) from by decide]
  rw [Nat.shiftRight_eq_div_pow]
  have hu : u.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt u
  have hdiv : u.toNat / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32) |>.mpr
    rw [show (2 ^ 32 * 2 ^ 32 : Nat) = 2 ^ 64 from by rw [← Nat.pow_add]]
    exact hu
  exact (Nat.mod_eq_of_lt hdiv).symm

/--
@isnad1 id=eq.0h1v.s4.418feca21337 from=translated src=- shape=4f67078d vocab=49cc2a7e
-/
theorem joinHalves_splitInHalf (u : UInt64) :
    joinHalves (splitInHalf u).1 (splitInHalf u).2 = u := by
  apply _root_.UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  rw [_root_.UInt64.toNat_toBitVec, _root_.UInt64.toNat_toBitVec]
  unfold splitInHalf hiHalf loHalf
  dsimp
  rw [toNat_joinHalves]
  rw [_root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_toUInt32,
      _root_.UInt64.toNat_shiftRight]
  rw [show ((32 : UInt64).toNat = 32) from rfl]
  rw [show ((32 : Nat) % 64 = 32) from by decide]
  rw [Nat.shiftRight_eq_div_pow]
  have hu : u.toNat < 2 ^ 64 := _root_.UInt64.toNat_lt u
  have hdiv : u.toNat / 2 ^ 32 < 2 ^ 32 := by
    apply Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32) |>.mpr
    rw [show (2 ^ 32 * 2 ^ 32 : Nat) = 2 ^ 64 from by rw [← Nat.pow_add]]
    exact hu
  rw [Nat.mod_eq_of_lt hdiv]
  conv_rhs => rw [← Nat.div_add_mod u.toNat (2 ^ 32)]
  ring

/--
@isnad1 id=eq.0h2v.s4.98ca1e77de60 from=translated src=- shape=139ab35a vocab=21ca0b2a
-/
theorem splitInHalf_joinHalves (hi lo : UInt32) :
    splitInHalf (joinHalves hi lo) = (hi, lo) := by
  have hhi : hi.toNat < 2 ^ 32 := _root_.UInt32.toNat_lt hi
  have hlo : lo.toNat < 2 ^ 32 := _root_.UInt32.toNat_lt lo
  have hfst : ((joinHalves hi lo) >>> 32).toUInt32 = hi := by
    apply _root_.UInt32.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    rw [_root_.UInt32.toNat_toBitVec, _root_.UInt32.toNat_toBitVec,
        _root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_shiftRight]
    rw [show ((32 : UInt64).toNat = 32) from rfl]
    rw [show ((32 : Nat) % 64 = 32) from by decide]
    rw [Nat.shiftRight_eq_div_pow, toNat_joinHalves]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 32)]
    rw [Nat.div_eq_of_lt hlo, Nat.zero_add, Nat.mod_eq_of_lt hhi]
  have hsnd : (joinHalves hi lo).toUInt32 = lo := by
    apply _root_.UInt32.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    rw [_root_.UInt32.toNat_toBitVec, _root_.UInt32.toNat_toBitVec,
        _root_.UInt64.toNat_toUInt32, toNat_joinHalves]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hlo
  unfold splitInHalf
  exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨hfst, hsnd⟩

end UInt64
