/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzNat.Conversion
import Tengoku.Azurite.Azurite.AzNat.Equiv.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/--
@isnad1 id=eq.0h1v.s3.4abc83e90051 from=translated src=- shape=7718e021 vocab=c2652c6b
-/
theorem UInt64.toNat_toAzNat (u : UInt64) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt64.toAzNat
  by_cases h : u = 0
  · simp [h, Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]
  · simp [h, Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]

/--
@isnad1 id=eq.0h1v.s3.f92909084f63 from=translated src=- shape=7718e021 vocab=4d46fd8d
-/
theorem UInt32.toNat_toAzNat (u : UInt32) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt32.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

/--
@isnad1 id=eq.0h1v.s3.3ebb244944fa from=translated src=- shape=7718e021 vocab=4b2baa9a
-/
theorem UInt16.toNat_toAzNat (u : UInt16) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt16.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

/--
@isnad1 id=eq.0h1v.s3.0697e5af6dc6 from=translated src=- shape=7718e021 vocab=4931b940
-/
theorem UInt8.toNat_toAzNat (u : UInt8) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold UInt8.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

/--
@isnad1 id=eq.0h1v.s3.a2dfe19fd77f from=translated src=- shape=7718e021 vocab=803ff9ec
-/
theorem USize.toNat_toAzNat (u : USize) : Azurite.AzNat.toNat u.toAzNat = u.toNat := by
  unfold USize.toAzNat; rw [UInt64.toNat_toAzNat]; rfl

/--
@isnad1 id=eq.0h1v.s3.24e66c6d0d82 from=translated src=- shape=7718e021 vocab=bff003eb
-/
theorem Int64.toNat_toAzNatClampNeg (i : Int64) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int64.toAzNatClampNeg
  split
  · rename_i h
    have h1 : i.toBitVec.slt 0 = true := h
    have h2 : decide (i.toBitVec.toInt < 0) = true := h1
    have h3 : i.toInt < 0 := of_decide_eq_true h2
    simp [Azurite.AzNat.toNat, Azurite.AzNat.toNatLimbsList]
    change 0 = i.toInt.toNat
    omega
  · rename_i h
    rw [UInt64.toNat_toAzNat]
    have h1 : ¬(i.toBitVec.slt 0 = true) := h
    have h2 : ¬(decide (i.toBitVec.toInt < 0) = true) := h1
    have h3 : ¬(i.toInt < 0) := fun hc => h2 (decide_eq_true hc)
    have h4 : 0 ≤ i.toInt := by exact Int.not_lt.mp h3
    change i.toBitVec.toNat = i.toInt.toNat
    have h_toInt : i.toInt = if 2 * i.toBitVec.toNat < 2 ^ 64 then (i.toBitVec.toNat : ℤ) else (i.toBitVec.toNat : ℤ) - (2 ^ 64 : ℤ) := rfl
    have isLt := i.toBitVec.isLt
    omega

/--
@isnad1 id=eq.0h1v.s3.41295224b169 from=translated src=- shape=7718e021 vocab=7e11b359
-/
theorem Int32.toNat_toAzNatClampNeg (i : Int32) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int32.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int32.toInt_toInt64]

/--
@isnad1 id=eq.0h1v.s3.2d7ae77115b3 from=translated src=- shape=7718e021 vocab=4c2a3802
-/
theorem Int16.toNat_toAzNatClampNeg (i : Int16) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int16.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int16.toInt_toInt64]

/--
@isnad1 id=eq.0h1v.s3.b1cc9129cef9 from=translated src=- shape=7718e021 vocab=634fc1d4
-/
theorem Int8.toNat_toAzNatClampNeg (i : Int8) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold Int8.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [Int8.toInt_toInt64]

/--
@isnad1 id=eq.0h1v.s3.a1412dd27b38 from=translated src=- shape=7718e021 vocab=6539b88b
-/
theorem ISize.toNat_toAzNatClampNeg (i : ISize) : Azurite.AzNat.toNat i.toAzNatClampNeg = i.toNatClampNeg := by
  unfold ISize.toAzNatClampNeg
  rw [Int64.toNat_toAzNatClampNeg]
  change i.toInt64.toInt.toNat = i.toInt.toNat
  rw [ISize.toInt_toInt64]

/--
@isnad1 id=eq.0h1v.s3.bc66eea825f3 from=translated src=- shape=7718e021 vocab=be40fe8e
-/
theorem UInt64.ofNat_toNat_eq_toAzNat (u : UInt64) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt64.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.d5c52c0992a5 from=translated src=- shape=7718e021 vocab=9b0b7bd8
-/
theorem UInt32.ofNat_toNat_eq_toAzNat (u : UInt32) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt32.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.cf2956d3d3bf from=translated src=- shape=7718e021 vocab=7c534c0b
-/
theorem UInt16.ofNat_toNat_eq_toAzNat (u : UInt16) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt16.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.9a9d52797cb6 from=translated src=- shape=7718e021 vocab=c0dfeddc
-/
theorem UInt8.ofNat_toNat_eq_toAzNat (u : UInt8) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← UInt8.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.c5d3e3e938ea from=translated src=- shape=7718e021 vocab=f8a62296
-/
theorem USize.ofNat_toNat_eq_toAzNat (u : USize) : Azurite.AzNat.ofNat u.toNat = u.toAzNat := by
  rw [← USize.toNat_toAzNat, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.094b6ca84961 from=translated src=- shape=7718e021 vocab=a76488ee
-/
theorem Int64.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int64) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int64.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.53911e99a811 from=translated src=- shape=7718e021 vocab=73009115
-/
theorem Int32.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int32) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int32.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.706a99a1786f from=translated src=- shape=7718e021 vocab=178031d8
-/
theorem Int16.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int16) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int16.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.14a6f6912241 from=translated src=- shape=7718e021 vocab=31a3b526
-/
theorem Int8.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : Int8) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← Int8.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

/--
@isnad1 id=eq.0h1v.s3.414b8b1c9aff from=translated src=- shape=7718e021 vocab=254c4265
-/
theorem ISize.ofNat_toNatClampNeg_eq_toAzNatClampNeg (i : ISize) : Azurite.AzNat.ofNat i.toNatClampNeg = i.toAzNatClampNeg := by
  rw [← ISize.toNat_toAzNatClampNeg, Azurite.AzNat.ofNat_toNat]

namespace Azurite.AzNat

/--
@isnad1 id=eq.0h1v.s6.370b6133e5a5 from=translated src=- shape=bc0e694a vocab=f1c8fdd0
-/
lemma toNatLimbsList_mod_2_64 (l : List UInt64) : toNatLimbsList l % 2^64 = if h : 0 < l.length then (l.get ⟨0, h⟩).toNat else 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [toNatLimbsList]

/--
@isnad1 id=eq.0h1v.s5.d2affa18bc70 from=translated src=- shape=9fd4e752 vocab=ef00fb52
-/
lemma toNat_mod_2_64_eq_toUInt64_toNat (n : AzNat) : n.toNat % 2^64 = n.toUInt64.toNat := by
  unfold toNat toUInt64
  have ht := toNatLimbsList_mod_2_64 n.limbs.toList
  rw [ht]
  simp
  split
  · rfl
  · rfl

/--
@isnad1 id=eq.0h1v.s3.2a98e1c562d9 from=translated src=- shape=69b989be vocab=0bf434c5
-/
theorem toUInt64_toNat (n : AzNat) : n.toUInt64 = n.toNat.toUInt64 := by
  apply UInt64.ext
  have h_nat : n.toNat.toUInt64.toNat = n.toNat % 2^64 := rfl
  rw [h_nat]
  exact (toNat_mod_2_64_eq_toUInt64_toNat n).symm

/--
@isnad1 id=eq.0h1v.s3.0bc983eea010 from=translated src=- shape=7718e021 vocab=dae160ed
-/
theorem toUInt64_ofNat (n : Nat) : (ofNat n).toUInt64 = n.toUInt64 := by
  have ht := toUInt64_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- UInt32
/--
@isnad1 id=eq.0h1v.s3.887cea228046 from=translated src=- shape=7718e021 vocab=4ea17a7b
-/
lemma nat_toUInt64_toUInt32 (N : Nat) : N.toUInt64.toUInt32 = N.toUInt32 := by
  apply UInt32.ext
  have h1 : N.toUInt64.toUInt32.toNat = N.toUInt64.toNat % 2^32 := rfl
  have h2 : N.toUInt64.toNat = N % 2^64 := rfl
  have h3 : N.toUInt32.toNat = N % 2^32 := rfl
  rw [h1, h2, h3]
  exact Nat.mod_mod_of_dvd N (by decide)

/--
@isnad1 id=eq.0h1v.s3.654b6bac347e from=translated src=- shape=69b989be vocab=b058ce7c
-/
theorem toUInt32_toNat (n : AzNat) : n.toUInt32 = n.toNat.toUInt32 := by
  have h1 : n.toUInt32 = n.toUInt64.toUInt32 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt32]

/--
@isnad1 id=eq.0h1v.s3.df7a4f842670 from=translated src=- shape=7718e021 vocab=b20cfd52
-/
theorem toUInt32_ofNat (n : Nat) : (ofNat n).toUInt32 = n.toUInt32 := by
  have ht := toUInt32_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- UInt16
/--
@isnad1 id=eq.0h1v.s3.8cf2ea6e5485 from=translated src=- shape=7718e021 vocab=bbf633a2
-/
lemma nat_toUInt64_toUInt16 (N : Nat) : N.toUInt64.toUInt16 = N.toUInt16 := by
  apply UInt16.ext
  have h1 : N.toUInt64.toUInt16.toNat = N.toUInt64.toNat % 2^16 := rfl
  have h2 : N.toUInt64.toNat = N % 2^64 := rfl
  have h3 : N.toUInt16.toNat = N % 2^16 := rfl
  rw [h1, h2, h3]
  exact Nat.mod_mod_of_dvd N (by decide)

/--
@isnad1 id=eq.0h1v.s3.a95b57135baf from=translated src=- shape=69b989be vocab=2655824a
-/
theorem toUInt16_toNat (n : AzNat) : n.toUInt16 = n.toNat.toUInt16 := by
  have h1 : n.toUInt16 = n.toUInt64.toUInt16 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt16]

/--
@isnad1 id=eq.0h1v.s3.cc6e1a08834f from=translated src=- shape=7718e021 vocab=beb965eb
-/
theorem toUInt16_ofNat (n : Nat) : (ofNat n).toUInt16 = n.toUInt16 := by
  have ht := toUInt16_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- UInt8
/--
@isnad1 id=eq.0h1v.s3.bff6a373e293 from=translated src=- shape=7718e021 vocab=aa7f65d8
-/
lemma nat_toUInt64_toUInt8 (N : Nat) : N.toUInt64.toUInt8 = N.toUInt8 := by
  apply UInt8.ext
  have h1 : N.toUInt64.toUInt8.toNat = N.toUInt64.toNat % 2^8 := rfl
  have h2 : N.toUInt64.toNat = N % 2^64 := rfl
  have h3 : N.toUInt8.toNat = N % 2^8 := rfl
  rw [h1, h2, h3]
  exact Nat.mod_mod_of_dvd N (by decide)

/--
@isnad1 id=eq.0h1v.s3.f3345308dcd1 from=translated src=- shape=69b989be vocab=b4560a58
-/
theorem toUInt8_toNat (n : AzNat) : n.toUInt8 = n.toNat.toUInt8 := by
  have h1 : n.toUInt8 = n.toUInt64.toUInt8 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt8]

/--
@isnad1 id=eq.0h1v.s3.1e67558a3c29 from=translated src=- shape=7718e021 vocab=9921b97a
-/
theorem toUInt8_ofNat (n : Nat) : (ofNat n).toUInt8 = n.toUInt8 := by
  have ht := toUInt8_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- USize
/--
@isnad1 id=eq.0h1v.s3.5421d42b2520 from=translated src=- shape=7718e021 vocab=1f3eb162
-/
lemma nat_toUInt64_toUSize (N : Nat) : N.toUInt64.toUSize = N.toUSize := by
  apply USize.ext
  have h1 : N.toUInt64.toUSize.toNat = N.toUInt64.toNat % USize.size := rfl
  have h2 : N.toUInt64.toNat = N % 2^64 := rfl
  have h3 : N.toUSize.toNat = N % USize.size := rfl
  rw [h1, h2, h3]
  have hdvd : USize.size ∣ 2^64 := by
    obtain h | h := USize.size_eq
    · rw [h]; decide
    · rw [h]; decide
  exact Nat.mod_mod_of_dvd N hdvd

/--
@isnad1 id=eq.0h1v.s3.a7b5b748502b from=translated src=- shape=69b989be vocab=80ac347e
-/
theorem toUSize_toNat (n : AzNat) : n.toUSize = n.toNat.toUSize := by
  have h1 : n.toUSize = n.toUInt64.toUSize := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUSize]

/--
@isnad1 id=eq.0h1v.s3.85869f281086 from=translated src=- shape=7718e021 vocab=d4c1d750
-/
theorem toUSize_ofNat (n : Nat) : (ofNat n).toUSize = n.toUSize := by
  have ht := toUSize_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- Int64
/--
@isnad1 id=eq.0h1v.s3.171d0121a7d1 from=translated src=- shape=433304fb vocab=3409c8f1
-/
theorem toInt64_toNat (n : AzNat) : n.toInt64 = n.toNat.toUInt64.toInt64 := by
  have h1 : n.toInt64 = n.toUInt64.toInt64 := rfl
  rw [h1, toUInt64_toNat]

/--
@isnad1 id=eq.0h1v.s3.50d045ffad1f from=translated src=- shape=7367b1cd vocab=30af7355
-/
theorem toInt64_ofNat (n : Nat) : (ofNat n).toInt64 = n.toUInt64.toInt64 := by
  have ht := toInt64_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- Int32
/--
@isnad1 id=eq.0h1v.s3.dd7b49daa200 from=translated src=- shape=433304fb vocab=de6e217b
-/
theorem toInt32_toNat (n : AzNat) : n.toInt32 = n.toNat.toUInt32.toInt32 := by
  have h1 : n.toInt32 = n.toUInt64.toUInt32.toInt32 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt32]

/--
@isnad1 id=eq.0h1v.s3.f4fe5a4f4cee from=translated src=- shape=7367b1cd vocab=0d0fd027
-/
theorem toInt32_ofNat (n : Nat) : (ofNat n).toInt32 = n.toUInt32.toInt32 := by
  have ht := toInt32_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- Int16
/--
@isnad1 id=eq.0h1v.s3.084fffb919bb from=translated src=- shape=433304fb vocab=95845da9
-/
theorem toInt16_toNat (n : AzNat) : n.toInt16 = n.toNat.toUInt16.toInt16 := by
  have h1 : n.toInt16 = n.toUInt64.toUInt16.toInt16 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt16]

/--
@isnad1 id=eq.0h1v.s3.d4966ac8776c from=translated src=- shape=7367b1cd vocab=212f943d
-/
theorem toInt16_ofNat (n : Nat) : (ofNat n).toInt16 = n.toUInt16.toInt16 := by
  have ht := toInt16_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- Int8
/--
@isnad1 id=eq.0h1v.s3.c9c5ef23773e from=translated src=- shape=433304fb vocab=55b526fa
-/
theorem toInt8_toNat (n : AzNat) : n.toInt8 = n.toNat.toUInt8.toInt8 := by
  have h1 : n.toInt8 = n.toUInt64.toUInt8.toInt8 := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUInt8]

/--
@isnad1 id=eq.0h1v.s3.c0e118b0b08e from=translated src=- shape=7367b1cd vocab=73868876
-/
theorem toInt8_ofNat (n : Nat) : (ofNat n).toInt8 = n.toUInt8.toInt8 := by
  have ht := toInt8_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

-- ISize
/--
@isnad1 id=eq.0h1v.s3.696737007ed3 from=translated src=- shape=433304fb vocab=3c3bb4a2
-/
theorem toISize_toNat (n : AzNat) : n.toISize = n.toNat.toUSize.toISize := by
  have h1 : n.toISize = n.toUInt64.toUSize.toISize := rfl
  rw [h1, toUInt64_toNat, nat_toUInt64_toUSize]

/--
@isnad1 id=eq.0h1v.s3.8802f3a03f2c from=translated src=- shape=7367b1cd vocab=73a01bd9
-/
theorem toISize_ofNat (n : Nat) : (ofNat n).toISize = n.toUSize.toISize := by
  have ht := toISize_toNat (ofNat n)
  rw [toNat_ofNat] at ht
  exact ht

end Azurite.AzNat
