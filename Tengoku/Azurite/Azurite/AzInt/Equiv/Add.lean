/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.AzInt.Add
import Tengoku.Azurite.Azurite.AzInt.Equiv.Basic
import Tengoku.Azurite.Azurite.AzInt.Equiv.Conversion
import Tengoku.Azurite.Azurite.AzNat.Equiv.Add
import Tengoku.Azurite.Azurite.AzNat.Equiv.Sub
import Tengoku.Azurite.Azurite.AzNat.Equiv.Compare

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite.AzInt

/-- `mkNorm true a` represents `a` nonnegatively.
@isnad1 id=eq.0h1v.s3.a3017a3dbe38 from=translated src=- shape=c1004c8b vocab=01d4ac72
-/
lemma toInt_mkNorm_true (a : AzNat) : (mkNorm true a).toInt = (a.toNat : Int) := by
  unfold mkNorm
  by_cases h : a = 0
  · simp only [h, ↓reduceDIte]
    show ((0 : AzInt)).toInt = ((0 : AzNat).toNat : Int)
    rfl
  · simp only [h, ↓reduceDIte]
    show (if true then (a.toNat : Int) else _) = _
    simp

/-- `mkNorm false a` represents `-a` when `a ≠ 0`.
@isnad1 id=eq.1h1v.s4.ab1d6a1e959a from=translated src=- shape=895b49c2 vocab=87dab87f
-/
lemma toInt_mkNorm_false (a : AzNat) (h : a ≠ 0) :
    (mkNorm false a).toInt = -(a.toNat : Int) := by
  unfold mkNorm
  simp only [h, ↓reduceDIte]
  show (if false then _ else -(a.toNat : Int)) = _
  simp

/-- `mkNonzero false a h` represents `-a`.
@isnad1 id=eq.1h1v.s4.676998959581 from=translated src=- shape=ff1d1bb6 vocab=89bde439
-/
lemma toInt_mkNonzero_false (a : AzNat) (h : a ≠ 0) :
    (mkNonzero false a h).toInt = -(a.toNat : Int) := by
  show (if false then _ else -(a.toNat : Int)) = _
  simp

/-- `mkNonzero true a h` represents `a`.
@isnad1 id=eq.1h1v.s4.c73750f696c2 from=translated src=- shape=747d5761 vocab=b83554fa
-/
lemma toInt_mkNonzero_true (a : AzNat) (h : a ≠ 0) :
    (mkNonzero true a h).toInt = (a.toNat : Int) := by
  show (if true then (a.toNat : Int) else _) = _
  simp

/-- Correctness of `AzInt.addUInt64`.
@isnad1 id=eq.0h2v.s4.b40ce36b2619 from=translated src=- shape=df04f8ad vocab=104b0a50
-/
theorem toInt_addUInt64 (z : AzInt) (u : UInt64) :
    (z.addUInt64 u).toInt = z.toInt + (u.toNat : Int) := by
  unfold addUInt64
  have h_tz : z.toInt = if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int) := rfl
  rw [h_tz]
  by_cases hs : z.sign
  · simp only [hs, ↓reduceIte]
    rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_addUInt64]
    push_cast; ring
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    have h_eq := AzNat.compareUInt64_eq z.abs u
    split <;> rename_i h_cmp
    · -- .lt
      rw [h_cmp] at h_eq
      have h_lt : z.abs.toNat < u.toNat := Nat.compare_eq_lt.mp h_eq.symm
      rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_sub, UInt64.toNat_toAzNat]
      omega
    · -- .eq
      rw [h_cmp] at h_eq
      have h_e : z.abs.toNat = u.toNat := Nat.compare_eq_eq.mp h_eq.symm
      rw [toInt_zero]; omega
    · -- .gt
      rw [h_cmp] at h_eq
      have h_gt : u.toNat < z.abs.toNat := Nat.compare_eq_gt.mp h_eq.symm
      have h_sub_pos : z.abs.subUInt64 u ≠ 0 := by
        intro hc
        have hc' : (z.abs.subUInt64 u).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_subUInt64] at hc'; omega
      rw [toInt_mkNonzero_false _ h_sub_pos, AzNat.toNat_subUInt64]
      omega

/-- `ofInt`-version of `toInt_addUInt64`.
@isnad1 id=eq.0h2v.s4.4d509a9ee1d1 from=translated src=- shape=d6a30233 vocab=991cee79
-/
theorem ofInt_addUInt64 (i : Int) (u : UInt64) :
    ofInt (i + (u.toNat : Int)) = (ofInt i).addUInt64 u := by
  have h : (ofInt (i + (u.toNat : Int))).toInt = ((ofInt i).addUInt64 u).toInt := by
    rw [toInt_ofInt, toInt_addUInt64, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- Correctness of `AzInt.add`.
@isnad1 id=eq.0h2v.s4.20a54e94d10e from=translated src=- shape=0438c7a3 vocab=393d9100
-/
theorem toInt_add (a b : AzInt) : (a + b).toInt = a.toInt + b.toInt := by
  show (add a b).toInt = a.toInt + b.toInt
  unfold add
  have h_ta : a.toInt = if a.sign then (a.abs.toNat : Int) else -(a.abs.toNat : Int) := rfl
  have h_tb : b.toInt = if b.sign then (b.abs.toNat : Int) else -(b.abs.toNat : Int) := rfl
  rw [h_ta, h_tb]
  have h_cmp_eq := AzNat.compare_eq_compare_toNat a.abs b.abs
  by_cases hsa : a.sign = true
  · by_cases hsb : b.sign = true
    · -- true, true
      simp only [hsa, hsb, ↓reduceDIte, ↓reduceIte]
      rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_add]
      push_cast; ring
    · -- true, false
      simp only [hsa, hsb, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i h_cmp
      · rw [h_cmp] at h_cmp_eq
        have h_lt : a.abs.toNat < b.abs.toNat := Nat.compare_eq_lt.mp h_cmp_eq.symm
        have h_sub_ne : b.abs - a.abs ≠ 0 := by
          intro hc
          have : (b.abs - a.abs).toNat = 0 := by rw [hc]; rfl
          rw [AzNat.toNat_sub] at this; omega
        rw [toInt_mkNonzero_false _ h_sub_ne, AzNat.toNat_sub]
        omega
      · rw [h_cmp] at h_cmp_eq
        have h_eq : a.abs.toNat = b.abs.toNat := Nat.compare_eq_eq.mp h_cmp_eq.symm
        rw [toInt_zero]; omega
      · rw [h_cmp] at h_cmp_eq
        have h_gt : b.abs.toNat < a.abs.toNat := Nat.compare_eq_gt.mp h_cmp_eq.symm
        rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_sub]
        omega
  · have hanz : a.abs ≠ 0 := fun h0 => by
      rw [a.zero_sign h0] at hsa; exact hsa rfl
    by_cases hsb : b.sign = true
    · -- false, true
      simp only [hsa, hsb, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i h_cmp
      · rw [h_cmp] at h_cmp_eq
        have h_lt : a.abs.toNat < b.abs.toNat := Nat.compare_eq_lt.mp h_cmp_eq.symm
        rw [Azurite.AzNat.toInt_toAzInt, AzNat.toNat_sub]
        omega
      · rw [h_cmp] at h_cmp_eq
        have h_eq : a.abs.toNat = b.abs.toNat := Nat.compare_eq_eq.mp h_cmp_eq.symm
        rw [toInt_zero]; omega
      · rw [h_cmp] at h_cmp_eq
        have h_gt : b.abs.toNat < a.abs.toNat := Nat.compare_eq_gt.mp h_cmp_eq.symm
        have h_sub_ne : a.abs - b.abs ≠ 0 := by
          intro hc
          have : (a.abs - b.abs).toNat = 0 := by rw [hc]; rfl
          rw [AzNat.toNat_sub] at this; omega
        rw [toInt_mkNonzero_false _ h_sub_ne, AzNat.toNat_sub]
        omega
    · -- false, false
      simp only [hsa, hsb, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      have h_sum_ne : a.abs + b.abs ≠ 0 := by
        intro hc
        have : (a.abs + b.abs).toNat = 0 := by rw [hc]; rfl
        rw [AzNat.toNat_add] at this
        have : a.abs.toNat = 0 := by omega
        exact hanz (AzNat.toNat_injective (by rw [this, AzNat.toNat_zero]))
      rw [toInt_mkNonzero_false _ h_sum_ne, AzNat.toNat_add]
      push_cast; ring

/-- `ofInt`-version of `toInt_add`.
@isnad1 id=eq.0h2v.s4.38874710eb5d from=translated src=- shape=0438c7a3 vocab=ef8299f7
-/
theorem ofInt_add (i j : Int) : ofInt (i + j) = ofInt i + ofInt j := by
  have h : (ofInt (i + j)).toInt = (ofInt i + ofInt j).toInt := by
    rw [toInt_ofInt, toInt_add, toInt_ofInt, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

/-- Correctness of `AzInt.neg`.
@isnad1 id=eq.0h1v.s3.a1f9a6eab4dc from=translated src=- shape=5a02da31 vocab=396a8c3e
-/
@[simp] theorem toInt_neg (z : AzInt) : (-z).toInt = -z.toInt := by
  show (neg z).toInt = -z.toInt
  unfold neg
  by_cases h : z.abs = 0
  · have h_z : z.toInt = 0 := by
      show (if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int)) = 0
      rw [h]; simp
    rw [h_z, neg_zero]
    unfold mkNorm; simp [h]; rfl
  · cases hs : z.sign
    · rw [Bool.not_false, toInt_mkNorm_true]
      show _ = -(if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int))
      rw [hs]; simp
    · rw [Bool.not_true, toInt_mkNorm_false _ h]
      show _ = -(if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int))
      rw [hs]; simp

/-- `ofInt`-version of `toInt_neg`.
@isnad1 id=eq.0h1v.s3.d0ed3d9fb663 from=translated src=- shape=5a02da31 vocab=c5d95cfe
-/
theorem ofInt_neg (i : Int) : ofInt (-i) = -ofInt i := by
  have h : (ofInt (-i)).toInt = (-ofInt i).toInt := by
    rw [toInt_ofInt, toInt_neg, toInt_ofInt]
  have := congrArg ofInt h
  rwa [ofInt_toInt, ofInt_toInt] at this

end Azurite.AzInt
