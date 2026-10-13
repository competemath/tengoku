/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
-/
module

public import Tengoku

/-!
# Valuation Subring

Material destined for Mathlib.
-/

@[expose] public section

variable {F : Type*} [Field F]

/--
@isnad1 id=iff.0h4v.s8.0602ba120f32 from=translated src=- shape=28537b3f vocab=a284c374
-/
lemma ValuationSubring.subtype_inj {R : ValuationSubring F} {x y : R} :
    R.subtype x = R.subtype y ↔ x = y :=
  R.subtype_injective.eq_iff

/--
@isnad1 id=eq.1h3v.s8.c9852cf3794e from=translated src=- shape=8027318c vocab=1afa9b9b
-/
theorem ValuationSubring.valued_eq_one_of_isUnit {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : IsUnit x) : Valued.v x.val = 1 := by
  obtain ⟨u, hu⟩ := hx
  apply le_antisymm ((hv.v.mem_valuationSubring_iff _).1 x.2)
  rw [← Valued.v.map_one (R := K), ← Submonoid.coe_one, ← u.mul_inv, hu,
    Submonoid.coe_mul, Valued.v.map_mul]
  nth_rw 2 [← mul_one (Valued.v x.val)]
  exact mul_le_mul_right ((hv.v.mem_valuationSubring_iff _).1 (u⁻¹.val.property)) _

/--
@isnad1 id=isunit.1h3v.s8.b700c9555cdf from=translated src=- shape=568195c0 vocab=1afa9b9b
-/
theorem ValuationSubring.isUnit_of_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring)
    (hx : Valued.v x.val = 1) : IsUnit x := by
  have : IsUnit x.val := by rw [isUnit_iff_ne_zero, ne_eq, ← map_eq_zero hv.v, hx]; aesop
  obtain ⟨u, hu⟩ := this
  have hu_inv_le : Valued.v u⁻¹.val ≤ 1 := by
    rw [← one_mul (Valued.v _), ← hx, ← hu, ← Valued.v.map_mul, u.mul_inv, hu, hx, Valued.v.map_one]
  rw [isUnit_iff_exists]
  exact ⟨⟨u⁻¹.val, hu_inv_le⟩,  ⟨by aesop, by aesop⟩⟩

/--
@isnad1 id=iff.0h3v.s8.2b51adb3ab60 from=translated src=- shape=ec53702f vocab=1afa9b9b
-/
theorem ValuationSubring.isUnit_iff_valued_eq_one {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀] (x : hv.v.valuationSubring) :
    IsUnit x ↔ Valued.v x.val = 1 :=
  ⟨valued_eq_one_of_isUnit x, isUnit_of_valued_eq_one x⟩
