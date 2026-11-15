import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CyclotomicUniv

variable (N : ℕ)

abbrev R₀ : Type := AdjoinRoot (cyclotomic N ℤ)

abbrev ζ₀ : R₀ N := AdjoinRoot.root (cyclotomic N ℤ)

def den : R₀ N := (N : R₀ N) * ∏ k ∈ Finset.Ico 1 N, (1 - ζ₀ N ^ k)

abbrev base : Type := Localization.Away (den N)

def ζ : base N := algebraMap (R₀ N) (base N) (ζ₀ N)

/--
@isnad1 id=eq.0h1v.s8.925586324831 from=translated src=- shape=620bcb06 vocab=cf393fbe
-/
theorem algebraMap_ζ₀ : algebraMap (R₀ N) (base N) (ζ₀ N) = ζ N := rfl

/--
@isnad1 id=eq.0h1v.s9.22ab67e7e29c from=translated src=- shape=e1efe867 vocab=cccf19e2
-/
theorem algebraMap_den :
    algebraMap (R₀ N) (base N) (den N) = (N : base N) * ∏ k ∈ Finset.Ico 1 N, (1 - ζ N ^ k) := by
  simp only [den, map_mul, map_natCast, map_prod, map_sub, map_one, map_pow, algebraMap_ζ₀]

section Basic

variable [NeZero N]

/--
@isnad1 id=ne.0h1v.s5.8198dfee00c1 from=translated src=- shape=a023becb vocab=a6f218f1
-/
theorem degree_cyclotomic_ne_zero : (cyclotomic N ℤ).degree ≠ 0 := by
  rw [degree_cyclotomic]
  exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'

/--
@isnad1 id=isdomain.0h1v.s4.218f2c2b707f from=translated src=- shape=a4efea94 vocab=20dbe45e
-/
instance instIsDomainR₀ : IsDomain (R₀ N) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible (NeZero.pos N)).prime

/--
@isnad1 id=injectiv.0h1v.s7.dc01bcfa65ed from=translated src=- shape=28d50696 vocab=f909e371
-/
theorem of_injective : Function.Injective (AdjoinRoot.of (cyclotomic N ℤ)) :=
  AdjoinRoot.of.injective_of_degree_ne_zero (degree_cyclotomic_ne_zero N)

/--
@isnad1 id=charzero.0h1v.s4.9eb923051b18 from=translated src=- shape=a4efea94 vocab=077e6ea4
-/
instance instCharZeroR₀ : CharZero (R₀ N) where
  cast_injective a b h := by
    have h' : AdjoinRoot.of (cyclotomic N ℤ) (a : ℤ) = AdjoinRoot.of (cyclotomic N ℤ) (b : ℤ) := by
      rwa [map_natCast, map_natCast]
    exact_mod_cast of_injective N h'

/--
@isnad1 id=isprimit.0h1v.s4.253c6e047dc3 from=translated src=- shape=9c20510f vocab=ffb2ee41
-/
theorem isPrimitiveRoot_ζ₀ : IsPrimitiveRoot (ζ₀ N) N := by
  have h := AdjoinRoot.isRoot_root (cyclotomic N ℤ)
  rw [map_cyclotomic] at h
  exact (isRoot_cyclotomic_iff (R := R₀ N)).mp h

/--
@isnad1 id=ne.0h1v.s5.f9d9f80c340e from=translated src=- shape=2ca71cb7 vocab=f5c8d78f
-/
theorem den_ne_zero : den N ≠ 0 := by
  rw [den]
  refine mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact sub_ne_zero.mpr (Ne.symm ((isPrimitiveRoot_ζ₀ N).pow_ne_one_of_pos_of_lt (by omega) hk.2))

/--
@isnad1 id=le.0h1v.s7.08c95e23de3c from=translated src=- shape=d4568c78 vocab=1cf7f1f2
-/
theorem powers_den_le : Submonoid.powers (den N) ≤ nonZeroDivisors (R₀ N) :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (den_ne_zero N)

/--
@isnad1 id=isdomain.0h1v.s6.75c14f462e5e from=translated src=- shape=a4efea94 vocab=2e83b9e3
-/
instance instIsDomain : IsDomain (base N) :=
  IsLocalization.isDomain_localization (powers_den_le N)

/--
@isnad1 id=injectiv.0h1v.s8.319268cc1d29 from=translated src=- shape=5d0feda5 vocab=8e8e0266
-/
theorem algebraMap_injective : Function.Injective (algebraMap (R₀ N) (base N)) :=
  IsLocalization.injective (base N) (powers_den_le N)

/--
@isnad1 id=charzero.0h1v.s6.14213f448195 from=translated src=- shape=a4efea94 vocab=d8b85a4c
-/
instance instCharZero : CharZero (base N) where
  cast_injective a b h := by
    have h' : algebraMap (R₀ N) (base N) (a : R₀ N) = algebraMap (R₀ N) (base N) (b : R₀ N) := by
      rwa [map_natCast, map_natCast]
    exact_mod_cast algebraMap_injective N h'

/--
@isnad1 id=isprimit.0h1v.s6.badec9bb7ea3 from=translated src=- shape=9c20510f vocab=9697c7ad
-/
theorem isPrimitiveRoot_ζ : IsPrimitiveRoot (ζ N) N :=
  (isPrimitiveRoot_ζ₀ N).map_of_injective (algebraMap_injective N)

omit [NeZero N] in
/--
@isnad1 id=isunit.0h1v.s8.4876308588f6 from=translated src=- shape=3a2dcdba vocab=419d4848
-/
theorem isUnit_den : IsUnit (algebraMap (R₀ N) (base N) (den N)) :=
  IsLocalization.Away.algebraMap_isUnit (den N)

omit [NeZero N] in

/--
@isnad1 id=isunit.0h1v.s7.4de2d6ad8d1f from=translated src=- shape=1147a29b vocab=74c0469b
-/
theorem isUnit_natCast : IsUnit (N : base N) :=
  isUnit_of_dvd_unit (Dvd.intro _ (algebraMap_den N).symm) (isUnit_den N)

omit [NeZero N] in

/--
@isnad1 id=isunit.1h2v.s7.3715dd02e3ad from=translated src=- shape=c1547a6f vocab=79134766
-/
theorem isUnit_natCast_of_dvd {ℓ : ℕ} (h : ℓ ∣ N) : IsUnit (ℓ : base N) :=
  isUnit_of_dvd_unit (Nat.cast_dvd_cast h) (isUnit_natCast N)

def ζUnit : (base N)ˣ := ((isPrimitiveRoot_ζ N).isUnit (NeZero.ne N)).unit

/--
@isnad1 id=eq.0h1v.s6.46945c9e856f from=translated src=- shape=e0c473b8 vocab=2ccfccd0
-/
@[simp] theorem val_ζUnit : (ζUnit N : base N) = ζ N := rfl

omit [NeZero N] in

def invNat (ℓ : ℕ) (h : ℓ ∣ N) : base N := ((isUnit_natCast_of_dvd N h).unit⁻¹ : (base N)ˣ)

omit [NeZero N] in
/--
@isnad1 id=eq.1h2v.s8.b7d1764e5de2 from=translated src=- shape=4a7efe98 vocab=2be2577d
-/
theorem natCast_mul_invNat (ℓ : ℕ) (h : ℓ ∣ N) : (ℓ : base N) * invNat N ℓ h = 1 := by
  rw [invNat]
  exact (isUnit_natCast_of_dvd N h).mul_val_inv

omit [NeZero N] in
/--
@isnad1 id=eq.1h2v.s8.a597d5c340e5 from=translated src=- shape=db2ef3c4 vocab=2be2577d
-/
theorem invNat_mul_natCast (ℓ : ℕ) (h : ℓ ∣ N) : invNat N ℓ h * (ℓ : base N) = 1 := by
  rw [mul_comm, natCast_mul_invNat]

end Basic

section Lift

variable {N} [NeZero N] {F : Type*} [Field F] {z : F} (hz : IsPrimitiveRoot z N)
include hz

/--
@isnad1 id=eq.1h3v.s6.be4a2918c3e0 from=translated src=- shape=541bd386 vocab=b302b140
-/
theorem eval₂_cyclotomic_eq_zero : (cyclotomic N ℤ).eval₂ (Int.castRingHom F) z = 0 := by
  rw [eval₂_eq_eval_map, map_cyclotomic_int]
  exact hz.isRoot_cyclotomic (NeZero.pos N)

def lift₀ : R₀ N →+* F := AdjoinRoot.lift (Int.castRingHom F) z (eval₂_cyclotomic_eq_zero hz)

/--
@isnad1 id=eq.1h3v.s6.c02948e05bb9 from=translated src=- shape=23ffc590 vocab=f03ce4f1
-/
@[simp] theorem lift₀_ζ₀ : lift₀ hz (ζ₀ N) = z := AdjoinRoot.lift_root _

/--
@isnad1 id=eq.1h3v.s7.92e72f612fdc from=translated src=- shape=a1dfb456 vocab=e001f453
-/
theorem lift₀_den : lift₀ hz (den N) = (N : F) * ∏ k ∈ Finset.Ico 1 N, (1 - z ^ k) := by
  simp only [den, map_mul, map_natCast, map_prod, map_sub, map_one, map_pow, lift₀_ζ₀]

/--
@isnad1 id=isunit.1h3v.s6.a87f321d9a4d from=translated src=- shape=21e1ec16 vocab=2d121fdf
-/
theorem isUnit_lift₀_den : IsUnit (lift₀ hz (den N)) := by
  rw [lift₀_den, isUnit_iff_ne_zero]
  haveI : NeZero ((N : ℕ) : F) := hz.neZero'
  refine mul_ne_zero (NeZero.ne (N : F)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact sub_ne_zero.mpr (Ne.symm (hz.pow_ne_one_of_pos_of_lt (by omega) hk.2))

def lift : base N →+* F := IsLocalization.Away.lift (den N) (isUnit_lift₀_den hz)

/--
@isnad1 id=eq.1h4v.s9.87d4ca5f5a30 from=translated src=- shape=eb5dfca2 vocab=9e3810ab
-/
@[simp] theorem lift_algebraMap (x : R₀ N) : lift hz (algebraMap (R₀ N) (base N) x) = lift₀ hz x :=
  IsLocalization.Away.lift_eq _ _ _

/--
@isnad1 id=eq.1h3v.s7.6311268b54c3 from=translated src=- shape=23ffc590 vocab=dce2b8bd
-/
@[simp] theorem lift_ζ : lift hz (ζ N) = z := by
  rw [← algebraMap_ζ₀, lift_algebraMap, lift₀_ζ₀]

/--
@isnad1 id=eq.2h4v.s7.e1644766885f from=translated src=- shape=34d1e871 vocab=3265bfbd
-/
theorem lift_invNat (ℓ : ℕ) (h : ℓ ∣ N) : lift hz (invNat N ℓ h) = (ℓ : F)⁻¹ := by
  have h1 : (ℓ : F) * lift hz (invNat N ℓ h) = 1 := by
    have := congrArg (lift hz) (natCast_mul_invNat N ℓ h)
    rwa [map_mul, map_natCast, map_one] at this
  have hℓ : (ℓ : F) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact zero_ne_one h1
  exact (eq_inv_of_mul_eq_one_right h1)

/--
@isnad1 id=injectiv.1h3v.s6.c6800ea6ccfb from=translated src=- shape=7ea60d1e vocab=02d8893d
-/
theorem lift₀_injective [CharZero F] : Function.Injective (lift₀ hz) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih P =>
    rw [lift₀, AdjoinRoot.lift_mk] at hx
    rw [AdjoinRoot.mk_eq_zero, cyclotomic_eq_minpoly hz (NeZero.pos N)]
    refine minpoly.isIntegrallyClosed_dvd (hz.isIntegral (NeZero.pos N)) ?_
    rwa [aeval_def, show algebraMap ℤ F = Int.castRingHom F from RingHom.ext_int _ _]

/--
@isnad1 id=injectiv.1h3v.s7.4af0398e3241 from=translated src=- shape=7ea60d1e vocab=d483f6ef
-/
theorem lift_injective [CharZero F] : Function.Injective (lift hz) := by
  rw [lift, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h; rw [algebraMap_injective N h]
  · intro h; rw [lift₀_injective hz h]

end Lift

end CyclotomicUniv

end
