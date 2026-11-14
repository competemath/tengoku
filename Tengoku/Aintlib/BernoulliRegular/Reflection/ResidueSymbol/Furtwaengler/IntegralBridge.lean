/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Aintlib.BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ConcreteSetup
public import Tengoku.Aintlib.BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerCongruence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integral target bridge for Stickelberger Gauss sums

This file moves the concrete Furtwängler Gauss sums from the field target `R'`
to the ring of integers `𝓞 R'`.  The digit-sum congruence is measured at the
concrete prime ideal `Q : Ideal (𝓞 R')`, so later Layer 2 arguments need the
same character values and Gauss sum as actual algebraic integers.
-/

@[expose] public section
namespace Tengoku.Aintlib end Tengoku.Aintlib open Tengoku.Aintlib 
noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : ConcreteStickelbergerSetup ℓ p k K R')

/-- Unit form of the integral `p`-th root, for constructing multiplicative
characters valued in `𝓞 R'`.-/
noncomputable def zeta_p_int_unit : (𝓞 R')ˣ :=
  (S.zeta_p_int_isPrimitiveRoot.isUnit (Fact.out : Nat.Prime p).ne_zero).unit

/-- The underlying ring element of the integral root-of-unity unit.
@isnad1 id=eq.0h6v.s7.a0c3dc41ce9e from=translated src=- shape=eca606c0 vocab=85d27baf
-/
@[simp]
theorem zeta_p_int_unit_coe : (S.zeta_p_int_unit : 𝓞 R') = S.zeta_p_int := by
  simp [zeta_p_int_unit]

/-- The integral unit lift maps back to the selected field unit value.
@isnad1 id=eq.0h6v.s8.c73f4806cf41 from=translated src=- shape=9d7a2d41 vocab=d5288a12
-/
@[simp]
theorem algebraMap_zeta_p_int_unit :
    algebraMap (𝓞 R') R' (S.zeta_p_int_unit : 𝓞 R') = (S.zeta_p : R'ˣ) := by
  simp [S.algebraMap_zeta_p_int]

/-- The unit lift of `ζ_p` reduces to the selected finite-field root.
@isnad1 id=eq.0h6v.s8.90391448a3ba from=translated src=- shape=24569260 vocab=e6c0185e
-/
@[simp]
theorem residueMap_zeta_p_int_unit :
    S.residueMap (S.zeta_p_int_unit : 𝓞 R') = (S.zeta_k : k) := by
  rw [S.zeta_p_int_unit_coe]
  exact S.residueMap_zeta_p_int

/-- The unit lift of `ζ_p` remains primitive.
@isnad1 id=isprimit.0h6v.s7.5b39cc81e81b from=translated src=- shape=a60de1e5 vocab=1aab0b70
-/
theorem zeta_p_int_unit_isPrimitiveRoot : IsPrimitiveRoot S.zeta_p_int_unit p := by
  simpa [zeta_p_int_unit] using
    S.zeta_p_int_isPrimitiveRoot.isUnit_unit (Fact.out : Nat.Prime p).ne_zero

/-- The residue character with values in the ring of integers.-/
noncomputable def residueCharInt : MulChar k (𝓞 R') :=
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  residueMulChar S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

/-- Unit-valued form of the integral residue character.-/
noncomputable def residueCharIntUnitHom : kˣ →* (𝓞 R')ˣ :=
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  residueUnitHom S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot

/-- On units, the integral residue character is the unit-group hom.
@isnad1 id=eq.0h7v.s9.5bb708c49e58 from=translated src=- shape=c429d8f1 vocab=41815ad9
-/
@[simp]
theorem residueCharInt_apply_unit (x : kˣ) :
    S.residueCharInt (x : k) = (S.residueCharIntUnitHom x : 𝓞 R') := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  simp [residueCharInt, residueCharIntUnitHom, residueMulChar]

/-- The unit-valued integral residue character has exponent dividing `p`.
@isnad1 id=eq.0h7v.s9.634c9b014a27 from=translated src=- shape=a00ee700 vocab=8f8b81b7
-/
theorem residueCharIntUnitHom_pow_p (x : kˣ) :
    S.residueCharIntUnitHom x ^ p = 1 := by
  apply Units.ext
  change ((S.residueCharIntUnitHom x : (𝓞 R')ˣ) : 𝓞 R') ^ p = (1 : 𝓞 R')
  rw [← S.residueCharInt_apply_unit x]
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  simp only [ConcreteStickelbergerSetup.residueCharInt]
  exact residueMulChar_pow_eq_one S.zeta_k S.hzeta_k S.hdiv S.zeta_p_int_unit
    S.zeta_p_int_unit_isPrimitiveRoot x

/-- Modulo `Q`, the integral residue character is the order-`p`
Teichmüller projection `x ↦ x^((#k - 1) / p)` on residue-field units.
@isnad1 id=eq.0h7v.s8.5b0e2a688054 from=translated src=- shape=09bbbef1 vocab=f3b3f746
-/
theorem residueCharInt_residueMap_eq_pow_d (x : kˣ) :
    S.residueMap (S.residueCharInt (x : k)) =
      (x : k) ^ ((Fintype.card k - 1) / p) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [residueCharInt, residueMulChar_apply_unit, map_pow, S.residueMap_zeta_p_int_unit]
  have h := congrArg (fun u : kˣ => (u : k))
    (Reflection.ResidueSymbol.PowerResidue.zeta_pow_finiteFieldExponent_val
      S.hzeta_k S.hdiv x)
  simpa [Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit] using h

/-- Unit-lift form of `residueCharInt_residueMap_eq_pow_d`: if a residue-field
unit `x` is represented by an integral unit `u`, then reducing
`residueCharInt x` modulo `Q` gives the `d`-th power of the residue of `u`,
where `d = (#k - 1) / p`.
@isnad1 id=eq.1h8v.s9.bf9698c8f248 from=translated src=- shape=47dec6e9 vocab=f3b3f746
-/
theorem residueCharInt_residueMap_eq_pow_d_of_unit
    (x : kˣ) (u : (𝓞 R')ˣ) (hxu : (x : k) = S.residueMap (u : 𝓞 R')) :
    S.residueMap (S.residueCharInt (x : k)) =
      (S.residueMap (u : 𝓞 R')) ^ ((Fintype.card k - 1) / p) := by
  rw [S.residueCharInt_residueMap_eq_pow_d x, ← hxu]

/-- Coercing the integral residue character to `R'` recovers the original
field-valued residue character.
@isnad1 id=eq.0h6v.s8.91afffe64fc9 from=translated src=- shape=02ba74be vocab=cb3d9808
-/
theorem residueCharInt_ringHomComp :
    S.residueCharInt.ringHomComp (algebraMap (𝓞 R') R') = S.residueChar := by
  ext u
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  simp [residueCharInt, residueChar, StickelbergerSetup.residueChar, abstractSetup,
    residueMulChar_apply_unit]

/-- The integral additive character defined by the exponent form
`ψ(x) = ζ_ℓ ^ psiExponent x`.-/
noncomputable def psiInt : AddChar k (𝓞 R') where
  toFun x := S.zeta_ell_int ^ S.psiExponent x
  map_zero_eq_one' := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent 0) =
      algebraMap (𝓞 R') R' (1 : 𝓞 R')
    rw [map_pow, map_one, S.algebraMap_zeta_ell_int]
    simpa [S.psi_pow_form] using (AddChar.map_zero_eq_one S.psi)
  map_add_eq_mul' x y := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent (x + y)) =
      algebraMap (𝓞 R') R'
        (S.zeta_ell_int ^ S.psiExponent x * S.zeta_ell_int ^ S.psiExponent y)
    rw [map_mul, map_pow, map_pow, map_pow, S.algebraMap_zeta_ell_int]
    calc
      S.zeta_ell ^ S.psiExponent (x + y) = S.psi (x + y) := (S.psi_pow_form (x + y)).symm
      _ = S.psi x * S.psi y := AddChar.map_add_eq_mul S.psi x y
      _ = S.zeta_ell ^ S.psiExponent x * S.zeta_ell ^ S.psiExponent y := by
        rw [S.psi_pow_form x, S.psi_pow_form y]

/-- Coercing the integral additive character to `R'` recovers the original
field-valued additive character.
@isnad1 id=eq.0h7v.s8.1eb7af1deb5f from=translated src=- shape=94e908d8 vocab=03b9414a
-/
@[simp]
theorem algebraMap_psiInt (x : k) :
    algebraMap (𝓞 R') R' (S.psiInt x) = S.psi x := by
  change algebraMap (𝓞 R') R' (S.zeta_ell_int ^ S.psiExponent x) = S.psi x
  rw [map_pow, S.algebraMap_zeta_ell_int]
  exact (S.psi_pow_form x).symm

/-- Additive-character form of `algebraMap_psiInt`.
@isnad1 id=eq.0h6v.s8.5dd92c43d83a from=translated src=- shape=d477771d vocab=d594c7b6
-/
theorem psiInt_ringHomComp :
    (algebraMap (𝓞 R') R').toMonoidHom.compAddChar S.psiInt = S.psi := by
  ext x
  exact S.algebraMap_psiInt x

/-- The integral additive character is congruent to `1` modulo the selected
prime `Q`.
@isnad1 id=mem.0h7v.s8.d93c5487b050 from=translated src=- shape=8066f3da vocab=adde4f3d
-/
theorem psiInt_sub_one_mem_Q (x : k) : S.psiInt x - 1 ∈ S.Q := by
  change S.zeta_ell_int ^ S.psiExponent x - 1 ∈ S.Q
  exact zeta_pow_sub_one_mem_of_natCast_mem S.zeta_ell_int_isPrimitiveRoot
    S.hQ (S.psiExponent x)

/-- The concrete Gauss sum as an algebraic integer.-/
noncomputable def gaussSumInt (S : ConcreteStickelbergerSetup ℓ p k K R') (a : ℕ) : 𝓞 R' :=
  _root_.gaussSum (S.residueCharInt ^ a) S.psiInt

/-- Coercing the integral Gauss sum to the field target recovers the
field-valued Gauss sum used in the abstract Stickelberger setup.
@isnad1 id=eq.0h7v.s8.7bc752daf5b8 from=translated src=- shape=fdd29ba8 vocab=6f5a6268
-/
theorem algebraMap_gaussSumInt (a : ℕ) :
    algebraMap (𝓞 R') R' (S.gaussSumInt a) =
      _root_.gaussSum (S.residueChar ^ a) S.psi := by
  simp only [gaussSumInt]
  rw [gaussSum_ringHomComp]
  have hχ :
      (S.residueCharInt ^ a).ringHomComp (algebraMap (𝓞 R') R') =
        S.residueChar ^ a := by
    rw [← MulChar.ringHomComp_pow, S.residueCharInt_ringHomComp]
  rw [hχ, S.psiInt_ringHomComp]

/-- Non-triviality of the integral-valued residue-character powers in the
Stickelberger range.
@isnad1 id=ne.2h7v.s9.591e8905dd67 from=translated src=- shape=e142ab4f vocab=0d0f3868
-/
theorem residueCharInt_pow_ne_one {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.residueCharInt ^ a ≠ 1 := by
  have hfield :
      (S.residueCharInt ^ a).ringHomComp (algebraMap (𝓞 R') R') ≠ 1 := by
    rw [← MulChar.ringHomComp_pow, S.residueCharInt_ringHomComp]
    exact S.abstractSetup.residueChar_pow_ne_one ha₁ ha₂
  exact (MulChar.ringHomComp_ne_one_iff
    (R := k) (R' := 𝓞 R') (R'' := R')
    (f := algebraMap (𝓞 R') R') NumberField.RingOfIntegers.coe_injective).mp hfield

/-- Phase-B containment at the actual integral prime `Q`.
@isnad1 id=mem.2h7v.s8.7ede7db391b1 from=translated src=- shape=878cabc5 vocab=db3a46fe
-/
theorem gaussSumInt_mem_Q {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ∈ S.Q :=
  gaussSum_mem_ideal_of_addChar_sub_one_mem
    (S.residueCharInt_pow_ne_one ha₁ ha₂) S.psiInt S.psiInt_sub_one_mem_Q

/-- Raised Phase-B containment at the actual integral prime `Q`.
@isnad1 id=mem.2h8v.s8.cf30f850ffa0 from=translated src=- shape=82be6184 vocab=36ac2ee4
-/
theorem gaussSumInt_pow_mem_Q_pow {a n : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ n ∈ S.Q ^ n :=
  Ideal.pow_mem_pow (S.gaussSumInt_mem_Q ha₁ ha₂) n

/-- Integral-target exact-order assembly for the digit-sum congruence.
@isnad1 id=and.3h8v.s10.5402843d543c from=translated src=- shape=e637d7ca vocab=6d21d3cd
-/
theorem gaussSumInt_qadic_ord_at_prime_of_leading_congruence
    (a : ℕ) {lead : 𝓞 R'}
    (h_lead_mem :
      lead ∈ S.Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)))
    (h_lead_not_mem_succ :
      lead ∉ S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1))
    (h_congr :
      S.gaussSumInt a - lead ∈
        S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1)) :
    S.gaussSumInt a ∈ S.Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)) ∧
      S.gaussSumInt a ∉
        S.Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1) :=
  exact_mem_pow_of_sub_mem_succ h_lead_mem h_lead_not_mem_succ h_congr

end ConcreteStickelbergerSetup

end Furtwaengler

end BernoulliRegular
-- Tengoku: root names of this library moved to Tengoku.Aintlib so they do not collide with other libraries (generated)
