/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.RingTheory.FractionalIdeal.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fractional Ideals and Base-Ring Equivalences

Material destined for mathlib.

This file defines the image of a fractional ideal under a ring equivalence of
base domains and the induced equivalence of fraction fields. This is the
semilinear counterpart of `FractionalIdeal.map`, which only applies to algebra
maps over a fixed base ring.
-/

open scoped nonZeroDivisors
open IsLocalization

namespace FractionalIdeal

variable {A B K L : Type*}
variable [CommRing A] [CommRing B]
variable [CommRing K] [Algebra A K] [IsFractionRing A K]
variable [CommRing L] [Algebra B L] [IsFractionRing B L]

section Basic

variable (e : A ≃+* B)

/-- The induced fraction-ring equivalence respects scalar multiplication along `e`.
@isnad1 id=eq.0h7v.s9.55801e0606ae from=translated src=- shape=395d2b5f vocab=c828c947
-/
-- Retain this public simp wrapper for compatibility. The upstream application
-- lemma now unfolds its left-hand side to `IsLocalization.map`.
@[simp, nolint simpNF]
theorem ringEquivOfRingEquiv_smul (a : A) (x : K) :
    IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e (a • x) =
      e a • IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]

/--
@isnad1 id=isintege.1h6v.s8.8017dd18f010 from=translated src=- shape=aaa0911e vocab=9e6d3077
-/
theorem isInteger_ringEquivOfRingEquiv {x : K}
    (hx : IsLocalization.IsInteger A x) :
    IsLocalization.IsInteger B
      (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x) := by
  rcases hx with ⟨a, ha⟩
  refine ⟨e a, ?_⟩
  rw [← ha, IsFractionRing.ringEquivOfRingEquiv_algebraMap]

end Basic

section Domains

variable [IsDomain A] [IsDomain B]
variable (e : A ≃+* B)

/-- The underlying submodule of the image of a fractional ideal under a
base-ring equivalence.-/
noncomputable def ringEquivMapSubmodule (I : FractionalIdeal A⁰ K) : Submodule B L where
  carrier := {y | ∃ x : K, x ∈ I ∧
    IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x = y}
  zero_mem' := by
    refine ⟨0, zero_mem I, ?_⟩
    simp
  add_mem' := by
    rintro y z ⟨y', hy', rfl⟩ ⟨z', hz', rfl⟩
    refine ⟨y' + z', (I : Submodule A K).add_mem hy' hz', ?_⟩
    simp
  smul_mem' := by
    rintro b y ⟨y', hy', rfl⟩
    refine ⟨e.symm b • y', ?_, ?_⟩
    · exact (I : Submodule A K).smul_mem (e.symm b) hy'
    · rw [ringEquivOfRingEquiv_smul, e.apply_symm_apply]

/-- The image of a fractional ideal under a ring equivalence of base domains and
the induced equivalence of fraction fields.-/
noncomputable def ringEquivMap (I : FractionalIdeal A⁰ K) : FractionalIdeal B⁰ L where
  val := ringEquivMapSubmodule (K := K) (L := L) e I
  property := by
    rcases I.isFractional with ⟨a, ha, hI⟩
    have hea : e a ∈ B⁰ := by
      have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro hea0
        exact ha0 (e.injective (by simpa using hea0)))
    refine ⟨e a, hea, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simpa only [ringEquivOfRingEquiv_smul] using
      isInteger_ringEquivOfRingEquiv (K := K) (L := L) e (hI x hx)

-- These domain instances occur in `ringEquivMap`'s arguments and cannot be omitted.
set_option linter.unusedSectionVars false in
/--
@isnad1 id=iff.0h7v.s8.8e217ed06c82 from=translated src=- shape=3a5f3a8d vocab=5944ce2f
-/
@[simp]
theorem mem_ringEquivMap {e : A ≃+* B} {I : FractionalIdeal A⁰ K} {y : L} :
    y ∈ ringEquivMap (K := K) (L := L) e I ↔
      ∃ x : K, x ∈ I ∧
        IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x = y :=
  Iff.rfl

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h6v.s8.a5d6769d6e6f from=translated src=- shape=deb2664f vocab=af32e6a8
-/
@[simp]
theorem ringEquivMap_spanSingleton (x : K) :
    ringEquivMap (K := K) (L := L) e (spanSingleton A⁰ x) =
      spanSingleton B⁰ (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases (mem_spanSingleton A⁰).mp hz with ⟨a, rfl⟩
    rw [ringEquivOfRingEquiv_smul]
    exact (mem_spanSingleton B⁰).mpr ⟨e a, rfl⟩
  · intro hy
    rcases (mem_spanSingleton B⁰).mp hy with ⟨b, hb⟩
    refine ⟨e.symm b • x, (mem_spanSingleton A⁰).mpr ⟨e.symm b, rfl⟩, ?_⟩
    rw [ringEquivOfRingEquiv_smul, e.apply_symm_apply]
    exact hb

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h6v.s8.57887efc8a27 from=translated src=- shape=ba553916 vocab=a2a5e4eb
-/
@[simp]
theorem ringEquivMap_coeIdeal (I : Ideal A) :
    ringEquivMap (K := K) (L := L) e (I : FractionalIdeal A⁰ K) =
      (Ideal.map (e : A →+* B) I : FractionalIdeal B⁰ L) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_coeIdeal] at hx ⊢
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨e a, Ideal.mem_map_of_mem (e : A →+* B) ha, ?_⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  · intro hy
    rw [mem_coeIdeal] at hy
    rcases hy with ⟨b, hb, rfl⟩
    rcases (Ideal.mem_map_iff_of_surjective (e : A →+* B) e.surjective).mp hb with
      ⟨a, ha, rfl⟩
    refine ⟨algebraMap A K a, ?_, ?_⟩
    · rw [mem_coeIdeal]
      exact ⟨a, ha, rfl⟩
    · rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
      simp

/--
@isnad1 id=eq.0h7v.s8.40b48b4021d7 from=translated src=- shape=80aa219e vocab=91617ab1
-/
@[simp]
theorem ringEquivMap_mul (I J : FractionalIdeal A⁰ K) :
    ringEquivMap (K := K) (L := L) e (I * J) =
      ringEquivMap (K := K) (L := L) e I *
        ringEquivMap (K := K) (L := L) e J := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine FractionalIdeal.mul_induction_on hx ?_ ?_
    · intro i hi j hj
      rw [map_mul]
      exact FractionalIdeal.mul_mem_mul
        ((mem_ringEquivMap (e := e) (I := I)).mpr ⟨i, hi, rfl⟩)
        ((mem_ringEquivMap (e := e) (I := J)).mpr ⟨j, hj, rfl⟩)
    · intro x y hx hy
      have hxsub :
          IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x ∈
            ((ringEquivMap (K := K) (L := L) e I *
              ringEquivMap (K := K) (L := L) e J : FractionalIdeal B⁰ L) : Submodule B L) :=
        mem_coe.mpr hx
      have hysub :
          IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e y ∈
            ((ringEquivMap (K := K) (L := L) e I *
              ringEquivMap (K := K) (L := L) e J : FractionalIdeal B⁰ L) : Submodule B L) :=
        mem_coe.mpr hy
      have hsum :
          IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e x +
              IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e y ∈
            ((ringEquivMap (K := K) (L := L) e I *
              ringEquivMap (K := K) (L := L) e J : FractionalIdeal B⁰ L) : Submodule B L) :=
        ((ringEquivMap (K := K) (L := L) e I *
          ringEquivMap (K := K) (L := L) e J : FractionalIdeal B⁰ L) : Submodule B L).add_mem
            hxsub hysub
      simpa using mem_coe.mp hsum
  · intro y hy
    refine FractionalIdeal.mul_induction_on hy ?_ ?_
    · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      refine ⟨i * j, FractionalIdeal.mul_mem_mul hi hj, ?_⟩
      simp
    · rintro x y ⟨x', hx', rfl⟩ ⟨y', hy', rfl⟩
      have hxsub : x' ∈ ((I * J : FractionalIdeal A⁰ K) : Submodule A K) :=
        mem_coe.mpr hx'
      have hysub : y' ∈ ((I * J : FractionalIdeal A⁰ K) : Submodule A K) :=
        mem_coe.mpr hy'
      have hsum : x' + y' ∈ ((I * J : FractionalIdeal A⁰ K) : Submodule A K) :=
        ((I * J : FractionalIdeal A⁰ K) : Submodule A K).add_mem hxsub hysub
      refine ⟨x' + y', mem_coe.mp hsum, ?_⟩
      simp

/--
@isnad1 id=eq.0h5v.s7.2a7b056f31c4 from=translated src=- shape=6dbc43e9 vocab=81d8d4b2
-/
@[simp]
theorem ringEquivMap_one :
    ringEquivMap (K := K) (L := L) e (1 : FractionalIdeal A⁰ K) = 1 := by
  rw [← coeIdeal_top, ringEquivMap_coeIdeal, Ideal.map_top, coeIdeal_top]

end Domains

end FractionalIdeal
