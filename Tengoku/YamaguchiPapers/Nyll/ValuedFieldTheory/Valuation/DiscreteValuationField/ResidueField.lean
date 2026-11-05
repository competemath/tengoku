/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residue-field API for local maps

This file adds reusable local-ring residue-field lemmas that are used by the
Henselian and unramified parts of the DVF library.  It keeps mathlib's
`IsLocalRing.ResidueField.map` and `IsLocalRing.residue` as the primary
objects.
-/

namespace ValuationTheory

noncomputable section

universe u v w

namespace DiscreteValuationField
namespace ResidueField

variable {R : Type u} {S : Type v} {T : Type w}

section LocalRing

variable [CommRing R] [IsLocalRing R]

/-- Equality in the residue field is equality modulo the maximal ideal.
@isnad1 id=iff.0h3v.s8.9c9ac7280400 from=translated src=- shape=553f29f6 vocab=575e4663
-/
theorem residue_eq_residue_iff_sub_mem_maximalIdeal (x y : R) :
    IsLocalRing.residue R x = IsLocalRing.residue R y ↔
      x - y ∈ IsLocalRing.maximalIdeal R := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]

end LocalRing

section FieldLift

variable [CommRing R] [IsLocalRing R] [Field S]
variable (f : R →+* S) [IsLocalHom f]

end FieldLift

section LocalHom

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable (f : R →+* S) [IsLocalHom f]

/-- A local homomorphism pulls back the target maximal ideal to the source
maximal ideal.
@isnad1 id=eq.0h3v.s7.eeebfaf2aa94 from=translated src=- shape=f0bd6817 vocab=b094da4a
-/
theorem comap_maximalIdeal_eq :
    (IsLocalRing.maximalIdeal S).comap f = IsLocalRing.maximalIdeal R :=
  IsLocalRing.maximalIdeal_comap f

/-- A local homomorphism induces an injective map on residue fields.
@isnad1 id=injectiv.0h3v.s7.1458658fca09 from=translated src=- shape=6182662a vocab=1f4489a6
-/
theorem map_injective :
    Function.Injective (IsLocalRing.ResidueField.map f) := by
  intro x y hxy
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  rw [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.map_residue] at hxy
  rw [residue_eq_residue_iff_sub_mem_maximalIdeal]
  have hsubS : f (r - s) ∈ IsLocalRing.maximalIdeal S := by
    rw [map_sub]
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := S) (f r) (f s)).1 hxy
  have hpre : r - s ∈ (IsLocalRing.maximalIdeal S).comap f := hsubS
  rwa [comap_maximalIdeal_eq f] at hpre

/-- A residue-field map induced by a local homomorphism has trivial kernel.
@isnad1 id=iff.0h4v.s8.73f92e12089c from=translated src=- shape=527132d3 vocab=a6fd8c83
-/
theorem map_eq_zero_iff (x : IsLocalRing.ResidueField R) :
    IsLocalRing.ResidueField.map f x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact map_injective f (by simpa using hx)
  · intro hx
    rw [hx, map_zero]

/-- The residue-field isomorphism induced by a surjective residue-field map
coming from a local homomorphism.-/
noncomputable def ringEquivOfSurjective
    (hsurj : Function.Surjective (IsLocalRing.ResidueField.map f)) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map f)
    ⟨map_injective f, hsurj⟩

/-- The residue-ring equivalence induced by a surjective map evaluates by that map.
@isnad1 id=eq.1h4v.s9.51ef37f438d0 from=translated src=- shape=6ed24566 vocab=219ad544
-/
@[simp]
theorem ringEquivOfSurjective_apply
    (hsurj : Function.Surjective (IsLocalRing.ResidueField.map f))
    (x : IsLocalRing.ResidueField R) :
    ringEquivOfSurjective f hsurj x =
      IsLocalRing.ResidueField.map f x :=
  rfl

end LocalHom

section Algebra

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- For a local algebra map, mathlib's residue-field algebra map agrees with
the residue-field map induced by the structure homomorphism.
@isnad1 id=eq.0h2v.s7.ab71859bc61a from=translated src=- shape=0c35a7c1 vocab=8bb62ede
-/
theorem algebraMap_eq_map_algebraMap :
    algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) =
      IsLocalRing.ResidueField.map (algebraMap R S) := by
  ext x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  simp [IsLocalRing.ResidueField.map_residue,
    IsLocalRing.ResidueField.algebraMap_residue]

/-- The residue-field map induced by a local algebra map is injective.
@isnad1 id=injectiv.0h2v.s8.38998bb93f9b from=translated src=- shape=72bcbe37 vocab=3a9a54b5
-/
theorem map_algebraMap_injective :
    Function.Injective
      (IsLocalRing.ResidueField.map (algebraMap R S)) :=
  map_injective (algebraMap R S)

end Algebra

section AlgEquiv

variable [CommRing T] [IsLocalRing T]
variable [CommRing R] [IsLocalRing R] [Algebra T R]
variable [CommRing S] [IsLocalRing S] [Algebra T S]
variable [IsLocalHom (algebraMap T R)] [IsLocalHom (algebraMap T S)]

/-- A local algebra equivalence induces an algebra equivalence on residue
fields over the base residue field.-/
noncomputable def algEquivOfAlgEquiv
    (e : R ≃ₐ[T] S) :
    IsLocalRing.ResidueField R ≃ₐ[IsLocalRing.ResidueField T]
      IsLocalRing.ResidueField S := by
  letI : IsLocalHom (e.toRingEquiv : R →+* S) :=
    IsLocalHom.of_surjective (e.toRingEquiv : R →+* S) e.surjective
  letI : IsLocalHom (e.symm.toRingEquiv : S →+* R) :=
    IsLocalHom.of_surjective (e.symm.toRingEquiv : S →+* R) e.symm.surjective
  exact
    { IsLocalRing.ResidueField.mapEquiv e.toRingEquiv with
      commutes' := by
        intro x
        obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
        simp [IsLocalRing.ResidueField.algebraMap_residue,
          IsLocalRing.ResidueField.map_residue, e.commutes t] }

/-- The residue-field equivalence induced by an algebra equivalence acts through
residue representatives.
@isnad1 id=eq.0h5v.s9.005a5a5624ad from=translated src=- shape=c1683fbf vocab=2d354ca4
-/
@[simp]
theorem algEquivOfAlgEquiv_apply
    (e : R ≃ₐ[T] S)
    (x : IsLocalRing.ResidueField R) :
    algEquivOfAlgEquiv e x =
      IsLocalRing.ResidueField.map e.toRingEquiv x :=
  rfl

/-- The inverse induced residue equivalence agrees with the inverse quotient-map equivalence.
@isnad1 id=eq.0h5v.s9.0752a435eaf6 from=translated src=- shape=dc2a2dc2 vocab=7a98eea6
-/
theorem algEquivOfAlgEquiv_symm_apply_eq_mapEquiv
    (e : R ≃ₐ[T] S)
    (x : IsLocalRing.ResidueField S) :
    (algEquivOfAlgEquiv e).symm x =
      IsLocalRing.ResidueField.mapEquiv e.symm.toRingEquiv x :=
  rfl

/-- The induced residue equivalence sends the residue of an integral element to
its transported residue.
@isnad1 id=eq.0h5v.s9.b0998a5c9a48 from=translated src=- shape=a98876de vocab=1710526a
-/
@[simp]
theorem algEquivOfAlgEquiv_apply_residue
    (e : R ≃ₐ[T] S) (x : R) :
    algEquivOfAlgEquiv e (IsLocalRing.residue R x) =
      IsLocalRing.residue S (e x) := by
  let : IsLocalHom (e.toRingEquiv : R →+* S) :=
    IsLocalHom.of_surjective (e.toRingEquiv : R →+* S) e.surjective
  change IsLocalRing.ResidueField.map e.toRingEquiv
      (IsLocalRing.residue R x) = IsLocalRing.residue S (e x)
  rfl

/-- The inverse induced residue equivalence sends residues back along the inverse
algebra equivalence.
@isnad1 id=eq.0h5v.s9.02d12c15d2db from=translated src=- shape=1bab2118 vocab=2c746c58
-/
@[simp]
theorem algEquivOfAlgEquiv_symm_apply_residue
    (e : R ≃ₐ[T] S) (x : S) :
    (algEquivOfAlgEquiv e).symm (IsLocalRing.residue S x) =
      IsLocalRing.residue R (e.symm x) := by
  let : IsLocalHom (e.symm.toRingEquiv : S →+* R) :=
    IsLocalHom.of_surjective (e.symm.toRingEquiv : S →+* R) e.symm.surjective
  rw [algEquivOfAlgEquiv_symm_apply_eq_mapEquiv]
  change IsLocalRing.ResidueField.map e.symm.toRingEquiv
      (IsLocalRing.residue S x) = IsLocalRing.residue R (e.symm x)
  rfl

/-- Passing to residue fields commutes with inversion of algebra equivalences.
@isnad1 id=eq.0h4v.s8.242eba5ff38c from=translated src=- shape=99178d05 vocab=6ced865a
-/
@[simp]
theorem algEquivOfAlgEquiv_symm
    (e : R ≃ₐ[T] S) :
    (algEquivOfAlgEquiv e).symm = algEquivOfAlgEquiv e.symm := by
  ext x
  rfl

/-- The identity algebra equivalence induces the identity on residue fields.
@isnad1 id=eq.0h2v.s8.28a3727de9e2 from=translated src=- shape=ac5db100 vocab=8018f0a3
-/
@[simp]
theorem algEquivOfAlgEquiv_refl :
    algEquivOfAlgEquiv (AlgEquiv.refl : R ≃ₐ[T] R) =
      (AlgEquiv.refl :
        IsLocalRing.ResidueField R ≃ₐ[IsLocalRing.ResidueField T]
          IsLocalRing.ResidueField R) := by
  ext x
  simp [algEquivOfAlgEquiv]

/-- Residue-field equivalences respect composition of algebra equivalences.
@isnad1 id=eq.0h6v.s9.5a10baceff89 from=translated src=- shape=73b71e84 vocab=e9320e51
-/
@[simp]
theorem algEquivOfAlgEquiv_trans
    {U : Type*} [CommRing U] [IsLocalRing U] [Algebra T U]
    [IsLocalHom (algebraMap T U)]
    (eRS : R ≃ₐ[T] S) (eSU : S ≃ₐ[T] U) :
    (algEquivOfAlgEquiv eRS).trans (algEquivOfAlgEquiv eSU) =
      algEquivOfAlgEquiv (eRS.trans eSU) := by
  ext x
  rw [algEquivOfAlgEquiv]
  exact congr_arg (fun f => f x)
    (IsLocalRing.ResidueField.mapEquiv_trans
      eRS.toRingEquiv eSU.toRingEquiv).symm

end AlgEquiv

end ResidueField
end DiscreteValuationField

end

end ValuationTheory
