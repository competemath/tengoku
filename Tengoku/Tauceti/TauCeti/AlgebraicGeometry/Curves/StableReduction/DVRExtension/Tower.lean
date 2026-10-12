/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.AlgebraicGeometry.Curves.StableReduction.DVRExtension.Basic

/-!
# Maps and towers of chosen finite DVR extensions

The chosen place in a finite extension of a DVR is part of the data: a field embedding alone does
not say how the corresponding local rings are related. This file therefore packages a compatible
field embedding and local-ring map, with the square between them as an explicit law. These maps
form the category of chosen extensions. It also records the finite separable field towers that
occur between such extensions; these maps are the compatible pieces used by later
common-refinement arguments.

A map is determined by its field component, and conversely a `K`-embedding of the extension
fields under which the chosen places correspond extends uniquely to a map: the local-ring component
is the localisation of the restriction of the field embedding to the integral closures. The
existence of a common refinement for two arbitrary chosen extensions is proved in
`TauCeti.AlgebraicGeometry.Curves.StableReduction.DVRExtension.CommonRefinement`.

## Main declarations

* `TauCeti.FiniteDVRExtension.Hom`: a map of chosen extensions, and the category instance
  `TauCeti.FiniteDVRExtension.finiteDVRExtensionCategory`.
* `TauCeti.FiniteDVRExtension.Hom.comap_prime`: the chosen places correspond under the field
  component of a map.
* `TauCeti.FiniteDVRExtension.Hom.ext_field`: a map is determined by its field component.
* `TauCeti.FiniteDVRExtension.Hom.ofAlgHom`: the map extending a field embedding under which the
  chosen places correspond.
-/

public section

universe u

namespace TauCeti

open CategoryTheory

namespace FiniteDVRExtension

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A map of chosen finite DVR extensions.

`field` embeds the extension fields over `K`, while `localMap` embeds the selected local rings
over `R`. The commutative-square law says that the field embedding restricts to the local-ring map.
The local map is local, so the chosen closed point is respected rather than merely mapping one
subring into another.
-/
structure Hom (E F : FiniteDVRExtension R K) where
  /-- The embedding of the extension fields over `K`. -/
  field : E.extensionField →ₐ[K] F.extensionField
  /-- The map of chosen local rings over `R`. -/
  localMap : E.localRing →ₐ[R] F.localRing
  /-- The field and local-ring maps commute with the fraction maps. -/
  field_local : ∀ x,
    field (algebraMap E.localRing E.extensionField x) =
      algebraMap F.localRing F.extensionField (localMap x)
  /-- The map preserves the chosen maximal ideals. -/
  isLocalHom_localMap : IsLocalHom localMap.toRingHom

attribute [instance] Hom.isLocalHom_localMap
attribute [simp] Hom.field_local

namespace Hom

/-- Two maps are equal when their field and local-ring components agree. -/
lemma ext {E F : FiniteDVRExtension R K} {f g : Hom E F}
    (hfield : f.field = g.field) (hlocal : f.localMap = g.localMap) : f = g := by
  cases f
  cases g
  cases hfield
  cases hlocal
  congr

end Hom

/-- Chosen extensions and their compatible maps form a category over a fixed `R` and `K`. -/
instance finiteDVRExtensionCategory : Category (FiniteDVRExtension R K) where
  Hom := Hom
  id E :=
    { field := AlgHom.id K E.extensionField
      localMap := AlgHom.id R E.localRing
      field_local := fun x ↦ by simp
      isLocalHom_localMap := by
        have h : (AlgHom.id R E.localRing).toRingHom = RingHom.id E.localRing := by
          ext x
          simp
        rw [h]
        exact isLocalHom_id _ }
  comp f g :=
    { field := g.field.comp f.field
      localMap := g.localMap.comp f.localMap
      field_local := fun x ↦ by
        simp only [AlgHom.comp_apply]
        rw [f.field_local x, g.field_local (f.localMap x)]
      isLocalHom_localMap := by
        let _ : IsLocalHom g.localMap.toRingHom := g.isLocalHom_localMap
        let _ : IsLocalHom f.localMap.toRingHom := f.isLocalHom_localMap
        have h : (g.localMap.comp f.localMap).toRingHom =
            g.localMap.toRingHom.comp f.localMap.toRingHom := by
          ext x
          rfl
        rw [h]
        exact RingHom.isLocalHom_comp _ _ }
  id_comp := by
    intro E F f
    apply Hom.ext
    · ext x
      rfl
    · ext x
      rfl
  comp_id := by
    intro E F f
    apply Hom.ext
    · ext x
      rfl
    · ext x
      rfl
  assoc := by
    intro E F G H f g h
    apply Hom.ext
    · ext x
      rfl
    · ext x
      rfl

namespace Hom

variable {E F : FiniteDVRExtension R K}

/-- A map of chosen extensions is determined by its field component. -/
@[ext (iff := false)]
theorem ext_field {f g : E ⟶ F} (h : f.field = g.field) : f = g :=
  Hom.ext h <| AlgHom.ext fun x => IsFractionRing.injective F.localRing F.extensionField <| by
    rw [← f.field_local, ← g.field_local, h]

/-- The map of chosen extensions extending a `K`-embedding `φ` of the extension fields under which
the chosen places correspond. Its local-ring component is the localisation of the restriction of
`φ` to the integral closures. -/
noncomputable def ofAlgHom (φ : E.extensionField →ₐ[K] F.extensionField)
    (hφ : F.prime.comap (φ.restrictScalars R).mapIntegralClosure = E.prime) : E ⟶ F :=
  let ψ : E.integralClosure →ₐ[R] F.localRing :=
    (IsScalarTower.toAlgHom R F.integralClosure F.localRing).comp
      (φ.restrictScalars R).mapIntegralClosure
  have hψ : ∀ y : E.prime.primeCompl, IsUnit (ψ y) := fun y => by
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
      IsLocalization.AtPrime.isUnit_to_map_iff F.localRing F.prime]
    intro h
    exact y.2 (hφ.le (Ideal.mem_comap.mpr h))
  let l : E.localRing →ₐ[R] F.localRing := IsLocalization.liftAlgHom hψ
  have hl : ∀ c, l (algebraMap E.integralClosure E.localRing c) = ψ c := fun c =>
    IsLocalization.lift_eq hψ c
  { field := φ
    localMap := l
    field_local := fun x =>
      RingHom.congr_fun (IsLocalization.ringHom_ext E.prime.primeCompl
        (j := φ.toRingHom.comp (algebraMap E.localRing E.extensionField))
        (k := (algebraMap F.localRing F.extensionField).comp l.toRingHom)
        (RingHom.ext fun c => by
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hl, ψ,
            AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply]
          -- both sides are `φ c`: the algebra maps out of the integral closures are the inclusions
          rfl)) x
    isLocalHom_localMap := by
      refine ((IsLocalRing.local_hom_TFAE _).out 4 1).mp ?_
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal E.prime E.localRing,
        Ideal.map_le_iff_le_comap]
      intro x hx
      rw [← hφ, Ideal.mem_comap] at hx
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hl,
        AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
        IsLocalization.AtPrime.to_map_mem_maximal_iff F.localRing F.prime]
      exact hx }

end Hom

end FiniteDVRExtension

end TauCeti
