/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude, Codex
-/
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.RingTheory.Flat.Basic
import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.Localization.LocalizationLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fraction fields of partial localizations

Let `A` be a domain over a field `k`, and let `C ⊇ k` be a field with `C ⊗[k] A` a domain.
The partial localization `C ⊗[k] Frac(A)` is then a domain with the same fraction field as
`C ⊗[k] A`, compatibly with the canonical maps (`isDomain_and_exists_tensorFractionEquiv`).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). An input of the genus argument for
Hrushovski–Weil curves.
-/

namespace AclGeom

open TensorProduct

noncomputable section

section TensorFractionFields

variable {k C A : Type*} [Field k] [Field C] [CommRing A] [IsDomain A]
  [Algebra k C] [Algebra k A] [IsDomain (C ⊗[k] A)]

/-- Localizing before or after extending constants gives the same fraction field, and the
partial localization `C ⊗[k] Frac(A)` is a domain.
@isnad1 id=and.0h3v.s15.3dd76f27c686 from=translated src=- shape=fd8aa61c vocab=24d864f7
-/
theorem isDomain_and_exists_tensorFractionEquiv :
    IsDomain (C ⊗[k] FractionRing A) ∧
      ∃ e : FractionRing (C ⊗[k] FractionRing A) ≃ₐ[C] FractionRing (C ⊗[k] A),
        ∀ (c : C) (a : A), e (algebraMap (C ⊗[k] FractionRing A)
          (FractionRing (C ⊗[k] FractionRing A)) (c ⊗ₜ[k] algebraMap A (FractionRing A) a)) =
          algebraMap (C ⊗[k] A) (FractionRing (C ⊗[k] A)) (c ⊗ₜ[k] a) := by
  let R := C ⊗[k] A
  let B := C ⊗[k] FractionRing A
  let T := FractionRing R
  let j : R →ₐ[C] B := Algebra.TensorProduct.map (AlgHom.id C C)
    (IsScalarTower.toAlgHom k A (FractionRing A))
  let _ : Algebra R B := j.toAlgebra
  let _ : IsScalarTower C R B := IsScalarTower.of_algebraMap_eq fun c ↦ (j.commutes c).symm
  let S : Submonoid R := (nonZeroDivisors A).map
    (Algebra.TensorProduct.includeRight : A →ₐ[k] R)
  have _ : IsLocalization S B :=
    IsLocalization.tensorProduct_tensorProduct_right k C (nonZeroDivisors A) (FractionRing A)
      (by
        apply RingHom.ext
        intro a
        rfl)
  have hincl : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[k] R) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k C).injective
  have hS : S ≤ nonZeroDivisors R := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hincl).mpr
      (nonZeroDivisors.ne_zero ha))
  have hdom : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hS
  refine ⟨hdom, ?_⟩
  let f : R →ₐ[C] T := IsScalarTower.toAlgHom C R T
  have hunit : ∀ s : S, IsUnit (f s) := by
    rintro ⟨_, a, ha, rfl⟩
    apply IsUnit.mk0
    change algebraMap R T (Algebra.TensorProduct.includeRight a) ≠ 0
    exact (map_ne_zero_iff _ (IsFractionRing.injective R T)).mpr
      ((map_ne_zero_iff _ hincl).mpr (nonZeroDivisors.ne_zero ha))
  let l : B →ₐ[C] T := IsLocalization.liftAlgHom (M := S) (f := f) hunit
  let _ : Algebra B T := l.toAlgebra
  have hl (r : R) : l (algebraMap R B r) = algebraMap R T r := IsLocalization.lift_eq hunit r
  let _ : IsScalarTower C B T := IsScalarTower.of_algebraMap_eq fun c ↦ (l.commutes c).symm
  let _ : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun r ↦ (hl r).symm
  have _ : IsFractionRing B T :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (M := S) B T
  let e : FractionRing B ≃ₐ[B] T := IsLocalization.algEquiv (nonZeroDivisors B) _ _
  refine ⟨e.restrictScalars C, fun c a ↦ ?_⟩
  change e (algebraMap B (FractionRing B) (j (c ⊗ₜ[k] a))) = _
  rw [e.commutes]
  exact hl (c ⊗ₜ[k] a)

end TensorFractionFields

end

end AclGeom
