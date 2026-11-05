/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.AlgebraicGeometry.Morphisms.UniversallyInjective
import Tengoku.Seed.FieldTheory.PurelyInseparable.Exponent
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal injectivity and the actual fraction-field extension

**Status:** a universally injective affine scheme map forces the associated fraction-field
extension to be purely inseparable. Uniqueness of restrictions of algebraic-closure
embeddings and fraction-ring extensionality prove this directly. Named consumer: the
polynomial Frobenius factorization used for the actual normal subgroup's finite Ga cover.
No residue-field comparison or inverse finite map is supplied by a caller (#21).
-/

namespace AclGeom.FiniteGaCover
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- Named consumer: a finite Frobenius cover of the actual normal subgroup.
Universal injectivity of the affine morphism makes its fraction-field extension purely
inseparable. The proof uses embeddings into an algebraic closure, without identifying
residue fields or cancelling a finite map as a monomorphism.-/
theorem isPurelyInseparable_of_universallyInjective
    {R A K L : Type u} [CommRing R] [CommRing A] [Field K] [Field L]
    [Algebra R A] [Algebra A L] [IsFractionRing A L]
    [Algebra R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R A L] [IsScalarTower R K L]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    IsPurelyInseparable K L := by
  apply (isPurelyInseparable_iff_subsingleton_emb K L).mpr
  constructor
  intro φ ψ
  let φA : A →+* AlgebraicClosure L := φ.toRingHom.comp (algebraMap A L)
  let ψA : A →+* AlgebraicClosure L := ψ.toRingHom.comp (algebraMap A L)
  have hR : φA.comp (algebraMap R A) = ψA.comp (algebraMap R A) := by
    apply RingHom.ext
    intro r
    change φ (algebraMap A L (algebraMap R A r)) =
      ψ (algebraMap A L (algebraMap R A r))
    rw [← IsScalarTower.algebraMap_apply R A L, IsScalarTower.algebraMap_apply R K L,
      φ.commutes, ψ.commutes]
  have hp : Spec.map (CommRingCat.ofHom φA) = Spec.map (CommRingCat.ofHom ψA) := by
    have hinj := ((tfae_universallyInjective
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).out 1 2).mp
      (inferInstance : UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    apply hinj (AlgebraicClosure L)
    change Spec.map (CommRingCat.ofHom φA) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom ψA) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hR)
  have hA : φA = ψA := congrArg CommRingCat.Hom.hom (Spec.map_injective hp)
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  exact congrArg (fun f : A →+* AlgebraicClosure L ↦ f a) hA

end
end AclGeom.FiniteGaCover
