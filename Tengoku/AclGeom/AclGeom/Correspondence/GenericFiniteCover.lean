/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.PointwiseFaithfulness
import Tengoku.Seed.RingTheory.Localization.Integral
import Tengoku.Seed.RingTheory.Localization.Away.AdjoinRoot
import Tengoku.Seed.RingTheory.FiniteType
import Tengoku.Seed.AlgebraicGeometry.Group.Affine
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Finite
import Tengoku.Seed.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite maps on actual nonempty opens

**Status:** proved generic criteria (#21). An algebraic finite-type domain extension is
finite and injective after one base localization. Over an ACF base, a dominant finite-type
domain map injective on k-points supplies algebraicity internally. Its actual Spec map is
finite and surjective on nonempty opens, with the actual commuting square. The algebraic
criteria permit independent ring universes; the geometric criterion uses one universe.
Named consumer: `SchemeAffineParameterCover` supplies every premise from its actual action.
-/

namespace AclGeom.GenericFiniteCover
noncomputable section

/-- A finite-type algebraic domain extension becomes finite after one base localization.
 Named consumer: the actual affine-group coefficient morphism on dense opens.-/
theorem exists_finite_away {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    [Algebra.IsAlgebraic R S] (hinj : Function.Injective (algebraMap R S)) :
    ∃ r : R, r ≠ 0 ∧
      (IsLocalization.Away.map (Localization.Away r)
        (Localization.Away (algebraMap R S r)) (algebraMap R S) r).Finite ∧
      Function.Injective (IsLocalization.Away.map (Localization.Away r)
        (Localization.Away (algebraMap R S r)) (algebraMap R S) r) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  obtain ⟨r, hr, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples R s
  refine ⟨r, hr, ?_⟩
  let Rr := Localization.Away r
  let Sr := Localization.Away (algebraMap R S r)
  let f : Rr →+* Sr := IsLocalization.Away.map Rr Sr (algebraMap R S) r
  let : Algebra Rr Sr := f.toAlgebra
  have hf (a : R) : f (algebraMap R Rr a) = algebraMap S Sr (algebraMap R S a) :=
    IsLocalization.map_eq _ a
  have : IsScalarTower R Rr Sr := IsScalarTower.of_algebraMap_eq fun a ↦ (hf a).symm
  have hg (x : S) (hx : x ∈ s) : IsIntegral Rr (algebraMap S Sr x) := by
    have hh : IsIntegral Rr (algebraMap S Sr (r • x)) :=
      ((hint x hx).algebraMap (B := Sr)).tower_top
    apply IsIntegral.of_mul_unit
      (r := IsLocalization.Away.invSelf r)
      (y := algebraMap Rr Sr (algebraMap R Rr r))
    · rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
    · simpa only [Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply R Rr Sr,
        ← IsScalarTower.algebraMap_apply R S Sr, mul_comm] using hh
  have hS (x : S) : IsIntegral Rr (algebraMap S Sr x) := by
    have hx : x ∈ Algebra.adjoin R (s : Set S) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hg x hx
    | algebraMap a =>
      rw [← IsScalarTower.algebraMap_apply R S Sr,
        IsScalarTower.algebraMap_apply R Rr Sr]
      exact isIntegral_algebraMap
    | add x y _ _ hx hy => simpa only [map_add] using hx.add hy
    | mul x y _ _ hx hy => simpa only [map_mul] using hx.mul hy
  have : Algebra.IsIntegral Rr Sr := by
    constructor
    intro x
    obtain ⟨a, ⟨_, n, rfl⟩, rfl⟩ :=
      IsLocalization.exists_mk'_eq (Submonoid.powers (algebraMap R S r)) x
    have hu : IsUnit (algebraMap R Rr (r ^ n)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit r).pow n
    apply IsIntegral.of_mul_unit
      (r := ((hu.unit⁻¹ : Rrˣ) : Rr))
      (y := algebraMap Rr Sr (algebraMap R Rr (r ^ n)))
    · rw [← map_mul]
      have hh : ((hu.unit⁻¹ : Rrˣ) : Rr) * algebraMap R Rr (r ^ n) = 1 := by
        simpa only [hu.unit_spec] using Units.inv_mul hu.unit
      exact (congrArg (algebraMap Rr Sr) hh).trans (map_one _)
    · have he : algebraMap Rr Sr (algebraMap R Rr (r ^ n)) =
          algebraMap S Sr ((algebraMap R S r) ^ n) := by
        rw [← IsScalarTower.algebraMap_apply R Rr Sr,
          IsScalarTower.algebraMap_apply R S Sr, map_pow]
      rw [he, IsLocalization.mk'_spec]
      exact hS a
  have : Algebra.FiniteType R Sr := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R S) inferInstance
  have : Algebra.FiniteType Rr Sr := Algebra.FiniteType.of_restrictScalars_finiteType R Rr Sr
  refine ⟨Algebra.IsIntegral.finite, ?_⟩
  apply (IsLocalization.Away.map_injective_iff Sr (algebraMap R S) r).mpr
  intro a ha
  have hz : a = 0 := hinj (ha.trans (map_zero _).symm)
  exact ⟨0, by rw [hz]; simp⟩

end
end AclGeom.GenericFiniteCover

namespace AclGeom.GenericFiniteCover
noncomputable section

/-- A dominant finite-type domain map injective on ACF points is finite over a dense
 principal open. Named consumer: the actual affine-group coordinate map.-/
theorem exists_finite_away_of_injective_points {k B A : Type*} [Field k] [IsAlgClosed k]
    [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra k B] [Algebra k A] [Algebra.FiniteType k A]
    (ψ : B →ₐ[k] A) (hinj : Function.Injective ψ)
    (hpoints : Function.Injective (fun φ : A →ₐ[k] k ↦ φ.comp ψ)) :
    ∃ r : B, r ≠ 0 ∧
      (IsLocalization.Away.map (Localization.Away r)
        (Localization.Away (ψ r)) ψ.toRingHom r).Finite ∧
      Function.Injective (IsLocalization.Away.map (Localization.Away r)
        (Localization.Away (ψ r)) ψ.toRingHom r) := by
  let : Algebra B A := ψ.toAlgebra
  have : IsScalarTower k B A := IsScalarTower.of_algHom ψ
  let E := FractionRing A
  let F := FractionRing B
  let ι : B →ₐ[k] E := (IsScalarTower.toAlgHom k A E).comp ψ
  have hι : Function.Injective ι := (IsFractionRing.injective A E).comp hinj
  have : IsScalarTower B A E := inferInstance
  let η : F →ₐ[k] E := IsFractionRing.liftAlgHom hι
  let : Algebra F E := η.toAlgebra
  have : IsScalarTower B F E := IsScalarTower.of_algebraMap_eq fun x ↦ by
    exact (IsFractionRing.lift_algebraMap hι x).symm
  have : Algebra.IsAlgebraic F E :=
    isAlgebraic_fractionRing_of_injective_points (B := B) (A := A)
      (C := F) (E := E) hpoints
  have : Algebra.IsAlgebraic B E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := B) (K := F) (C := E)).mpr inferInstance
  have : Algebra.IsAlgebraic B A := Algebra.IsAlgebraic.of_injective
    (IsScalarTower.toAlgHom B A E) (IsFractionRing.injective A E)
  have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType k B A
  exact exists_finite_away hinj

end
end AclGeom.GenericFiniteCover

namespace AclGeom.GenericFiniteCover
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u

/-- A dominant affine chart map injective on ACF points restricts to a finite surjective
 map between actual nonempty opens. Named consumer: the actual affine-action coordinates.-/
theorem exists_finite_open_square {k B A : Type u} [Field k] [IsAlgClosed k]
    [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
    [Algebra k B] [Algebra k A] [Algebra.FiniteType k A]
    (ψ : B →ₐ[k] A) (hinj : Function.Injective ψ)
    (hpoints : Function.Injective (fun φ : A →ₐ[k] k ↦ φ.comp ψ))
    (X : Over (Spec (.of k)))
    (g : (Spec (.of A)).asOver (Spec (.of k)) ⟶ X) [IsOpenImmersion g.left]
    (f : X ⟶ (Spec (.of B)).asOver (Spec (.of k)))
    (hψ : (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op = g ≫ f) :
    ∃ (U T : Over (Spec (.of k))) (jU : U ⟶ X)
      (jT : T ⟶ (Spec (.of B)).asOver (Spec (.of k))) (π : U ⟶ T),
      IsOpenImmersion jU.left ∧ IsOpenImmersion jT.left ∧
      Nonempty U.left ∧ Nonempty T.left ∧ IsFinite π.left ∧ Surjective π.left ∧
      jU ≫ f = π ≫ jT := by
  obtain ⟨r, hr, hfinite, hinjloc⟩ := exists_finite_away_of_injective_points ψ hinj hpoints
  let Rr := Localization.Away r
  let Sr := Localization.Away (ψ r)
  have : IsDomain Rr := IsLocalization.Away.isDomain Rr hr
  have hψr : ψ r ≠ 0 := by
    intro h
    exact hr (hinj (h.trans (map_zero _).symm))
  have : IsDomain Sr := IsLocalization.Away.isDomain Sr hψr
  let U := (Spec (.of Sr)).asOver (Spec (.of k))
  let T := (Spec (.of Rr)).asOver (Spec (.of k))
  let iA : U ⟶ (Spec (.of A)).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k A Sr)).op
  let iB : T ⟶ (Spec (.of B)).asOver (Spec (.of k)) :=
    (algSpec (.of k)).map (CommAlgCat.ofHom (IsScalarTower.toAlgHom k B Rr)).op
  let φ : Rr →ₐ[k] Sr := IsLocalization.Away.mapₐ Rr Sr ψ r
  let π : U ⟶ T := (algSpec (.of k)).map (CommAlgCat.ofHom φ).op
  have hiA : IsOpenImmersion iA.left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A Sr)))
    infer_instance
  have hiB : IsOpenImmersion iB.left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B Rr)))
    infer_instance
  have hπfinite : IsFinite π.left := by
    change IsFinite (Spec.map (CommRingCat.ofHom φ.toRingHom))
    exact (IsFinite.SpecMap_iff _).mpr hfinite
  have hπsurj : Surjective π.left := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap φ.toRingHom)
    exact hfinite.to_isIntegral.comap_surjective hinjloc
  have hcomm : iA ≫ (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op = π ≫ iB := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (algebraMap A Sr)) ≫
        Spec.map (CommRingCat.ofHom ψ.toRingHom) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B Rr))
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    ext b
    change algebraMap A Sr (ψ b) = φ (algebraMap B Rr b)
    have hy : Submonoid.powers r ≤ (Submonoid.powers (ψ r)).comap ψ.toRingHom := by
      rintro z ⟨n, rfl⟩
      exact ⟨n, (map_pow ψ r n).symm⟩
    exact (IsLocalization.map_eq (M := Submonoid.powers r)
      (T := Submonoid.powers (ψ r)) (S := Rr) (Q := Sr) (g := ψ.toRingHom) hy b).symm
  have hU : Nonempty U.left := by
    change Nonempty (PrimeSpectrum Sr)
    exact ⟨⟨⊥, inferInstance⟩⟩
  have hT : Nonempty T.left := by
    change Nonempty (PrimeSpectrum Rr)
    exact ⟨⟨⊥, inferInstance⟩⟩
  refine ⟨U, T, iA ≫ g, iB, π, ?_, hiB, hU, hT, hπfinite, hπsurj, ?_⟩
  · change IsOpenImmersion (iA.left ≫ g.left)
    infer_instance
  · have hh : iA ≫ (g ≫ f) =
        iA ≫ (algSpec (.of k)).map (CommAlgCat.ofHom ψ).op :=
      congrArg (fun m : (Spec (.of A)).asOver (Spec (.of k)) ⟶
        (Spec (.of B)).asOver (Spec (.of k)) ↦ iA ≫ m) hψ.symm
    exact (Category.assoc iA g f).trans (hh.trans hcomm)

end
end AclGeom.GenericFiniteCover
