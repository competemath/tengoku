import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_finite_algebra_specMap_comp_eq_of_isFinite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_finite_algebra_specMap_comp_eq_of_isFinite

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace X5P2

/--
@isnad1 id=eq.0h3v.s6.2eb02fc3a870 from=translated src=- shape=81e9ec55 vocab=09a66081
-/
theorem specMap_ofHom_preimage {R S : Type} [CommRing R] [CommRing S]
    (w : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (Spec.preimage w).hom) = w := by
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/--
@isnad1 id=eq.1h4v.s6.7a78f8aa9362 from=translated src=- shape=f12398e6 vocab=5de93eef
-/
theorem ringHom_eq_of_specMap_eq {R S : Type} [CommRing R] [CommRing S] (φ ψ : R →+* S)
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ := by
  have h2 := Spec.map_inj.mp h
  have h3 := congrArg CommRingCat.Hom.hom h2
  simpa only [CommRingCat.hom_ofHom] using h3

end X5P2

open X5P2 in
/--
@isnad1 id=ex.1h5v.s8.71a50613a996 from=translated src=- shape=2037168b vocab=dcddf7fb
-/
theorem solution
    {B : Type} [CommRing B] {K : Scheme.{0}} (g : K ⟶ Spec (CommRingCat.of B)) [IsFinite g]
    (C : Type) [CommRing C] [Algebra B C] (κ : Spec (CommRingCat.of C) ⟶ K)
    (hκ : κ ≫ g = Scheme.specOver (𝒪 := B) C) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Module.Finite B D)
      (ι : Spec (CommRingCat.of D) ⟶ K) (φ : D →ₐ[B] C),
      ι ≫ g = Scheme.specOver (𝒪 := B) D ∧ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι = κ := by
  classical
  haveI : IsAffine K := isAffine_of_isAffineHom g
  let D : Type := ↑(Γ(K, ⊤))
  let e : K ≅ Spec (CommRingCat.of D) := K.isoSpec
  obtain ⟨β, hβ⟩ : ∃ β : B →+* D, Spec.map (CommRingCat.ofHom β) = e.inv ≫ g := ⟨_, specMap_ofHom_preimage _⟩
  letI : Algebra B D := β.toAlgebra
  have hι : e.inv ≫ g = Spec.map (CommRingCat.ofHom (algebraMap B D)) := hβ.symm

  have hfinI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap B D))) := by
    rw [← hι]; infer_instance
  have hfin : Module.Finite B D := by
    have h := (IsFinite.SpecMap_iff _).mp hfinI
    rwa [CommRingCat.hom_ofHom, RingHom.finite_algebraMap] at h

  obtain ⟨φ, hφ⟩ : ∃ φ : D →+* C, Spec.map (CommRingCat.ofHom φ) = κ ≫ e.hom := ⟨_, specMap_ofHom_preimage _⟩
  have hcomm : φ.comp (algebraMap B D) = algebraMap B C := by
    apply ringHom_eq_of_specMap_eq
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ, ← hι, Category.assoc, e.hom_inv_id_assoc, hκ]
  refine ⟨D, inferInstance, β.toAlgebra, hfin, e.inv, { toRingHom := φ, commutes' := fun b => DFunLike.congr_fun hcomm b },
    hι, ?_⟩
  show Spec.map (CommRingCat.ofHom φ) ≫ e.inv = κ
  rw [hφ, Category.assoc, e.hom_inv_id, Category.comp_id]
