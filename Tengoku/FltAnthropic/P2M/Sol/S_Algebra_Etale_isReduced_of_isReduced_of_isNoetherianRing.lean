import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleReducedAux

/--
@isnad1 id=geometri.0h2v.s5.eb3f49802d56 from=translated src=- shape=1471da2c vocab=40c4c95b
-/
theorem geometricallyReduced_specMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S] :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  constructor
  intro K _ y Z fst snd hP
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = y := ⟨Spec.preimage y, Spec.map_preimage y⟩
  letI : Algebra R K := φ.hom.toAlgebra
  have hP' : IsPullback fst snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := hP
  haveI : _root_.IsReduced (K ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] S)
  haveI : _root_.IsReduced (S ⊗[R] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R S K).toRingHom (Algebra.TensorProduct.comm R S K).injective
  haveI : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (S ⊗[R] K))) := (affine_isReduced_iff _).mpr ‹_›
  exact isReduced_of_isOpenImmersion (hP'.isoPullback ≪≫ pullbackSpecIso R S K).hom

end EtaleReducedAux

/--
@isnad1 id=isreduce.0h2v.s6.a75181841958 from=translated src=- shape=4f101e93 vocab=d17d0abb
-/
theorem solution
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [_root_.IsReduced R] [Algebra.Etale R S] :
    _root_.IsReduced S := by
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI := EtaleReducedAux.geometricallyReduced_specMap R S
  have h := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  exact (affine_isReduced_iff (CommRingCat.of S)).mp h
