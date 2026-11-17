import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_surjective_and_flat_and_quasiCompact_of_isPullback_specMap_algebraMap_of_field

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FFSquare

/--
@isnad1 id=and.0h2v.s7.ef901d2ae063 from=translated src=- shape=b382480e vocab=b5d51f40
-/
theorem specMap_algebraMap {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) := by
  refine ⟨⟨fun x => ?_⟩, ?_, inferInstance⟩
  · haveI : Subsingleton ↥(Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
    obtain ⟨y⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of Ω)))
    exact ⟨y, Subsingleton.elim _ _⟩
  · rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    change (algebraMap F Ω).Flat
    rw [RingHom.Flat]
    exact inferInstance

/--
@isnad1 id=and.1h7v.s7.c0e29de9228c from=translated src=- shape=ffcf897f vocab=26b91bad
-/
theorem main {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    {X X₀ : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of Ω)} {f₀ : X₀ ⟶ Spec (CommRingCat.of F)} (r : X ⟶ X₀)
    (hr : IsPullback r fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))) :
    Surjective r ∧ Flat r ∧ QuasiCompact r := by
  obtain ⟨h1, h2, h3⟩ := specMap_algebraMap (F := F) (Ω := Ω)
  exact ⟨MorphismProperty.of_isPullback (P := @Surjective) hr.flip h1,
    MorphismProperty.of_isPullback (P := @Flat) hr.flip h2,
    MorphismProperty.of_isPullback (P := @QuasiCompact) hr.flip h3⟩

end FFSquare

/--
@isnad1 id=and.1h7v.s7.c0e29de9228c from=translated src=- shape=ffcf897f vocab=26b91bad
-/
theorem solution
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    {X X₀ : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of Ω)} {f₀ : X₀ ⟶ Spec (CommRingCat.of F)} (r : X ⟶ X₀)
    (hr : IsPullback r fX f₀ (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))) :
    Surjective r ∧ Flat r ∧ QuasiCompact r :=
  FFSquare.main r hr
