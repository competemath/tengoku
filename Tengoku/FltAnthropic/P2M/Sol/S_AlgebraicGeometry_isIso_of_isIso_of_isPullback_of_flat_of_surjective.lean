import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=isiso.6h15v.s7.78601b1ba51b from=translated src=- shape=da80528d vocab=da6e4be3
-/
theorem solution
    {S S' A B A' B' : Scheme.{0}} (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (pA : A ⟶ S) (pB : B ⟶ S) (φ : A ⟶ B) (hφ : φ ≫ pB = pA)
    (pA' : A' ⟶ S') (pB' : B' ⟶ S') (φ' : A' ⟶ B') (hφ' : φ' ≫ pB' = pA')
    (gA : A' ⟶ A) (gB : B' ⟶ B) (sqA : IsPullback gA pA' pA b) (sqB : IsPullback gB pB' pB b)
    (comm : φ' ≫ gB = gA ≫ φ) (hiso : IsIso φ') :
    IsIso φ := by

  have outer : IsPullback (φ' ≫ pB') gA b (φ ≫ pB) := by
    rw [hφ', hφ]
    exact sqA.flip
  have sq : IsPullback φ' gA gB φ := IsPullback.of_right outer comm sqB.flip

  have hS : Surjective gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hF : Flat gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hQ : QuasiCompact gB := MorphismProperty.of_isPullback sqB.flip inferInstance
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) gB := ⟨⟨hS, hF⟩, hQ⟩
  have hP : (MorphismProperty.isomorphisms Scheme.{0}) φ' := (MorphismProperty.isomorphisms.iff _).mpr hiso
  exact (MorphismProperty.isomorphisms.iff _).mp
    (MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq hQ' hP)
