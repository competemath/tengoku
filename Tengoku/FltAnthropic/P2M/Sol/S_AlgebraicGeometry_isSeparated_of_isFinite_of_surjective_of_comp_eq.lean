import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=issepara.1h6v.s6.c6edb0167bdb from=translated src=- shape=a108a62c vocab=5ff2cb15
-/
theorem solution
    {X Y S : Scheme.{0}} (p : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (h : p ≫ g = f)
    [IsFinite p] [Surjective p] [IsSeparated f] : IsSeparated g := by

  let q : pullback f f ⟶ pullback g g := pullback.map f f g g p p (𝟙 S) (by simp [h]) (by simp [h])
  haveI : UniversallyClosed q :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) (inferInstance : UniversallyClosed p) (inferInstance : UniversallyClosed p)
      (by simp [h]) (by simp [h])

  have hsq : pullback.diagonal f ≫ q = p ≫ pullback.diagonal g := by
    apply pullback.hom_ext
    · erw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.diagonal_fst, Category.id_comp,
        pullback.diagonal_fst, Category.comp_id]
    · erw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.diagonal_snd, Category.id_comp,
        pullback.diagonal_snd, Category.comp_id]

  have hcomp : ∀ {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C), (⇑(u ≫ v).base : A → C) = ⇑v.base ∘ ⇑u.base := by
    intro A B C u v; ext; simp
  have hrange : Set.range (pullback.diagonal g).base = q.base '' Set.range (pullback.diagonal f).base := by
    have h1 : Set.range (p ≫ pullback.diagonal g).base = Set.range (pullback.diagonal g).base := by
      rw [hcomp]; exact Function.Surjective.range_comp p.surjective _
    rw [← h1, ← hsq, hcomp, Set.range_comp]
  have hclosed : IsClosed (Set.range (pullback.diagonal g).base) := by
    rw [hrange]
    exact q.isClosedMap _ (pullback.diagonal f).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩
