import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Transporting a complete indecomposable family through an equivalence -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CategoryTheory
universe u v u' v' w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]
variable (E : C ≌ D) [E.functor.Additive]
variable {ι : Type w} (F : ι → D)

/-- Completeness transfers without unfolding the construction of the equivalence.
@isnad1 id=ex.2h6v.s6.3b2c2b438e4b from=translated src=- shape=f656c7ff vocab=8fce41e5
-/
theorem complete_indecomposable_family_of_equivalence
    (hF : ∀ Y : D, Indecomposable Y → ∃ i, Nonempty (Y ≅ F i))
    (X : C) (hX : Indecomposable X) :
    ∃ i, Nonempty (X ≅ E.inverse.obj (F i)) := by
  have hEX := (indecomposable_map_iff_of_equivalence E.functor X).mpr hX
  obtain ⟨i, ⟨e⟩⟩ := hF (E.functor.obj X) hEX
  exact ⟨i, ⟨E.functor.preimageIso (e ≪≫ (E.counitIso.app (F i)).symm)⟩⟩

end MagnitudeConjecture.CategoryTheory
