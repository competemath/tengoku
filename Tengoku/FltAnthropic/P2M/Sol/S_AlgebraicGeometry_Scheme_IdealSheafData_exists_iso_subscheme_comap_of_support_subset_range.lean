import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_iso_subscheme_comap_of_support_subset_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=ex.1h4v.s8.9e7b59702c46 from=translated src=- shape=d88216ed vocab=e4c21a06
-/
theorem solution
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (ψ : Y ⟶ X) [IsOpenImmersion ψ]
    (h : (I.support : Set X) ⊆ Set.range ψ) :
    ∃ e : (I.comap ψ).subscheme ≅ I.subscheme, e.hom ≫ I.subschemeι = (I.comap ψ).subschemeι ≫ ψ := by
  have hZU : ∀ z : I.subscheme, I.subschemeι z ∈ Set.range ⇑ψ := by
    intro z
    apply h
    change I.subschemeι z ∈ (I.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
  haveI : IsIso (pullback.snd ψ I.subschemeι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    ext z
    simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Scheme.Pullback.range_snd]
    exact hZU z
  refine ⟨I.comapIso ψ ≪≫ asIso (pullback.snd ψ I.subschemeι), ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
