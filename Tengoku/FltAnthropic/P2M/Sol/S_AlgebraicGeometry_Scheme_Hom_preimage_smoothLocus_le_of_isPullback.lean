import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_preimage_smoothLocus_le_of_isPullback.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_preimage_smoothLocus_le_of_isPullback

set_option autoImplicit false

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry

universe u

set_option maxHeartbeats 800000

namespace AlgebraicGeometry export _root_.AlgebraicGeometry (Scheme.Hom.preimage_smoothLocus_eq Scheme.Hom Scheme.Hom.smoothLocus_eq_top_iff isPullback_morphismRestrict Scheme Smooth Scheme.Opens LocallyOfFinitePresentation Scheme.Opens.ι_preimage_self) namespace Scheme export _root_.AlgebraicGeometry.Scheme (Hom.preimage_smoothLocus_eq Hom Hom.smoothLocus_eq_top_iff Opens Opens.ι_preimage_self) namespace Hom export _root_.AlgebraicGeometry.Scheme.Hom (preimage_smoothLocus_eq smoothLocus_eq_top_iff smoothLocus) end AlgebraicGeometry.Scheme.Hom
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom in

/--
@isnad1 id=le.1h8v.s8.9d7efbf7a4e9 from=translated src=- shape=e97e6fb8 vocab=06224305
-/
theorem AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_le_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] :
    g' ⁻¹ᵁ f.smoothLocus ≤ f'.smoothLocus := by
  intro x' hx'

  set U : X.Opens := f.smoothLocus with hUdef
  haveI : LocallyOfFinitePresentation (U.ι ≫ f) := inferInstance
  have hU : Smooth (U.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq U.ι f]
    exact Scheme.Opens.ι_preimage_self U

  have sq : IsPullback (g' ∣_ U) ((g' ⁻¹ᵁ U).ι ≫ f') (U.ι ≫ f) g :=
    (isPullback_morphismRestrict g' U).paste_vert h
  haveI : LocallyOfFinitePresentation ((g' ⁻¹ᵁ U).ι ≫ f') := inferInstance
  have hU' : Smooth ((g' ⁻¹ᵁ U).ι ≫ f') := MorphismProperty.of_isPullback (P := @Smooth) sq hU

  have htop : (g' ⁻¹ᵁ U).ι ⁻¹ᵁ f'.smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq (g' ⁻¹ᵁ U).ι f', Scheme.Hom.smoothLocus_eq_top_iff]
    exact hU'
  have hmem : (⟨x', hx'⟩ : ↥(g' ⁻¹ᵁ U)) ∈ (g' ⁻¹ᵁ U).ι ⁻¹ᵁ f'.smoothLocus := by
    rw [htop]; trivial
  exact hmem

/--
@isnad1 id=le.1h8v.s8.9d7efbf7a4e9 from=translated src=- shape=e97e6fb8 vocab=06224305
-/
theorem solution
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (h : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] :
    g' ⁻¹ᵁ f.smoothLocus ≤ f'.smoothLocus :=
  AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_le_of_isPullback h
