import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_le_of_forall_mem_support_exists_specializes_map_germ_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_le_of_forall_mem_support_exists_specializes_map_germ_le

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

/--
@isnad1 id=le.1h3v.s12.c2f968ae11ab from=translated src=- shape=0bf03e59 vocab=9ffc6bfc
-/
theorem solution
    {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ x : X, x ∈ (J.support : Set X) →
      ∃ (y : X) (_ : x ⤳ y) (U : X.affineOpens) (hy : y ∈ (U : X.Opens)),
        Ideal.map (X.presheaf.germ (U : X.Opens) y hy).hom (I.ideal U) ≤
          Ideal.map (X.presheaf.germ (U : X.Opens) y hy).hom (J.ideal U)) :
    I ≤ J := by
  classical
  obtain ⟨hind, -, hsupp⟩ :=
    @AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy X
  rw [Scheme.IdealSheafData.le_def]
  intro U s hs
  rw [U.2.mem_ideal_iff]
  intro x hxU
  by_cases hxJ : x ∈ (J.support : Set X)
  · obtain ⟨y, hxy, V, hyV, hle⟩ := h x hxJ
    have hxV : x ∈ (V : X.Opens) := hxy.mem_open V.1.isOpen hyV

    have hsI : (X.presheaf.germ (U : X.Opens) x hxU).hom s ∈
        Ideal.map (X.presheaf.germ (V : X.Opens) x hxV).hom (I.ideal V) := by
      rw [← hind I x U V hxU hxV]
      exact Ideal.mem_map_of_mem _ hs
    rw [hind J x U V hxU hxV]

    have hgerm : (X.presheaf.germ (V : X.Opens) x hxV).hom =
        (X.presheaf.stalkSpecializes hxy).hom.comp (X.presheaf.germ (V : X.Opens) y hyV).hom := by
      rw [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
    rw [hgerm, ← Ideal.map_map] at hsI ⊢
    exact Ideal.map_mono hle hsI
  · rw [(hsupp J U x hxU).1 hxJ]
    exact Submodule.mem_top
