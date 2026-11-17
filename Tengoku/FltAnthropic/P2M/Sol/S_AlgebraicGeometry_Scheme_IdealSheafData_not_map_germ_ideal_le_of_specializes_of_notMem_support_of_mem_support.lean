import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_not_map_germ_ideal_le_of_specializes_of_notMem_support_of_mem_support.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_not_map_germ_ideal_le_of_specializes_of_notMem_support_of_mem_support

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

/--
@isnad1 id=not.4h6v.s12.7c062d7ee337 from=translated src=- shape=1b09c21f vocab=9ffc6bfc
-/
theorem solution
    {X : Scheme.{u}} (I J : X.IdealSheafData) (U : X.affineOpens) (x ξ : ↥X) (hx : x ∈ (U : X.Opens)) (hξx : ξ ⤳ x)
    (hξI : ξ ∉ (I.support : Set ↥X)) (hξJ : ξ ∈ (J.support : Set ↥X)) :
    ¬ (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom ≤ (J.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom := by
  intro hle
  have hξU : ξ ∈ (U : X.Opens) := hξx.mem_open U.1.isOpen hx
  obtain ⟨-, -, hdich⟩ := AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy (X := X)
  obtain ⟨hIξ, -⟩ := hdich I U ξ hξU
  obtain ⟨-, hJξ⟩ := hdich J U ξ hξU

  have hgerm : (X.presheaf.germ (U : X.Opens) ξ hξU).hom =
      (X.presheaf.stalkSpecializes hξx).hom.comp (X.presheaf.germ (U : X.Opens) x hx).hom := by
    rw [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have hle' : (I.ideal U).map (X.presheaf.germ (U : X.Opens) ξ hξU).hom ≤
      (J.ideal U).map (X.presheaf.germ (U : X.Opens) ξ hξU).hom := by
    rw [hgerm, ← Ideal.map_map, ← Ideal.map_map]
    exact Ideal.map_mono hle
  rw [hIξ hξI] at hle'
  have := (hJξ hξJ).trans' hle'
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp this)
