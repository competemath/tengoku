import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g

set_option autoImplicit false

universe w v u
open _root_.CategoryTheory open _root_.CategoryTheory.Abelian open _root_.CategoryTheory.Limits

theorem solution
    {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt.{w} C] {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  constructor
  · intro h0
    have hx : (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) = 0 := by
      rw [Ext.mk₀_id_comp, h0]
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS (Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) hx
    refine ⟨Ext.homEquiv₀ x₂, ?_⟩
    have : Ext.mk₀ (Ext.homEquiv₀ x₂ ≫ S.g) = Ext.mk₀ (𝟙 S.X₃) := by
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply, hx₂]
    exact Ext.homEquiv₀.symm.injective (by simpa [Ext.mk₀_homEquiv₀_apply] using this)
  · rintro ⟨s, hs⟩
    have h1 : (Ext.mk₀ s).comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) = 0 := by
      rw [hS.comp_extClass, Ext.comp_zero]
    rwa [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hs, Ext.mk₀_id_comp] at h1
