import Tengoku.Seed.CategoryTheory.Monoidal.Braided.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit

set_option autoImplicit false

universe v u

open _root_.CategoryTheory open _root_.CategoryTheory.MonoidalCategory

theorem solution {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {M N M' N' : C} (e : M ≅ M') (h : Nonempty (M ⊗ N ≅ 𝟙_ C)) (h' : Nonempty (M' ⊗ N' ≅ 𝟙_ C)) :
    Nonempty (N ≅ N') := by
  obtain ⟨i⟩ := h
  obtain ⟨i'⟩ := h'
  exact ⟨(ρ_ N).symm ≪≫ (Iso.refl N ⊗ᵢ i'.symm) ≪≫ (α_ N M' N').symm ≪≫
    ((β_ N M') ⊗ᵢ Iso.refl N') ≪≫ ((e.symm ⊗ᵢ Iso.refl N) ⊗ᵢ Iso.refl N') ≪≫
    (i ⊗ᵢ Iso.refl N') ≪≫ λ_ N'⟩
