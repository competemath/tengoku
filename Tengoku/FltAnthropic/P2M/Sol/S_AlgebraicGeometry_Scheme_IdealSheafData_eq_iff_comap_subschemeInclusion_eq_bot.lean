import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem solution
    {W : Scheme.{u}} (I₁ I₂ : W.IdealSheafData) :
    I₁ = I₂ ↔ I₂.comap I₁.subschemeι = ⊥ ∧ I₁.comap I₂.subschemeι = ⊥ := by
  have key : ∀ (I J : W.IdealSheafData), J.comap I.subschemeι = ⊥ ↔ J ≤ I := by
    intro I J
    rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot,
      Scheme.IdealSheafData.ker_subschemeι]
  rw [key, key, le_antisymm_iff, and_comm]
