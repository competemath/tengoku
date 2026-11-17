import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eq_of_isClosed_of_forall_rationalPoint_mem_iff
    {κ : Type u} [Field κ] [IsAlgClosed κ] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f]
    {Z₁ Z₂ : Set Y} (h₁ : IsClosed Z₁) (h₂ : IsClosed Z₂)
    (h : ∀ y : Spec (CommRingCat.of κ) ⟶ Y, y ≫ f = 𝟙 _ →
      (y.base (IsLocalRing.closedPoint κ) ∈ Z₁ ↔ y.base (IsLocalRing.closedPoint κ) ∈ Z₂)) :
    Z₁ = Z₂ := by exact @_root_.P2MW.S_AlgebraicGeometry_eq_of_isClosed_of_forall_rationalPoint_mem_iff.solution κ _ _ Y f _ Z₁ Z₂ h₁ h₂ h
