import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isNilpotent_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [Smooth f]
    {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    (t : Spec (CommRingCat.of C) ⟶ S) (x₀ : Spec (CommRingCat.of (C ⧸ J)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ t) :
    ∃ x : Spec (CommRingCat.of C) ⟶ X, x ≫ f = t ∧ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ x = x₀ := by exact @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine.solution X S _ _ f _ C _ J hJ t x₀ hx₀
