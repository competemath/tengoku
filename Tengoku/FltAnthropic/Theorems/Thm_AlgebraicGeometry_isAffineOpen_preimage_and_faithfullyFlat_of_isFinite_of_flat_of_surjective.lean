import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=and.2h4v.s13.c1c1500c6d20 from=translated src=- shape=ecc9f833 vocab=8004b736
-/
theorem AlgebraicGeometry.isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [Flat g] (hsurj : Function.Surjective g)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (g ⁻¹ᵁ U) ∧ Function.Injective (g.app U).hom ∧
      (letI _i : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra;
        Module.FaithfullyFlat Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) := by exact @_root_.P2MW.S_AlgebraicGeometry_isAffineOpen_preimage_and_faithfullyFlat_of_isFinite_of_flat_of_surjective.solution X Y g _ _ hsurj U hU
