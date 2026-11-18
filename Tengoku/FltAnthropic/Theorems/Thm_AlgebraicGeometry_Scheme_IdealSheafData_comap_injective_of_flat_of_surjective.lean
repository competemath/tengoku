import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.AlgebraicGeometry.Morphisms.UnderlyingMap
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Functorial
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_injective_of_flat_of_surjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_injective_of_flat_of_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=injectiv.0h3v.s5.9845ff16d5b7 from=translated src=- shape=159933fd vocab=e60ecd3a
-/
theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective
    {X Y : Scheme.{u}} (π : Y ⟶ X) [Flat π] [Surjective π] :
    Function.Injective fun I : X.IdealSheafData => I.comap π := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_injective_of_flat_of_surjective.solution X Y π _ _
