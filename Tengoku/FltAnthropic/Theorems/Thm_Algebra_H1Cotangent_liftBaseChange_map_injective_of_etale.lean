import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

/--
@isnad1 id=injectiv.0h3v.s10.517c6ba44171 from=translated src=- shape=383e4394 vocab=221c3633
-/
theorem Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale (R D T : Type u)
    [CommRing R] [CommRing D] [CommRing T] [Algebra R D] [Algebra D T] [Algebra R T] [IsScalarTower R D T]
    [Algebra.Etale D T] :
    Function.Injective ((Algebra.H1Cotangent.map R R D T).liftBaseChange T) := by exact @_root_.P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.solution R D T _ _ _ _ _ _ _ _
