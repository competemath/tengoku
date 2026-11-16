import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open TensorProduct

theorem Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Smooth S T] :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by exact @_root_.P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.solution R S T _ _ _ _ _ _ _ _
