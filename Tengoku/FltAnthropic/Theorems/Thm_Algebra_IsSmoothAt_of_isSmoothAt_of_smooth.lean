import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem Algebra.IsSmoothAt.of_isSmoothAt_of_smooth (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.FinitePresentation R S] [Algebra.Smooth S T] (𝔓 : Ideal T) [𝔓.IsPrime]
    (h : Algebra.IsSmoothAt R 𝔓) (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔓.under S = 𝔭) :
    Algebra.IsSmoothAt R 𝔭 := by exact @_root_.P2MW.S_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth.solution R S T _ _ _ _ _ _ _ _ _ 𝔓 _ h 𝔭 _ h𝔭
