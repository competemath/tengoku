import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_IsIntegral_injective_of_injective_algebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_IsIntegral_injective_of_injective_algebraMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Algebra.IsIntegral.injective_of_injective_algebraMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A C)) (φ : B →ₐ[A] C) :
    Function.Injective φ := by exact @_root_.P2MW.S_Algebra_IsIntegral_injective_of_injective_algebraMap.solution A B C _ _ _ _ _ _ _ _ hinj φ
