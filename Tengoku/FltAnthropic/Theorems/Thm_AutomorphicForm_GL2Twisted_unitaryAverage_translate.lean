import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_GL2Twisted_unitaryAverage_translate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_GL2Twisted_unitaryAverage_translate.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open AutomorphicForm.GL2Twisted

/--
@isnad1 id=eq.3h3v.s10.b5b7dfac90ce from=translated src=- shape=abe821dd vocab=33008b24
-/
theorem AutomorphicForm.GL2Twisted.unitaryAverage_translate (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F)
    (k₀ k₁ : GL (Fin 2) ℂ)
    (h₀ : star (k₀ : Matrix (Fin 2) (Fin 2) ℂ) * (k₀ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (h₁ : star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    unitaryAverage (fun k => F (k₀ * k * k₁)) = unitaryAverage F := by exact @_root_.P2MW.S_AutomorphicForm_GL2Twisted_unitaryAverage_translate.solution F hF k₀ k₁ h₀ h₁
