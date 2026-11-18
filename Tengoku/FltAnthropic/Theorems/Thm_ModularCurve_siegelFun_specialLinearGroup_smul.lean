import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SiegelFunction
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_siegelFun_specialLinearGroup_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_siegelFun_specialLinearGroup_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
open ModularCurve
/--
@isnad1 id=ex.0h2v.s9.c27beedbdf9e from=translated src=- shape=0923d4b7 vocab=fe649354
-/
theorem ModularCurve.siegelFun_specialLinearGroup_smul (N : ℕ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ μ : ℂ, μ ^ 12 = 1 ∧ ∀ (r s : ℤ) (τ : UpperHalfPlane),
      siegelFun N r s ((α • τ : UpperHalfPlane) : ℂ) =
        μ * siegelFun N (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
          (r * (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + s * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (τ : ℂ) := by exact @_root_.P2MW.S_ModularCurve_siegelFun_specialLinearGroup_smul.solution N α
