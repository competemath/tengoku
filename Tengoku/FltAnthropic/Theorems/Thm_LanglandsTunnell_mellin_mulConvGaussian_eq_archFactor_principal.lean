import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchParam
import Tengoku.Seed.Analysis.MellinTransform
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real

/--
@isnad1 id=eq.2h5v.s8.641c0a85bf39 from=translated src=- shape=8c4e97c6 vocab=889afce0
-/
theorem LanglandsTunnell.mellin_mulConvGaussian_eq_archFactor_principal (u₁ : ℂ) (a₁ : ZMod 2)
    (u₂ : ℂ) (a₂ : ZMod 2) (s : ℂ) (h₁ : 0 < (s + (u₁ + signShift a₁)).re)
    (h₂ : 0 < (s + (u₂ + signShift a₂)).re) :
    mellin (fun y : ℝ => (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))
        s =
      (RealArchParam.principal u₁ a₁ u₂ a₂).archFactor s := by exact @_root_.P2MW.S_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal.solution u₁ a₁ u₂ a₂ s h₁ h₂
