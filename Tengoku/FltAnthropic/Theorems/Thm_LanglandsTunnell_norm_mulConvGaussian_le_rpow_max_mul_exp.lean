import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchParam
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real

/--
@isnad1 id=ex.0h4v.s8.57d152d75814 from=translated src=- shape=66ce5490 vocab=16a832a4
-/
theorem LanglandsTunnell.norm_mulConvGaussian_le_rpow_max_mul_exp (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ)
    (a₂ : ZMod 2) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ‖(4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)‖
        ≤ C * y ^ (max (u₁ + signShift a₁).re (u₂ + signShift a₂).re) * Real.exp (-(π * y)) := by exact @_root_.P2MW.S_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp.solution u₁ a₁ u₂ a₂
