import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.0h3v.s6.7cb46ffa8a48 from=translated src=- shape=a427e372 vocab=f81d3912
-/
theorem LanglandsTunnell.exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma
    (d τ τ' : ℝ) :
    ∃ K R : ℝ, 0 < K ∧ ∀ y : ℝ, R ≤ y →
      ‖Complex.Gamma (((y + d : ℝ) : ℂ) + (τ' : ℂ) * Complex.I)‖
        ≤ K * y ^ d * ‖Complex.Gamma ((y : ℂ) + (τ : ℂ) * Complex.I)‖ := by exact @_root_.P2MW.S_LanglandsTunnell_exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma.solution d τ τ'
