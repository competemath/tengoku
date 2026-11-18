import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Stirling
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ σ τ : ℝ, R ≤ σ → |τ| ≤ K →
      (1 - ε) * Real.Gamma σ ≤ ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Real.Gamma σ := by exact @_root_.P2MW.S_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le.solution K ε hK hε
