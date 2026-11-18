import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.Calculus.Deriv.Basic
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real

/--
@isnad1 id=ex.4h6v.s8.b0008e3cd897 from=translated src=- shape=05ec1071 vocab=cd1268b4
-/
theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing
    (b : ℂ) (σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + h y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min b.re σ - ε) := by exact @_root_.P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing.solution b σ A f h hf hh hfeq
