import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s))
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) := by exact @_root_.P2MW.S_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant.solution s hs
