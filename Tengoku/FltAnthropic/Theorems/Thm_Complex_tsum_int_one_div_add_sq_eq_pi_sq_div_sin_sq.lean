import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

/--
@isnad1 id=eq.1h1v.s7.21d5870a53fa from=translated src=- shape=485b6b8c vocab=256ddcb2
-/
theorem Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    ∑' n : ℤ, 1 / (z + n) ^ 2 = (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 := by exact @_root_.P2MW.S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq.solution z hz
