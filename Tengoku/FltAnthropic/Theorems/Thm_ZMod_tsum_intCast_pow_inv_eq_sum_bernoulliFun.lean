import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Real Complex
open scoped Nat

theorem ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k)
    (a : ZMod N) :
    ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      -(2 * π * I) ^ k / (k ! * N) *
        ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * (bernoulliFun k ((r.val : ℝ) / N) : ℂ) := by exact @_root_.P2MW.S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun.solution N _ k hk a
