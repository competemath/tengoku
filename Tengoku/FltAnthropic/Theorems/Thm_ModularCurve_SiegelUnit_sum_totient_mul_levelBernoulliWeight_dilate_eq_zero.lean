import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero (N : ℕ) [NeZero N]
    (s : ZMod N) (hs : s ≠ 0) :
    ∑ r : ZMod N,
        (((N / Nat.gcd r.val N) * Nat.totient (Nat.gcd r.val N) : ℕ) : ℤ) *
          (6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2) = 0 := by exact @_root_.P2MW.S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero.solution N _ s hs
