import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul (N : ℕ) [NeZero N] (p r : ℤ) :
    ∑ s : ZMod N,
        (6 * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) ^ 2
          - 6 * (N : ℤ) * ((((p : ZMod N) + s * (r : ZMod N)).val : ℕ) : ℤ) + (N : ℤ) ^ 2) =
      (N : ℤ) * (6 * (p % (Int.gcd r N : ℤ)) ^ 2
        - 6 * (Int.gcd r N : ℤ) * (p % (Int.gcd r N : ℤ)) + (Int.gcd r N : ℤ) ^ 2) := by exact @_root_.P2MW.S_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul.solution N _ p r
