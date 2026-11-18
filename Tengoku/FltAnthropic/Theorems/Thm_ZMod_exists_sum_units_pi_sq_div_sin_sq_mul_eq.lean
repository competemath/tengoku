import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ZMod_exists_sum_units_pi_sq_div_sin_sq_mul_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ZMod_exists_sum_units_pi_sq_div_sin_sq_mul_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

/--
@isnad1 id=ex.1h1v.s9.e7e89a5d8a5e from=translated src=- shape=c693d31a vocab=058ab1a0
-/
theorem ZMod.exists_sum_units_pi_sq_div_sin_sq_mul_eq (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ h : (ZMod N)ˣ → ℂ, ∀ s : (ZMod N)ˣ,
      ∑ t : (ZMod N)ˣ, (π : ℂ) ^ 2 / Complex.sin (π * (t : ZMod N).val / N) ^ 2 * h (t * s) =
        (if s = 1 then 1 else 0) + (if s = -1 then 1 else 0) := by exact @_root_.P2MW.S_ZMod_exists_sum_units_pi_sq_div_sin_sq_mul_eq.solution N _ hN
