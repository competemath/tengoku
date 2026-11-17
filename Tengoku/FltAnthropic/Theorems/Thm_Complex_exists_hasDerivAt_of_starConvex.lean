import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_exists_hasDerivAt_of_starConvex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_exists_hasDerivAt_of_starConvex.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Complex.exists_hasDerivAt_of_starConvex {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ U)
    (hstar : StarConvex ℝ q U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ g : ℂ → ℂ, g q = 0 ∧ ∀ z ∈ U, HasDerivAt g (f z) z := by exact @_root_.P2MW.S_Complex_exists_hasDerivAt_of_starConvex.solution U hU q hq hstar f hf
