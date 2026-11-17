import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_contDiffOn_one_of_differentiableOn_pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_contDiffOn_one_of_differentiableOn_pi.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=contdiff.2h4v.s7.a78f154e70be from=translated src=- shape=4e0559b5 vocab=1e5e3baa
-/
theorem Complex.contDiffOn_one_of_differentiableOn_pi {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U := by exact @_root_.P2MW.S_Complex_contDiffOn_one_of_differentiableOn_pi.solution n E _ _ _ f U hU hf
