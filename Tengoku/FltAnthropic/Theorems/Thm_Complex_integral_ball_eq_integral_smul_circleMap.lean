import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integral_ball_eq_integral_smul_circleMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integral_ball_eq_integral_smul_circleMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.0h4v.s7.2f6391196fe8 from=translated src=- shape=50c55028 vocab=fe2e8818
-/
theorem Complex.integral_ball_eq_integral_smul_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    ∫ z in Metric.ball c R, f z
      = ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, p.1 • f (circleMap c p.1 p.2) := by exact @_root_.P2MW.S_Complex_integral_ball_eq_integral_smul_circleMap.solution E _ _ f c R
