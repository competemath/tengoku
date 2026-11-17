import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integrableOn_ball_iff_integrableOn_smul_circleMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integrableOn_ball_iff_integrableOn_smul_circleMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=iff.0h4v.s7.930d166ed9ff from=translated src=- shape=a87f60c8 vocab=9085bbf5
-/
theorem Complex.integrableOn_ball_iff_integrableOn_smul_circleMap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    MeasureTheory.IntegrableOn f (Metric.ball c R) ↔
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (circleMap c p.1 p.2))
        (Set.Ioo 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by exact @_root_.P2MW.S_Complex_integrableOn_ball_iff_integrableOn_smul_circleMap.solution E _ _ f c R
