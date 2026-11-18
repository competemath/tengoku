import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
    (H : ℝ → ℝ → ℂ) (hHm : Measurable (Function.uncurry H))
    (hHi : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (v : ℝ) (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H t u =
      ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * H (v * (σ * w - v) / w ^ 2) (v / w) := by exact @_root_.P2MW.S_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst.solution H hHm hHi v hv
