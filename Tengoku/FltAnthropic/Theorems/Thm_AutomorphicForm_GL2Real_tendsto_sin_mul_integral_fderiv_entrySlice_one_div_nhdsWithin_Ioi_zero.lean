import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

/--
@isnad1 id=tendsto.3h4v.s12.9561f18f96d8 from=translated src=- shape=2cdcbe5b vocab=8e2a572b
-/
theorem AutomorphicForm.GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        (fderiv ℝ (fun M => Φ (M, p))
            (Matrix.of.symm !![r * (Real.cos θ - q.2), r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1);
              -(r * q.1), r * (Real.cos θ + q.2)])
            (Matrix.of.symm !![1, 0; 0, 1]) +
          fderiv ℝ (fun M => Φ (M, p))
            (Matrix.of.symm !![r * (Real.cos θ + q.2), -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1));
              r * q.1, r * (Real.cos θ - q.2)])
            (Matrix.of.symm !![1, 0; 0, 1])) / (q.1 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by exact @_root_.P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.solution P _ _ Φ hΦs hΦc p r hr
