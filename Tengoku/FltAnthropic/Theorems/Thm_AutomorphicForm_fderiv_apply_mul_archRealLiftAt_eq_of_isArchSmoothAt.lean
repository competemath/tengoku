import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField NumberField.InfinitePlace AutomorphicForm

/--
@isnad1 id=eq.3h6v.s12.af9385dd5ea5 from=translated src=- shape=72dc9d14 vocab=e062a482
-/
theorem AutomorphicForm.fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          archDerivAt hw ArchDir.H φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 1 : ℝ) : ℂ) * archDerivAt hw ArchDir.E φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 1 0 : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          deriv (fun s : ℝ => φ (g * archRealLiftAt hw e *
            archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
              (Units.mk0 (Real.exp s) (Real.exp_ne_zero s))))) 0 := by exact @_root_.P2MW.S_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt.solution F _ _ w hw φ hφ g e he Y
