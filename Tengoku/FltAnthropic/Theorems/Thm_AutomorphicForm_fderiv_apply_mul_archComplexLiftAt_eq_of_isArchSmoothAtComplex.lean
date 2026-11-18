import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open NumberField NumberField.InfinitePlace AutomorphicForm Complex

theorem AutomorphicForm.fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℂ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℂ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          archDerivAtComplex hw ArchDirComplex.H φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          archDerivAtComplex hw ArchDirComplex.iH φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).re * archDerivAtComplex hw ArchDirComplex.E φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 0 1).im * archDerivAtComplex hw ArchDirComplex.iE φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).re * archDerivAtComplex hw ArchDirComplex.Fm φ (g * archComplexLiftAt hw e) +
      (((Matrix.of e)⁻¹ * Matrix.of Y) 1 0).im * archDerivAtComplex hw ArchDirComplex.iFm φ (g * archComplexLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).re *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp (s : ℂ)) (Complex.exp_ne_zero _))))) 0 +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2).im *
          deriv (fun s : ℝ => φ (g * archComplexLiftAt hw e *
            archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom
              (Units.mk0 (Complex.exp ((s : ℂ) * I)) (Complex.exp_ne_zero _))))) 0 := by exact @_root_.P2MW.S_AutomorphicForm_fderiv_apply_mul_archComplexLiftAt_eq_of_isArchSmoothAtComplex.solution F _ _ w hw φ hφ g e he Y
