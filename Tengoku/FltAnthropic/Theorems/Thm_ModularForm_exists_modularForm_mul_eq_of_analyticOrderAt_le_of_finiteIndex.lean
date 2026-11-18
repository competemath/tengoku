import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularForm_exists_modularForm_mul_eq_of_analyticOrderAt_le_of_finiteIndex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularForm_exists_modularForm_mul_eq_of_analyticOrderAt_le_of_finiteIndex.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped MatrixGroups ModularForm

/--
@isnad1 id=ex.4h6v.s12.eee6595ea014 from=translated src=- shape=bdaaefc9 vocab=3c77d2ef
-/
theorem ModularForm.exists_modularForm_mul_eq_of_analyticOrderAt_le_of_finiteIndex
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] {a b : ℤ} (c : ℤ) (habc : b + c = a)
    (Φ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a) (Ψ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) b) (hΨ : Ψ ≠ 0)
    (hord : ∀ τ : UpperHalfPlane, analyticOrderAt ((Ψ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((Φ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ))
    (hcusp : ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ C : ℝ,
      ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
        ‖((Φ : UpperHalfPlane → ℂ) ∣[a] (A : GL (Fin 2) ℝ)) τ‖ ≤ C * ‖((Ψ : UpperHalfPlane → ℂ) ∣[b] (A : GL (Fin 2) ℝ)) τ‖) :
    ∃ f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) c, ∀ τ : UpperHalfPlane, f τ * Ψ τ = Φ τ := by exact @_root_.P2MW.S_ModularForm_exists_modularForm_mul_eq_of_analyticOrderAt_le_of_finiteIndex.solution Γ _ a b c habc Φ Ψ hΨ hord hcusp
