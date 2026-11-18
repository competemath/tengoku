import Tengoku.FltAnthropic.Definitions.Def_TwistedNormClasses
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Tengoku.FltAnthropic.P2M.Sol.S_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem LT.TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.hyperbolicCell F)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) L,
      ((g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g : Matrix.GeneralLinearGroup (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g : Matrix.GeneralLinearGroup (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by exact @_root_.P2MW.S_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq.solution F L _ _ _ _ _ σ hgen γ hγ δ h
