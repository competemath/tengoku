import Tengoku.FltAnthropic.Definitions.Def_TwistedNormClasses
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Tengoku.FltAnthropic.P2M.Sol.S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=eq.4h6v.s9.32e341a1e60a from=translated src=- shape=a0d42b71 vocab=453e15bb
-/
theorem LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.ellipticCell F)
    (δ₁ δ₂ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h₁ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₁) = ConjClasses.mk γ)
    (h₂ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₂) = ConjClasses.mk γ) :
    LT.TwistedNorm.SigmaConjClasses.mk σ δ₁ = LT.TwistedNorm.SigmaConjClasses.mk σ δ₂ := by exact @_root_.P2MW.S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell.solution F L _ _ _ _ _ σ hgen γ hγ δ₁ δ₂ h₁ h₂
