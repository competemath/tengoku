import Tengoku.FltAnthropic.Definitions.Def_TwistedNormClasses
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Tengoku.FltAnthropic.P2M.Sol.S_LT_TwistedNorm_apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_TwistedNorm_apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=eq.5h6v.s11.9ace5af87050 from=translated src=- shape=822ead46 vocab=646bfd01
-/
theorem LT.TwistedNorm.apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (β : Matrix.GeneralLinearGroup (Fin 2) L) (hβ : (β : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.unipotentCell F)
    (hclass : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ β) = ConjClasses.mk γ)
    (η : Matrix.GeneralLinearGroup (Fin 2) L)
    (hη : ((η⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) η :
        Matrix.GeneralLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((η : Matrix.GeneralLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by exact @_root_.P2MW.S_LT_TwistedNorm_apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell.solution F L _ _ _ _ _ σ hgen β hβ γ hγ hclass η hη
