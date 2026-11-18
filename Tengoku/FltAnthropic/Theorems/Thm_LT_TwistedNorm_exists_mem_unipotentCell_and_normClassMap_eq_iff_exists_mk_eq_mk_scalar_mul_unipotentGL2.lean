import Tengoku.FltAnthropic.Definitions.Def_TwistedNormClasses
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.P2M.Sol.S_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    (∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, γ ∈ AutomorphicForm.unipotentCell F ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ↔
      ∃ (ζ : Lˣ) (b : L), Algebra.trace F L b ≠ 0 ∧
        LT.TwistedNorm.SigmaConjClasses.mk σ δ =
          LT.TwistedNorm.SigmaConjClasses.mk σ
            (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * AutomorphicForm.unipotentGL2 b) := by exact @_root_.P2MW.S_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2.solution F L _ _ _ _ _ σ hgen δ
