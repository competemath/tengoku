import Tengoku.FltAnthropic.Definitions.Def_TwistedNormClasses
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Tengoku.FltAnthropic.P2M.Sol.S_LT_TwistedNorm_exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_TwistedNorm_exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.3h5v.s12.55feafb4ea68 from=translated src=- shape=e9186fea vocab=cd39d874
-/
theorem LT.TwistedNorm.exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t t' : GL (Fin 2) L)
    (ht : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (ht' : (t' : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t' : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    ((∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ t' = b⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ↔
      Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧ Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∧
    ((∃ a : GL (Fin 2) L, ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ t' = a⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) a) ↔
      Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧ Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∧
    ((∃ g : GL (Fin 2) L, t' = g⁻¹ * t * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ↔
      (Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) ∧ Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ∨
      (Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 0 0) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1) ∧ Algebra.norm K ((t' : Matrix (Fin 2) (Fin 2) L) 1 1) = Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0))) := by exact @_root_.P2MW.S_LT_TwistedNorm_exists_eq_inv_mul_mul_map_iff_norm_eq_of_diagonal.solution K L _ _ _ _ _ σ hgen t t' ht ht'
