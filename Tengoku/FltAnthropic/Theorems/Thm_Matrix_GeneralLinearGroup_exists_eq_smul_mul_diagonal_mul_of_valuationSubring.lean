import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_EichlerOrder
import Tengoku.FltAnthropic.Definitions.Def_Submodule_FiniteAdeleBox
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField
/--
@isnad1 id=ex.0h3v.s10.e1aa9352cd89 from=translated src=- shape=f7d4d9ad vocab=a3ca62bf
-/
theorem Matrix.GeneralLinearGroup.exists_eq_smul_mul_diagonal_mul_of_valuationSubring
    {K : Type*} [Field K] (O : ValuationSubring K) (H : GL (Fin 2) K) :
    ∃ (s t : K) (k₁ k₂ : GL (Fin 2) K), s ≠ 0 ∧ t ≠ 0 ∧ t ∈ O ∧
      (∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, ((k₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (∀ i j, ((k₂⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
      (H : Matrix (Fin 2) (Fin 2) K) =
        s • ((k₁ : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![(1 : K), t] * (k₂ : Matrix (Fin 2) (Fin 2) K)) := by exact @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_eq_smul_mul_diagonal_mul_of_valuationSubring.solution K _ O H
