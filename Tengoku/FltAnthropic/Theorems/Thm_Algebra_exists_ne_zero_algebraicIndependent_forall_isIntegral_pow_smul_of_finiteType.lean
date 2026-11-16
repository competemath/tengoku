import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

theorem Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
    {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
    [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C] :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C), AlgebraicIndependent R z ∧
      ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c) := by exact @_root_.P2MW.S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType.solution R C _ _ _ _ _ _ _
