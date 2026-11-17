import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Matrix.exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
    (q : ℕ) (k : Type) [Field k] (φ : ZMod q →+* k)
    (B : Matrix (Fin 2) (Fin 2) k) (hB : B.det ≠ 0)
    (h : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) (ZMod q), ∃ c : k,
      B * (γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ = c • ((γ : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ * B)) :
    ∃ a : k, B = a • (1 : Matrix (Fin 2) (Fin 2) k) := by exact @_root_.P2MW.S_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul.solution q k _ φ B hB h
