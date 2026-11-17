import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct
theorem Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
    (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module ℚ A] [Module.Finite ℚ A]
    (Hp : Type*) [AddCommGroup Hp] [Module ℤ_[p] Hp]
    [Module.Finite ℤ_[p] Hp] [Module.Flat ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp)) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ A) (bHp : Basis (Fin n) ℤ_[p] Hp),
      ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i) := by exact @_root_.P2MW.S_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange.solution p _ A _ _ _ Hp _ _ _ _ φ
