import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w w'

open scoped BigOperators

theorem IsBaseChange.exists_dual_comp_eq_algebraMap_and_sum_smul_eq
    {A : Type u} [CommRing A] {A' : Type v} [CommRing A'] [Algebra A A']
    {M : Type w} [AddCommGroup M] [Module A M]
    {M' : Type w'} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
    (f : M →ₗ[A] M') (hf : IsBaseChange A' f)
    {n : ℕ} (x : Fin n → M) (φ : Fin n → (M →ₗ[A] A)) (hxφ : ∀ m : M, ∑ i, φ i m • x i = m) :
    ∃ φ' : Fin n → (M' →ₗ[A'] A'),
      (∀ (i : Fin n) (m : M), φ' i (f m) = algebraMap A A' (φ i m)) ∧
        ∀ m' : M', ∑ i, φ' i m' • f (x i) = m' := by exact @_root_.P2MW.S_IsBaseChange_exists_dual_comp_eq_algebraMap_and_sum_smul_eq.solution A _ A' _ _ M _ _ M' _ _ _ _ f hf n x φ hxφ
