import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

theorem IsAdicComplete.finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n)
    (hI : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, LinearMap.ker (t n) ≤ I ^ (n + 1) • ⊤)
    [Module.Finite R (M 0)]
    (L : Submodule R (∀ n, M n)) (hL : ∀ x, x ∈ L ↔ ∀ n, t n (x (n + 1)) = x n) :
    Module.Finite R L ∧
      (∀ (n : ℕ) (y : M n), ∃ x ∈ L, x n = y) ∧
      (∀ (n : ℕ) (x : ∀ n, M n), x ∈ L → (x n = 0 ↔ x ∈ I ^ (n + 1) • L)) := by exact @_root_.P2MW.S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top.solution R _ I _ M _ _ t hI ht hker _ L hL
