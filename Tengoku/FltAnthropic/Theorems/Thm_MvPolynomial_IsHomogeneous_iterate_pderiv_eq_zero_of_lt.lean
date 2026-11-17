import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Manifold

theorem MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R}
    {n : ℕ} (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) :
    (MvPolynomial.pderiv k)^[i] φ = 0 := by exact @_root_.P2MW.S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.solution σ R _ φ n hφ k i hi
