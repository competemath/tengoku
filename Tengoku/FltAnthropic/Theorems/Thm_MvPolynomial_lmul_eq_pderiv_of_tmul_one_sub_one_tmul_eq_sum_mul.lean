import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=eq.1h5v.s12.e00f2b3ed236 from=translated src=- shape=fd16db86 vocab=f21aa9f7
-/
theorem MvPolynomial.lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
    (R : Type*) [CommRing R] {m : ℕ} (g : MvPolynomial (Fin m) R)
    (a : Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : g ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] g =
        ∑ j, a j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) (j : Fin m) :
    Algebra.TensorProduct.lmul' R (a j) = MvPolynomial.pderiv j g := by exact @_root_.P2MW.S_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul.solution R _ m g a ha j
