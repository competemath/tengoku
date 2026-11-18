import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u
theorem Matrix.apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem {A : Type u} [CommRing A] [IsLocalRing A]
    (hH : ∀ x : A, (∀ n : ℕ, x ∈ IsLocalRing.maximalIdeal A ^ n) → x = 0)
    {a d : A} {q : ℕ} (had : IsUnit (a - (q : A) * d)) (hda : IsUnit (d - (q : A) * a))
    {N : Matrix (Fin 2) (Fin 2) A} (hN : ∀ i j, N i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A)
    (hrel : Matrix.diagonal ![a, d] * N = N ^ q * Matrix.diagonal ![a, d]) :
    N 0 1 = 0 ∧ N 1 0 = 0 := by exact @_root_.P2MW.S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem.solution A _ _ hH a d q had hda N hN hrel
