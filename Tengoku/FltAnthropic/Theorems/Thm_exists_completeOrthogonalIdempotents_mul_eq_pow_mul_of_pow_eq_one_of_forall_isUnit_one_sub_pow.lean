import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow
    (R : Type u) [CommRing R] (N : ℕ) (hd : IsUnit ((N + 1 : ℕ) : R))
    (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : R) (hω : ω ^ (N + 1) = 1) :
    ∃ e : Fin (N + 1) → R, CompleteOrthogonalIdempotents e ∧ ∀ k : Fin (N + 1), ω * e k = ζ ^ (k : ℕ) * e k := by exact @_root_.P2MW.S_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow.solution R _ N hd ζ hζ hζu ω hω
