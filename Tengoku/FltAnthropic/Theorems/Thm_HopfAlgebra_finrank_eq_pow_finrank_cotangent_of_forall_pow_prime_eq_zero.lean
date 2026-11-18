import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v

theorem HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] [Module.Finite k A]
    (hA : ∀ a : A, Coalgebra.counit (R := k) a = 0 → a ^ p = 0) :
    Module.finrank k A =
      p ^ Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent := by exact @_root_.P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero.solution k _ p _ _ A _ _ _ hA
