import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

/--
@isnad1 id=ex.2h4v.s14.5af57acaad5f from=translated src=- shape=0d9ece23 vocab=d0782da3
-/
theorem MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le
    (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] [Infinite K]
    (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      Nat.macaulayPow d (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) d)) +
          Module.finrank K (piece J d) ≤
        Nat.macaulayPow d (Module.finrank K (piece J d)) := by exact @_root_.P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le.solution n d hd K _ _ J hJ
