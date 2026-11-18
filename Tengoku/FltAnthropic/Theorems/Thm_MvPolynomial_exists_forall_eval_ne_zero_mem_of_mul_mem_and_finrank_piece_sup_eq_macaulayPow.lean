import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open _root_.MvPolynomial hiding finrank_piece_succ_le_macaulayPow exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le open _root_.AlgebraicGeometry.HilbertFunctor

/--
@isnad1 id=ex.2h4v.s15.4397095784a0 from=translated src=- shape=637c3727 vocab=0955f396
-/
theorem MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow
    (n m : ℕ) (K : Type) [Field K] [Infinite K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    ∃ G : MvPolynomial (Fin (n + 1)) K, G ≠ 0 ∧ ∀ a : Fin (n + 1) → K, MvPolynomial.eval a G ≠ 0 →
      (∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m → (∑ i, C (a i) * X i) * f ∈ J → f ∈ J) ∧
      Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) (m + 1)) =
        Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) ∧
      Nat.macaulayPow m (Module.finrank K (piece (J ⊔ Ideal.span {∑ i, C (a i) * X i}) m)) +
          Module.finrank K (piece J m) = Nat.macaulayPow m (Module.finrank K (piece J m)) := by exact @_root_.P2MW.S_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_and_finrank_piece_sup_eq_macaulayPow.solution n m K _ _ J hJ hmax
