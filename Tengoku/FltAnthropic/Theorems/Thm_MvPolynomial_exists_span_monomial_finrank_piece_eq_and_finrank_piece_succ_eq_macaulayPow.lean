import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

theorem MvPolynomial.exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow
    (n d : ℕ) (hd : 1 ≤ d) (a : ℕ) (ha : a ≤ (n + d).choose n) (K : Type) [Field K] :
    ∃ J : Ideal (MvPolynomial (Fin (n + 1)) K),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous d) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J d) = a ∧ Module.finrank K (piece J (d + 1)) = Nat.macaulayPow d a := by exact @_root_.P2MW.S_MvPolynomial_exists_span_monomial_finrank_piece_eq_and_finrank_piece_succ_eq_macaulayPow.solution n d hd a ha K _
