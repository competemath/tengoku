import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_finrank_piece_succ_le_macaulayPow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor

/--
@isnad1 id=le.2h4v.s13.1758ec89163e from=translated src=- shape=3b54936b vocab=ce28f11b
-/
theorem MvPolynomial.finrank_piece_succ_le_macaulayPow
    (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d)) := by exact @_root_.P2MW.S_MvPolynomial_finrank_piece_succ_le_macaulayPow.solution n d hd K _ J hJ
