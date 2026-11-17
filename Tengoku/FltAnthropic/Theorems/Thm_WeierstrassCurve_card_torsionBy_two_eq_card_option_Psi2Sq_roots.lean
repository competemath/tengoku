import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
import Tengoku.Seed.Algebra.Module.Torsion.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_WeierstrassCurve_card_torsionBy_two_eq_card_option_Psi2Sq_roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WeierstrassCurve_card_torsionBy_two_eq_card_option_Psi2Sq_roots.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace WeierstrassCurve
theorem card_torsionBy_two_eq_card_option_Psi2Sq_roots {K : Type*} [Field K] [DecidableEq K]
    {W : WeierstrassCurve K} [W.IsElliptic] (h2 : (2 : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point 2) =
      Nat.card (Option {x : K // W.Ψ₂Sq.eval x = 0}) := by exact @_root_.P2MW.S_WeierstrassCurve_card_torsionBy_two_eq_card_option_Psi2Sq_roots.solution K _ _ W _ h2
end WeierstrassCurve
