import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
import Tengoku.FltAnthropic.P2M.Sol.S_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace WeierstrassCurve
/--
@isnad1 id=eq.2h4v.s7.80c5d1f35517 from=translated src=- shape=f7ed4c75 vocab=ab616f4c
-/
theorem eval_Psi2Sq_of_two_nsmul_eq_zero {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y)
    (h2 : 2 • (Affine.Point.some _ _ h : W.Point) = 0) : W.Ψ₂Sq.eval x = 0 := by exact @_root_.P2MW.S_WeierstrassCurve_eval_Psi2Sq_of_two_nsmul_eq_zero.solution F _ _ W x y h h2
end WeierstrassCurve
