import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
import Tengoku.FltAnthropic.P2M.Sol.S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace WeierstrassCurve.Affine.Point
theorem two_nsmul_eq_zero_iff_Y_eq_negY {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y) :
    2 • (some _ _ h : W.Point) = 0 ↔ y = W.negY x y := by exact @_root_.P2MW.S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY.solution F _ _ W x y h
end WeierstrassCurve.Affine.Point
