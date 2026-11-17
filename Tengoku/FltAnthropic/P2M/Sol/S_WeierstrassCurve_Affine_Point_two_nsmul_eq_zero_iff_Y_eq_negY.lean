import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WeierstrassCurve_Affine_Point_two_nsmul_eq_zero_iff_Y_eq_negY

open WeierstrassCurve.Affine.Point
/--
@isnad1 id=iff.1h4v.s7.941ca78894ff from=translated src=- shape=2f30677b vocab=c9061137
-/
theorem solution {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} {x y : F} (h : W.Nonsingular x y) :
    2 • (some _ _ h : W.Point) = 0 ↔ y = W.negY x y := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, neg_some]
  exact ⟨fun hP => (some.inj hP).right, fun hy => by simp only [some.injEq]; exact ⟨trivial, hy⟩⟩
