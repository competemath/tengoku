import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# General Weierstrass model for the generalized Lutz-Nagell theorem

This file sets up a general Weierstrass curve `W : WeierstrassCurve ℤ` and its base change to `ℚ`,
along with basic rewriting lemmas (equation, coefficients).

Downstream generalized Lutz-Nagell files import this file instead of `ShortWeierstrass.lean`.
-/

open scoped Polynomial.Bivariate

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve

variable (W : WeierstrassCurve ℤ)

/-- The base change of `W` to `ℚ`.-/
abbrev curveQ (W : WeierstrassCurve ℤ) : WeierstrassCurve ℚ :=
  W.map (algebraMap ℤ ℚ)

/--
@isnad1 id=eq.0h1v.s3.b7e9a185582e from=translated src=- shape=36f9a6b5 vocab=3fce2e05
-/
@[simp] lemma curveQ_a₁ : (curveQ W).a₁ = (W.a₁ : ℚ) := by simp [curveQ]
/--
@isnad1 id=eq.0h1v.s3.d4f83db7bba9 from=translated src=- shape=36f9a6b5 vocab=3519e72b
-/
@[simp] lemma curveQ_a₂ : (curveQ W).a₂ = (W.a₂ : ℚ) := by simp [curveQ]
/--
@isnad1 id=eq.0h1v.s3.f1d120af8ef6 from=translated src=- shape=36f9a6b5 vocab=f7d079ba
-/
@[simp] lemma curveQ_a₃ : (curveQ W).a₃ = (W.a₃ : ℚ) := by simp [curveQ]
/--
@isnad1 id=eq.0h1v.s3.2570c0a6c440 from=translated src=- shape=36f9a6b5 vocab=2fcccb24
-/
@[simp] lemma curveQ_a₄ : (curveQ W).a₄ = (W.a₄ : ℚ) := by simp [curveQ]
/--
@isnad1 id=eq.0h1v.s3.2dd40d5aefd8 from=translated src=- shape=36f9a6b5 vocab=2bfa2343
-/
@[simp] lemma curveQ_a₆ : (curveQ W).a₆ = (W.a₆ : ℚ) := by simp [curveQ]

/--
@isnad1 id=iff.0h3v.s7.3cc83c68235b from=translated src=- shape=1cb642f0 vocab=1f429bdb
-/
lemma curveQ_equation_iff (x y : ℚ) :
    (curveQ W).toAffine.Equation x y ↔
      y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y =
        x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curveQ]

end LutzNagellTheorem
end LutzNagell
