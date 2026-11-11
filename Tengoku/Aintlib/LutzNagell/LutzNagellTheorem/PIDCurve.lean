/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# General Weierstrass model over a PID and its fraction field

This file sets up a general Weierstrass curve `W : WeierstrassCurve R` for a PID `R` and its
base change to the fraction field `K`, along with basic rewriting lemmas.

This generalizes `GeneralCurve.lean` from `ℤ/ℚ` to an arbitrary PID `R` with fraction field `K`.
-/

open scoped Polynomial.Bivariate

namespace LutzNagell
namespace PID

open WeierstrassCurve

variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- The base change of `W` to the fraction field `K`.-/
abbrev curveK : WeierstrassCurve K := W.map (algebraMap R K)

/--
@isnad1 id=eq.0h3v.s6.9fc8c3c77da9 from=translated src=- shape=758bf0e6 vocab=b92754c3
-/
@[simp] lemma curveK_a₁ : (curveK R K W).a₁ = algebraMap R K W.a₁ := by simp [curveK]
/--
@isnad1 id=eq.0h3v.s6.9c139c2f26bd from=translated src=- shape=758bf0e6 vocab=145c98fe
-/
@[simp] lemma curveK_a₂ : (curveK R K W).a₂ = algebraMap R K W.a₂ := by simp [curveK]
/--
@isnad1 id=eq.0h3v.s6.d729c8beb5c8 from=translated src=- shape=758bf0e6 vocab=555969c8
-/
@[simp] lemma curveK_a₃ : (curveK R K W).a₃ = algebraMap R K W.a₃ := by simp [curveK]
/--
@isnad1 id=eq.0h3v.s6.a52c4e67007b from=translated src=- shape=758bf0e6 vocab=9ead48fd
-/
@[simp] lemma curveK_a₄ : (curveK R K W).a₄ = algebraMap R K W.a₄ := by simp [curveK]
/--
@isnad1 id=eq.0h3v.s6.1293c9c88012 from=translated src=- shape=758bf0e6 vocab=852b54b4
-/
@[simp] lemma curveK_a₆ : (curveK R K W).a₆ = algebraMap R K W.a₆ := by simp [curveK]

/--
@isnad1 id=iff.0h5v.s9.c79ed211089f from=translated src=- shape=62bb3e73 vocab=c35b43e4
-/
lemma curveK_equation_iff (x y : K) :
    (curveK R K W).toAffine.Equation x y ↔
      y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x +
        algebraMap R K W.a₆ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [curveK]

end PID
end LutzNagell
