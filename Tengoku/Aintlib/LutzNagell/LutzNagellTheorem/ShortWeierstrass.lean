/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Weierstrass
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Short Weierstrass model for Lutz-Nagell

This file sets up the short Weierstrass curve

`y^2 = x^3 + A*x + B`

over `ℤ` and its base change to `ℚ`, and proves basic rewriting lemmas (equation, discriminant).

Downstream Lutz-Nagell files should import this file instead of re-expanding `Δ`/`Equation`.
-/

open scoped Polynomial.Bivariate

namespace LutzNagell
namespace LutzNagellTheorem

open WeierstrassCurve

/-- The short Weierstrass curve over `ℤ`: `y^2 = x^3 + A*x + B`.-/
def shortCurveZ (A B : ℤ) : WeierstrassCurve ℤ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := A, a₆ := B }

/-- The short Weierstrass curve over `ℚ`, obtained from `shortCurveZ` by base change.-/
def shortCurveQ (A B : ℤ) : WeierstrassCurve ℚ :=
  (shortCurveZ A B).map (algebraMap ℤ ℚ)

/--
@isnad1 id=eq.0h2v.s4.e24dba3b3f3e from=translated src=- shape=4ed13b70 vocab=abbeddbf
-/
@[simp] lemma shortCurveZ_a₁ (A B : ℤ) : (shortCurveZ A B).a₁ = 0 := rfl
/--
@isnad1 id=eq.0h2v.s4.61b2fb900bf4 from=translated src=- shape=4ed13b70 vocab=7c6c69cd
-/
@[simp] lemma shortCurveZ_a₂ (A B : ℤ) : (shortCurveZ A B).a₂ = 0 := rfl
/--
@isnad1 id=eq.0h2v.s4.cee1ebe8fdd0 from=translated src=- shape=4ed13b70 vocab=dbc5b6af
-/
@[simp] lemma shortCurveZ_a₃ (A B : ℤ) : (shortCurveZ A B).a₃ = 0 := rfl
/--
@isnad1 id=eq.0h2v.s3.2c72a65dc03b from=translated src=- shape=24ca3bc8 vocab=39986a71
-/
@[simp] lemma shortCurveZ_a₄ (A B : ℤ) : (shortCurveZ A B).a₄ = A := rfl
/--
@isnad1 id=eq.0h2v.s3.3c279530a8ea from=translated src=- shape=9da2df65 vocab=4bbc6962
-/
@[simp] lemma shortCurveZ_a₆ (A B : ℤ) : (shortCurveZ A B).a₆ = B := rfl

/--
@isnad1 id=eq.0h2v.s4.b24907109374 from=translated src=- shape=488223d7 vocab=7475c2aa
-/
@[simp] lemma shortCurveQ_a₁ (A B : ℤ) : (shortCurveQ A B).a₁ = 0 := by
  simp [shortCurveQ, shortCurveZ]

/--
@isnad1 id=eq.0h2v.s4.30485ea4c03d from=translated src=- shape=488223d7 vocab=b6135bbd
-/
@[simp] lemma shortCurveQ_a₂ (A B : ℤ) : (shortCurveQ A B).a₂ = 0 := by
  simp [shortCurveQ, shortCurveZ]

/--
@isnad1 id=eq.0h2v.s4.b8fac155929c from=translated src=- shape=488223d7 vocab=4e32d1b8
-/
@[simp] lemma shortCurveQ_a₃ (A B : ℤ) : (shortCurveQ A B).a₃ = 0 := by
  simp [shortCurveQ, shortCurveZ]

/--
@isnad1 id=eq.0h2v.s3.0807625996b3 from=translated src=- shape=db0d16d5 vocab=8c245524
-/
@[simp] lemma shortCurveQ_a₄ (A B : ℤ) : (shortCurveQ A B).a₄ = (A : ℚ) := by
  simp [shortCurveQ, shortCurveZ]

/--
@isnad1 id=eq.0h2v.s3.66ef7b7f1262 from=translated src=- shape=77ecab87 vocab=a80ba8c2
-/
@[simp] lemma shortCurveQ_a₆ (A B : ℤ) : (shortCurveQ A B).a₆ = (B : ℚ) := by
  simp [shortCurveQ, shortCurveZ]

/--
@isnad1 id=iff.0h4v.s6.3456b3804f99 from=translated src=- shape=eb8724b9 vocab=5ea00925
-/
lemma shortCurveQ_equation_iff (A B : ℤ) (x y : ℚ) :
    (shortCurveQ A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + (A : ℚ) * x + (B : ℚ) := by
  simpa [shortCurveQ, shortCurveZ, add_assoc, add_comm, add_left_comm, mul_assoc]
    using (WeierstrassCurve.Affine.equation_iff (W := shortCurveQ A B) x y)

/--
@isnad1 id=eq.0h2v.s6.b5c30de9e56d from=translated src=- shape=fb1fc8c3 vocab=121d29c5
-/
lemma shortCurveZ_delta (A B : ℤ) :
    (shortCurveZ A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, shortCurveZ]
  ring1

end LutzNagellTheorem
end LutzNagell
