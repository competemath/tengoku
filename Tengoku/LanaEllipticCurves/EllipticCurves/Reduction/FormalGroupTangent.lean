/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.FormalGroupAdditivity
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.DividedDiffDiagonal
import Tengoku.LanaEllipticCurves.EllipticCurves.Reduction.LocalParameterInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Diagonal chord/tangent identities for the formal addition law (issue #373)

The merged secant lemma `WeierstrassCurve.thirdChordPoint_functional_eq`
(`Reduction/FormalGroupAdditivity.lean`) is gated on the secant hypothesis `z₁ ≠ z₂`: its proof
divides the Vieta certificate by `(z₁ − z₂)`, which vanishes on the diagonal `z₁ = z₂`.  The
doubling (tangent) case needs, in place of the second known intersection, the **tangency**
relation: the
chord slope on the diagonal is the derivative of the Weierstrass expansion, and that derivative
satisfies the differentiated Weierstrass functional equation.

This file supplies those two diagonal ingredients (steps 1–2 of the #373 route), building on the
just-landed diagonal-derivative brick
`PowerSeries.adicEvalMv_dividedDiff_diagonal` (`FormalGroup/DividedDiffDiagonal.lean`, PR #91):

* `WeierstrassCurve.derivative_formalW` — the **differentiated Weierstrass functional equation** at
  the power-series level: `w′ = 3z² + (a₁ + 2a₂z)w + (a₁z + a₂z²)w′ + a₄w² + 2(a₃ + a₄z)w·w′
  + 3a₆w²·w′`, obtained by applying the formal derivative `d⁄dX` to `formalW_eq`.
* `WeierstrassCurve.wParamDeriv` — the numeric derivative `w′(z) = adicEval z (d⁄dX formalW) ∈ R`,
  the diagonal counterpart of `wParam`.
* `WeierstrassCurve.chordSlope_diag` — on the diagonal `z₁ = z₂ = z`, the numeric chord slope
  `λ = chordSlope` equals `wParamDeriv z`.  This is the identity "the tangent slope is the
  derivative".
* `WeierstrassCurve.wParamDeriv_tangency` — the numeric image of `derivative_formalW` under
  `adicEval z`: the tangency relation among `z`, `w(z)`, and `w′(z) = λ`, the second relation the
  doubling Vieta needs (in place of the secant's second known point).

and, in the final section, the lemma those two exist for:

* `WeierstrassCurve.thirdChordPoint_functional_eq_diag` — **the doubling third-chord lemma**: on the
  diagonal the pair `(t, λt + ν)` solves the numeric Weierstrass functional equation.  The
  double-root Vieta is closed by a `linear_combination` of the value equation
  `wParam_functional_eq`, the tangency relation `wParamDeriv_tangency` (with `λ = chordSlope_diag`),
  and `formalThirdRoot_vieta` (which on the diagonal reads `A·(t + 2z) + S = 0`) — the double-root
  analog of the secant certificate.

⚠️ **This file used to carry a `## Remaining for #373` section prescribing exactly that recipe for
exactly that lemma, twenty-one minutes before the lemma was added to this same file.**  The
follow-up landed the theorem into this file's own final section, left the paragraph calling it
missing, and left it out of this list.  *A "what remains" section is stale the moment the work lands
in the file it sits in, and no build can tell.*

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

open MvPowerSeries PowerSeries IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve

/-! ### The differentiated Weierstrass functional equation (power-series level) -/

section Derivative

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

open scoped PowerSeries

/-- **The differentiated Weierstrass functional equation.**  Applying the formal derivative
`d⁄dX` to the fixed-point equation `formalW_eq` (`w = z³ + (a₁z + a₂z²)w + (a₃ + a₄z)w² + a₆w³`)
yields the tangency identity for `w′ = d⁄dX w`:
`w′ = 3z² + (a₁ + 2a₂z)w + (a₁z + a₂z²)w′ + a₄w² + 2(a₃ + a₄z)w·w′ + 3a₆w²·w′`. -/
theorem derivative_formalW :
    derivative R W.formalW
      = 3 * PowerSeries.X ^ 2
        + (PowerSeries.C W.a₁ + 2 * (PowerSeries.C W.a₂ * PowerSeries.X)) * W.formalW
        + (PowerSeries.C W.a₁ * PowerSeries.X + PowerSeries.C W.a₂ * PowerSeries.X ^ 2)
          * derivative R W.formalW
        + PowerSeries.C W.a₄ * W.formalW ^ 2
        + 2 * (PowerSeries.C W.a₃ + PowerSeries.C W.a₄ * PowerSeries.X) * W.formalW
          * derivative R W.formalW
        + 3 * (PowerSeries.C W.a₆ * W.formalW ^ 2) * derivative R W.formalW := by
  conv_lhs => rw [W.formalW_eq, WeierstrassCurve.wOp]
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C,
    PowerSeries.derivative_X, smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero, zero_add,
    pow_one, Nat.cast_ofNat, Nat.add_one_sub_one]
  ring

end Derivative

/-! ### Diagonal chord slope = numeric derivative, and the numeric tangency relation -/

section Diagonal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable [IsAdicComplete (maximalIdeal R).asIdeal R]
variable (W : WeierstrassCurve K) [IsIntegral R W] {z : R}

/-- The `𝔪`-adic value of the formal derivative `w′` of the Weierstrass expansion at `z`,
i.e. `w′(z) = adicEval z (d⁄dX formalW)`. -/
noncomputable def wParamDeriv (hz : z ∈ (maximalIdeal R).asIdeal) : R :=
  adicEval (maximalIdeal R).asIdeal hz (PowerSeries.derivative R (integralModel R W).formalW)

omit [IsFractionRing R K] in
/-- **The numeric tangency relation.**  The `adicEval z` image of the differentiated Weierstrass
functional equation: with `w = wParam z` and `w′ = wParamDeriv z`,
`w′ = 3z² + (a₁ + 2a₂z)w + (a₁z + a₂z²)w′ + a₄w² + 2(a₃ + a₄z)w·w′ + 3a₆w²·w′`.
This is the second relation (in place of the secant's second known point) that the doubling Vieta
closes on. -/
theorem wParamDeriv_tangency (hz : z ∈ (maximalIdeal R).asIdeal) :
    wParamDeriv R W hz = 3 * z ^ 2
      + ((integralModel R W).a₁ + 2 * (integralModel R W).a₂ * z) * wParam R W hz
      + ((integralModel R W).a₁ * z + (integralModel R W).a₂ * z ^ 2) * wParamDeriv R W hz
      + (integralModel R W).a₄ * wParam R W hz ^ 2
      + 2 * ((integralModel R W).a₃ + (integralModel R W).a₄ * z) * wParam R W hz
        * wParamDeriv R W hz
      + 3 * ((integralModel R W).a₆ * wParam R W hz ^ 2) * wParamDeriv R W hz := by
  conv_lhs => rw [wParamDeriv, (integralModel R W).derivative_formalW]
  simp only [map_add, map_mul, map_pow, map_ofNat, adicEval_X, adicEval_C]
  rw [← wParam, ← wParamDeriv]
  ring

/-! ### The doubling (tangent) third chord point is on the curve -/

end Diagonal

end WeierstrassCurve
