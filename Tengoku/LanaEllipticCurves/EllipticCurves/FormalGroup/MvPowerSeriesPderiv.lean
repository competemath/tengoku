/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.RingTheory.PowerSeries.Substitution
import Tengoku.Seed.Algebra.Polynomial.Derivation
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.MvPowerSeriesCurry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `z₂`-partial derivative on `MvPowerSeries (Fin 2) R`

This Mathlib pin provides the univariate formal derivative
`PowerSeries.derivativeFun` / `PowerSeries.derivative : Derivation R R⟦X⟧ R⟦X⟧`
but has **no** partial-derivative operator on `MvPowerSeries`.  For the invariant-differential
argument behind log-additivity of the Weierstrass formal group
(`EllipticCurves.FormalGroup.LogAdditivity`, Silverman AEC IV.5) we need to differentiate a
bivariate series in its *second* variable `z₂`.

We obtain such an operator for free by transporting the univariate `derivativeFun` on the outer
`z₂`-variable across the currying ring isomorphism
`mvPowerSeriesFinTwoCurry : MvPowerSeries (Fin 2) R ≃+* R⟦z₁⟧⟦z₂⟧`
(`EllipticCurves.FormalGroup.MvPowerSeriesCurry`; the *outer* index `1` is `z₂`, the *inner*
index `0` is `z₁`).

## Main definitions and results

* `MvPowerSeries.pderivSnd : MvPowerSeries (Fin 2) R → MvPowerSeries (Fin 2) R` — the `z₂`-partial
  derivative, `curry.symm ∘ derivativeFun ∘ curry`.
* `MvPowerSeries.coeff_coeff_pderivSnd` — its bigraded coefficient formula: the `z₂`-degree `n` is
  bumped to `n + 1` and scaled by `n + 1`.
* Transported `Derivation`-style API: `pderivSnd_add`, `pderivSnd_zero`, `pderivSnd_smul`,
  `pderivSnd_mul` (Leibniz), `pderivSnd_C`, `pderivSnd_X_zero` (`∂_{z₂} z₁ = 0`),
  `pderivSnd_X_one` (`∂_{z₂} z₂ = 1`).
* `MvPowerSeries.pderivSndDerivation : Derivation R (MvPowerSeries (Fin 2) R) _` — `pderivSnd`
  packaged as a genuine `R`-linear `Derivation` (it is `R`-linear, kills `C r` and `X 0`, and sends
  `X 1 ↦ 1`), so the whole `Derivation` API (iterated Leibniz, the power rule, …) is available on it
  for free.
* `MvPowerSeries.pderivSnd_pow` — the power rule `∂_{z₂}(φ ^ n) = n • φ ^ (n-1) • ∂_{z₂}φ`, the
  inductive core of the substitution chain rule.
* `MvPowerSeries.coeff_pderivSnd` — the single-index `MvPowerSeries.coeff` form of the coefficient
  formula.
* `MvPowerSeries.pderivSnd_subst_coe` — the **chain rule, polynomial case**: for `p : R[X]` and a
  substitutable `G`, `∂_{z₂}(p(G)) = p'(G) · ∂_{z₂}G` (via `Derivation.comp_aeval_eq`).
* `MvPowerSeries.pderivSnd_subst` — the **substitution chain rule** in full generality: for a
  univariate `f : R⟦X⟧` and a substitutable bivariate `G` (`constantCoeff G = 0`),
  `∂_{z₂}(f.subst G) = (f.derivativeFun.subst G) · ∂_{z₂}G`.  This is the `Fin 2`-graded analogue of
  `PowerSeries.derivative_subst`, and the key calculus input for the invariant-differential form of
  log-additivity (`EllipticCurves.FormalGroup.LogAdditivity`, `#315`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.5.
-/

open scoped PowerSeries

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

/-! ### The substitution chain rule

`pderivSnd (f.subst G) = (f.derivativeFun.subst G) * pderivSnd G` for a univariate `f : R⟦X⟧` and a
substitutable bivariate `G` (`constantCoeff G = 0`, i.e. `PowerSeries.HasSubst G`).  We follow the
model of Mathlib's `PowerSeries.derivative_subst`: first the polynomial case via
`Derivation.comp_aeval_eq` on `pderivSndDerivation`, then the general case by a finite-truncation
argument.  (The obstruction noted in `LogAdditivity` — that currying `G` to `R⟦z₁⟧⟦z₂⟧` and applying
`PowerSeries.derivative_subst` fails because the `z₂`-constant coefficient `G(z₁, 0)` is
non-nilpotent — is why the argument is carried out directly in the `Fin 2` grading.) -/

end MvPowerSeries
