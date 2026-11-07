/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import Tengoku.Arklib.ArkLib.Data.Polynomial.Bivariate
public import Tengoku.Seed.FieldTheory.RatFunc.AsPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trivariate Polynomials

We define trivariate polynomials to match their representation in statements and proofs of
[BCIKS20]. A value of type `F[Z][X][Y]` is nested with `Y` outermost, `X` in the middle, and `Z`
innermost. The semantic evaluation and degree operations in this namespace make those axes explicit.

Applying `Polynomial.Bivariate` operations directly to `F[Z][X][Y]` instead treats it as a
bivariate polynomial over `F[Z]`. In particular, its `evalX` specializes the middle `X` variable,
while its `totalDegree` measures only `(X, Y)` and ignores `Z`.

## Main Definitions

### Notation, evaluation, and degree projections
- `eval_on_Z₀`: Evaluate a rational function on a point.
- `evalAtX`, `evalAtY`, `evalAtZ`: Evaluate the named variable of a trivariate polynomial.
- `degreeInX`, `degreeInY`, `degreeInZ`: The degree in one named variable.
- `degreeXY`, `degreeYZ`, `totalDegreeXYZ`: The projected or full total degrees.
- `toRatFuncPoly`: Maps a trivariate polynomial to a bivariate polynomial over the rational
  function field.
- `D_Y`: The `Y`-degree of a trivariate polynomial.
- `D_YZ`: The `YZ`-degree of a trivariate polynomial.

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/

@[expose] public section

namespace Trivariate

open Polynomial Bivariate

scoped notation3:max R "[Z][X]" => Polynomial (Polynomial R)

scoped notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial R))

scoped notation3:max "Y" => Polynomial.X
scoped notation3:max "X" => Polynomial.C Polynomial.X
scoped notation3:max "Z" => Polynomial.C (Polynomial.C Polynomial.X)

section Semiring

variable {R : Type*} [CommSemiring R]

/-- Evaluate the innermost `Z` variable of `p : R[Z][X][Y]` at `z`, leaving a polynomial in
`(X, Y)`.-/
noncomputable def evalAtZ (z : R) (p : R[Z][X][Y]) : R[X][Y] :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

/-- Backwards-compatible name for `evalAtZ`. New code should use the axis-explicit API.-/
@[deprecated evalAtZ (since := "2026-08-21")]
noncomputable abbrev eval_on_Z (p : R[Z][X][Y]) (z : R) : R[X][Y] :=
  evalAtZ z p

/-- The maximum exponent of the innermost `Z` variable in a trivariate polynomial.-/
noncomputable def degreeInZ (p : R[Z][X][Y]) : ℕ :=
  p.support.sup fun j => (p.coeff j).support.sup fun i => ((p.coeff j).coeff i).natDegree

/-- `evalAtZ` is the coefficient-wise evaluation map on the innermost variable.-/
theorem evalAtZ_eq_map_map_evalRingHom (z : R) (p : R[Z][X][Y]) :
    evalAtZ z p = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  rfl

end Semiring

/-! ### Axis regression checks

The unequal exponents in this monomial make accidental permutations observable. In particular,
the `(X, Y)` projection is `10`, the `(Y, Z)` projection is `8`, and the full degree is `15`.
-/

private noncomputable def axisRegressionPolynomial :
    Polynomial (Polynomial (Polynomial ℚ)) :=
  Polynomial.monomial 3 (Polynomial.monomial 7 (Polynomial.monomial 5 1))

section Field

variable {F : Type*} [Field F] [DecidableEq (RatFunc F)]

/-- Evaluate a rational function on a point.-/
noncomputable def eval_on_Z₀ (p : RatFunc F) (z : F) : F :=
  RatFunc.eval (RingHom.id _) z p

open Polynomial.Bivariate in
/-- A ring homomorphism mapping a trivariate polynomial to an element in the field of rational
functions of polynomial ring in two variables.-/
noncomputable def toRatFuncPoly (p : F[Z][X][Y]) : (RatFunc F)[X][Y] :=
  p.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

end Field

end Trivariate
-- Tengoku: 5 notation(s) of this module made scoped so they do not change other libraries (generated)
