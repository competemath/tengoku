module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.ResidualLaplace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The scalar residual germ, unconditionally

`ResidualLaplace.lean` reduces the Gaussian-weighted Laplace transform of `residualGerm p n h`
to an integral over `X` alone, and that reduction — `gaussianLaplace_residualGerm_eq_det` — is
**unconditional**. The eigenvalue law enters only afterwards, to evaluate the determinant
integral in general.

At the smallest singular shape `p = n = h = 1` it does not have to. There `X` is a single real
number, the determinant is `1 + T x²`, and the integral is

    J(T) = ∫_ℝ e^{-x²} (1 + T x²)^{-1/2} dx ,

which this module sandwiches between two multiples of `T^{-1/2} log T` by an elementary split at
`|x| = T^{-1/2}`. Feeding those bounds to `hasLocalVolumeOrder_of_gaussianLaplace`, itself
frontier-free, gives the local pair of `x²y²` with **no hypothesis at all**.

## Why this shape and not another

`residualGerm 1 1 1` is `‖YX‖²_F` at `1×1`, that is `x²y²`. It is the smallest germ in the
family whose multiplicity is `2` rather than `1`, and it is the verification plan's V2b: the
anti-vacuity witness that shows `HasLocalVolumeOrder` is inhabited somewhere *singular*, not
only at the regular quadratic of `hasExactLocalPair_quadraticGerm`. Proved under
`EigenvalueLawStatement` it could not serve that purpose, because a witness standing behind a
hypothesis with no known inhabitant is not a witness.

## The estimate

Both bounds come from the same two facts and a split at `δ = T^{-1/2}`:

* `(1 + T x²)^{-1/2} ≤ 1` everywhere, and `≤ 1/(√T |x|)` everywhere, so the inner interval
  contributes at most its length `2δ` and the outer one at most `(2/√T) ∫_δ^∞ e^{-x²}/x`, which
  splits again at `1` into `(1/2) log T` and a tail below `e^{-1}`;
* on `δ ≤ x ≤ 1` we have `1 ≤ T x²`, hence `1 + T x² ≤ 2 T x²` and
  `(1 + T x²)^{-1/2} ≥ 1/(√2 √T x)`, while `e^{-x²} ≥ e^{-1}`, so that interval alone already
  contributes `≍ T^{-1/2} log T`.

Nothing here is asymptotic in the sense of a limit: both bounds hold at every `T ≥ 3`, which is
the hypothesis `hasLocalVolumeOrder_of_gaussianLaplace` wants.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set
open scoped Matrix

/-- `J(T)`, the one-dimensional integral the `1×1` determinant integral collapses to.-/
@[expose] public noncomputable def scalarJ (T : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-x ^ 2) * (1 + T * x ^ 2) ^ (-(1 : ℝ) / 2)

/-! ## Pointwise facts about the integrand -/

variable {T : ℝ}

/-! ## Integrability -/

/-! ## The lower bound

On `T^{-1/2} ≤ x ≤ 1` we have `1 ≤ T x²`, so `1 + T x² ≤ 2 T x²` and the factor is at least
`1/(√2 √T x)`; the Gaussian is at least `e^{-1}`. That interval alone contributes
`≍ T^{-1/2} log T`. -/

/-! ## The upper bound

The integrand depends on `x` only through `x²`, so it is `g |x|` for the same `g`, and
`integral_comp_abs` halves the line. On `(0, ∞)` the estimate splits at `δ = T^{-1/2}` and at
`1`: below `δ` the integrand is at most `1`, between `δ` and `1` it is at most `1/(√T y)` whose
integral is the logarithm, and above `1` the Gaussian is integrable and `1/(√T y) ≤ 1/√T`. -/

/-! ## From the `1×1` determinant integral to `J` -/

/-- A `1×1` real matrix is a real number, measurably and measure-preservingly.-/
@[expose] public noncomputable def matrixOneEquiv : Matrix (Fin 1) (Fin 1) ℝ ≃ᵐ ℝ :=
  (MeasurableEquiv.funUnique (Fin 1) (Fin 1 → ℝ)).trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-! ## V2b, with no hypothesis -/

end AISafetyAtlas.SingularLearning
