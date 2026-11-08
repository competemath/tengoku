module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.QuadraticSplit
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.DyadicLocalization
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.ResidualGerm
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.CoordTransfer
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.DiffeoTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Gaussian-Laplace transform of the model band germ

`hasLocalVolumeOrder_of_gaussianLaplace` reduces a local pair to two-sided
bounds on

    `∫ exp (-T · f x) · exp (-‖x‖²) dx`,

so the whole of Stage 3 rests on estimating that integral for
`f = modelBandGerm p q`.  This module performs the reduction of that integral to
a two-dimensional one, and does not yet estimate it.

The reduction is three unconditional moves and one integrability obligation:

* transport through `splitLE`, which is measure preserving, turning the integral
  over `EuclideanSpace ℝ (Fin (p + q))` into one over the product;
* Fubini, which is the only step needing integrability — supplied by
  `integrable_exp_neg_sq_norm_mul`, since `exp (-T · germ) ≤ 1`;
* the radial formula in each factor.  `integral_fun_norm_addHaar` carries no
  integrability hypothesis, so `radial_two` is unconditional and can be reused
  by any germ that depends on the two block norms alone.

After the reduction the remaining object is

    `∫₀^∞ ∫₀^∞ r^(p-1) s^(q-1) exp (-T |r² - s²|) exp (-(r² + s²)) ds dr`,

whose behaviour is `Θ(1/T)` when `p + q ≥ 3` and `Θ(log T / T)` when
`p = q = 1`.  That dichotomy is the reason the printed statement carries a
dimension hypothesis, and it is why the two-dimensional case is a genuine
boundary rather than a convenience.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set

/-- The Gaussian-weighted Laplace transform of the model band germ: the object
`hasLocalVolumeOrder_of_gaussianLaplace` asks about.-/
@[expose] public noncomputable def bandLaplace (p q : ℕ) (T : ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin (p + q)),
    Real.exp (-‖x‖ ^ 2) * Real.exp (-T * modelBandGerm p q x)

/-! ## The one-variable estimates

Both bounds are elementary once one inequality is in hand: for positive `r` and
`s`,

    `|r² - s²| = |r - s| (r + s) ≥ r |r - s|`,

so the Laplace factor is at least as sharp as a one-sided exponential of width
`1 / (T r)` around `s = r`.  The upper bound is that width times a bounded
weight; the lower bound is the same width from below, on a box where every
factor is bounded away from zero.
-/

/-- The constant in the upper bound.  Explicit rather than existential, so that a
reader can see it depends on the two block dimensions and nothing else.-/
@[expose] public noncomputable def bandUpperConst (p q : ℕ) : ℝ :=
  (p : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin p))).real (Metric.ball 0 1) *
    ((q : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1)) *
    (2 * max (1:ℝ) (Nat.factorial (q - 1) : ℝ)) *
    (∫ r in Ioi (0:ℝ), r ^ (p - 2) * Real.exp (-r ^ 2))

/-! ## The lower bound

The band is thin in one direction only, which is why the region witnessing the
lower bound cannot be a product: the first radius ranges over a fixed interval
while the second is pinned to within `1 / (4T)` of it.  On that region every
factor is bounded below by an absolute constant, and the `1/T` in the answer is
the width of the region rather than anything about the integrand.
-/

/-- The constant in the lower bound.-/
@[expose] public noncomputable def bandLowerConst (p q : ℕ) : ℝ :=
  (p : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin p))).real (Metric.ball 0 1) *
    ((q : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin q))).real (Metric.ball 0 1)) *
    Real.exp (-15) / 4

/-! ## Assembly -/

/-! ## Transport to an arbitrary congruent form

Sylvester's law of inertia says every nondegenerate real quadratic form is
congruent to a signed sum of squares.  What the volume order needs from that is
only a linear change of coordinates carrying `|Q|` to the model germ: a linear
equivalence is not measure preserving, but it distorts volume by a constant
Jacobian and balls by bounded amounts, so the pair is unchanged.  That is what
`hasLocalVolumeOrder_comp_continuousLinearEquiv` supplies.

Stating the transport separately from the construction of the change of
coordinates keeps the two obligations apart: this theorem is proved here, and a
caller who produces the coordinates from Sylvester gets the pair with nothing
further to check.
-/

/-! ## Sorting the signs of a diagonalised form

Mathlib's Sylvester's law of inertia returns a weight vector `w` with entries
`±1` and an isometry onto Mathlib's weightedSumSquares at those weights.  What
the model germ needs is
the same data with the positive entries collected first, so that the sum splits
as `‖u‖² - ‖v‖²` over two blocks.  These two lemmas do that: the first sorts the
index set, the second evaluates the sum in the sorted order.

Both are pure algebra -- no measure, no topology -- which is why they are stated
over an arbitrary index bijection rather than being tangled into the analytic
argument.
-/

/-- The coordinate sorting, as a linear equivalence onto the two blocks.  Same
shape as `splitLE` with the index bijection `τ` in place of `finSumFinEquiv`;
measure preservation is not needed here, because the transport that consumes it
allows an arbitrary constant Jacobian.-/
@[expose] public noncomputable def sortProd {n p q : ℕ} (τ : Fin p ⊕ Fin q ≃ Fin n) :
    (Fin n → ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
  (LinearEquiv.funCongrLeft ℝ ℝ τ).trans <|
    (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℝ ℝ).trans
      ((WithLp.linearEquiv 2 ℝ (Fin p → ℝ)).symm.prodCongr
        (WithLp.linearEquiv 2 ℝ (Fin q → ℝ)).symm)

/-! ## The two-dimensional boundary

At `p = q = 1` the estimate above fails, and not for want of technique: the band
`|r² - s²| ≤ 1/T` has width `1/(T r)` in the second radius at *every* radius `r`,
and with no `r^(p-1)` weight to damp it the outer integral becomes `∫ dr / r`,
which contributes a logarithm.  The lemmas here exhibit that logarithm, which is
what makes `3 ≤ p + q` a real hypothesis rather than an artefact of the proof.

The window is taken at radii `r ≥ T^(-1/2)`, below which the band is wider than
the radius itself and the argument would double-count.
-/

/-! ## The hyperbolic germ

The pairing `⟨x, y⟩` on `ℝ^H × ℝ^H` is the indefinite form the saddle Hessian
degenerates to when both diagonal blocks vanish, and by `LossExpansion` it is
what the loss germ is comparable to there.  It is a signature-`(H,H)` form, so
the model theorem applies as soon as `2 ≤ H` — which the rung condition
`k < r < H` supplies.

The change of coordinates is polarisation, `⟨x,y⟩ = ‖(x+y)/2‖² - ‖(x-y)/2‖²`, and
it is a linear equivalence rather than an isometry, which is exactly the case
`hasLocalVolumeOrder_abs_of_congruent` was stated for.
-/

/-- Polarisation as a linear equivalence of the two blocks.-/
@[expose] public noncomputable def polarPair (H : ℕ) :
    (EuclideanSpace ℝ (Fin H) × EuclideanSpace ℝ (Fin H)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin H) × EuclideanSpace ℝ (Fin H)) where
  toFun p := ((2:ℝ)⁻¹ • (p.1 + p.2), (2:ℝ)⁻¹ • (p.1 - p.2))
  invFun q := (q.1 + q.2, q.1 - q.2)
  map_add' p q := by simp [Prod.ext_iff]; constructor <;> module
  map_smul' c p := by simp [Prod.ext_iff]; constructor <;> module
  left_inv p := by simp [Prod.ext_iff]; constructor <;> module
  right_inv q := by simp [Prod.ext_iff]; constructor <;> module

/-- The polarising change of coordinates on the ambient space.-/
@[expose] public noncomputable def hyperbolicEquiv (H : ℕ) :
    EuclideanSpace ℝ (Fin (H + H)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (H + H)) :=
  ((splitLE H H).symm.trans (polarPair H)).trans (splitLE H H)

/-- **The hyperbolic germ** `|⟨x, y⟩|`, read on the ambient space through the
block split.-/
@[expose] public noncomputable def hyperbolicGerm (H : ℕ)
    (w : EuclideanSpace ℝ (Fin (H + H))) : ℝ :=
  |inner ℝ ((splitLE H H).symm w).1 ((splitLE H H).symm w).2|

end AISafetyAtlas.SingularLearning
