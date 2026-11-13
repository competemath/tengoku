import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Chapter04

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chapter 4 — Theorem 4.3 (Jacobi's identity)

**Goal**: `(q;q)_∞^3 = ∑_{n≥0} (-1)^n (2n+1) q^{n(n+1)/2}` for `‖q‖ < 1`.

**Strategy** (see `docs/T43_strategy.md`). Parameterise by `Q : ℂ` with
`Q² = q`. JTP at base `Q`:
```
J(Q, z) = ∑_{n∈ℤ} z^n · Q^(n²) = ∏_{n≥1}(1 - Q^(2n))(1 + zQ^(2n-1))(1 + z⁻¹Q^(2n-1)).
```
At `z = -Q` both sides vanish (the `n=1` factor `(1 + z⁻¹Q)|_{z=-Q} = 0`).
Differentiate in `z`, evaluate at `z = -Q`:

* Series:  `dS/dz|_{z=-Q} = -Q⁻¹ · ∑_{n≥0}(2n+1)(-1)^n q^(n(n+1)/2)`.
* Product: `dP/dz|_{z=-Q} = -Q⁻¹ · (q;q)_∞^3`.

JTP gives equality of functions, hence of derivatives. Cancel `-Q⁻¹`.
Lift via `Complex.exists_sq` for the final wrapper.

This module sets up Phase 1: series-side termwise derivative.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch04

section Theorem43

open scoped Topology
open Filter

/-- The `n`-th term of the bilateral JTP series: `z ↦ z^n · Q^{n²}`.-/
noncomputable def jacobiSeriesT (Q : ℂ) (n : ℤ) : ℂ → ℂ :=
  fun z => z ^ n * Q ^ (n ^ 2)

/-- The termwise derivative: `(n : ℂ) · z^(n-1) · Q^{n²}`.-/
noncomputable def jacobiSeriesT' (Q : ℂ) (n : ℤ) : ℂ → ℂ :=
  fun z => (n : ℂ) * z ^ (n - 1) * Q ^ (n ^ 2)

/-! ## Summability of the derivative-bound series

We need summability of the uniform bound
`u(n) := (n.natAbs : ℝ) * R^(n.natAbs+1) * ‖Q‖^(n.natAbs * n.natAbs)`
over `n : ℤ` (and equivalently over `n : ℕ` via the `int_iff_nat_and_neg`
split). The key fact: `‖Q‖^(n*n)` provides Gaussian-style super-exponential
decay that dominates any polynomial-times-geometric bound on the rest.
-/

/-! ## The series derivative theorem

The series side `J(Q, z) = ∑_{n∈ℤ} z^n · Q^{n²}` is differentiable in `z`
on the punctured plane, with derivative given by termwise differentiation.
-/

/-! ## Phase 2: the product-side derivative at `z = -Q`

We factor the JTP infinite product as

  `jacobiInfiniteProduct Q z = (1 + z⁻¹ Q) · P_mod(z)`

where `P_mod` collects the other factors. At `z = -Q` the first factor
vanishes, so `(jacobiInfiniteProduct Q)' (-Q) = ((1 + z⁻¹ Q))' (-Q) · P_mod (-Q)`.

* `(1 + z⁻¹ Q)' (-Q) = -Q⁻¹` (computed below).
* `P_mod (-Q) = (q;q)_∞ ^ 3`  (uses partial-product limit + Ch02 multipliability).
-/

/-- Derivative of the vanishing factor `z ↦ 1 + z⁻¹ Q` at `z = -Q` is `-Q⁻¹`.-/
theorem hasDerivAt_oneAddInvMul_negQ {Q : ℂ} (hQ_ne : Q ≠ 0) :
    HasDerivAt (fun z : ℂ => 1 + z⁻¹ * Q) (-Q⁻¹) (-Q) := by
  have hnegQ_ne : (-Q : ℂ) ≠ 0 := neg_ne_zero.mpr hQ_ne
  -- d/dz(z⁻¹) = -(z²)⁻¹ at z = -Q ≠ 0
  have h1 : HasDerivAt (fun z : ℂ => z⁻¹) (-((-Q : ℂ) ^ 2)⁻¹) (-Q) := hasDerivAt_inv hnegQ_ne
  -- d/dz(z⁻¹ * Q) = -(z²)⁻¹ * Q
  have h2 : HasDerivAt (fun z : ℂ => z⁻¹ * Q) (-((-Q : ℂ) ^ 2)⁻¹ * Q) (-Q) := h1.mul_const Q
  -- d/dz(1 + z⁻¹ * Q) is the same derivative
  have h3 : HasDerivAt (fun z : ℂ => 1 + z⁻¹ * Q) (-((-Q : ℂ) ^ 2)⁻¹ * Q) (-Q) :=
    h2.const_add 1
  -- Simplify: -((-Q)²)⁻¹ * Q = -Q⁻¹
  have hval : -((-Q : ℂ) ^ 2)⁻¹ * Q = -Q⁻¹ := by
    have hsq : (-Q : ℂ) ^ 2 = Q ^ 2 := by ring
    rw [hsq]; field_simp
  rw [← hval]
  exact h3

/-- Product rule shortcut: if `g x = 0` then `(g · R)'(x) = g'(x) · R(x)`,
provided only that `R` is continuous at `x` (no derivative needed for `R`).

Proof via the slope characterization of `HasDerivAt`:
`(g(y)·R(y) - 0) / (y - x) = (g(y) - g(x))/(y-x) · R(y) → g'(x) · R(x)`.-/
theorem hasDerivAt_mul_of_left_vanish {g R : ℂ → ℂ} {g' x : ℂ}
    (hg : HasDerivAt g g' x) (hg0 : g x = 0) (hR : ContinuousAt R x) :
    HasDerivAt (fun z => g z * R z) (g' * R x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h_slope_g : Tendsto (fun y => (y - x)⁻¹ • (g y - g x)) (𝓝[≠] x) (𝓝 g') := by
    rw [hasDerivAt_iff_tendsto_slope] at hg
    exact hg
  have h_slope_g' : Tendsto (fun y => (y - x)⁻¹ • g y) (𝓝[≠] x) (𝓝 g') := by
    refine h_slope_g.congr' ?_
    filter_upwards with y
    rw [hg0]; simp
  have hR_lim : Tendsto R (𝓝[≠] x) (𝓝 (R x)) :=
    (hR.tendsto).mono_left nhdsWithin_le_nhds
  -- Slope of (g·R) at x: (y-x)⁻¹ · (g(y)R(y) - 0) = ((y-x)⁻¹ · g(y)) · R(y)
  have h_mul : Tendsto (fun y => (y - x)⁻¹ • (g y * R y - g x * R x))
      (𝓝[≠] x) (𝓝 (g' * R x)) := by
    refine (h_slope_g'.mul hR_lim).congr' ?_
    filter_upwards with y
    rw [hg0]; simp; ring
  exact h_mul

/-! ### Local summability for shifted odd-factor family

`ℂ` is a CommMonoid (not CommGroup) under multiplication, so we cannot use
`Multipliable.tprod_eq_zero_mul` (which needs CommGroup). Instead we use
`tprod_eq_zero_mul'`, which requires multipliability of the shifted family.
We build that from `multipliable_one_add_of_summable` and a local geometric bound. -/

/-! ### Evaluation of `P_mod(-Q) = (q;q)_∞^3` -/

/-! ### Phase 3: series-side reindex

The bilateral series derivative at `z = -Q` reindexes via pairing `n ↔ -1 - n`
to a one-sided sum:
`∑' n : ℤ, jacobiSeriesT' Q n (-Q) = -Q⁻¹ · ∑' n : ℕ, (-1)^n · (2n+1) · Q^(n(n+1))`. -/

/-! ### Phase 3 → 2 bridge: transfer derivative via JTP S = P -/

/-! ### Phase 2 finish: continuity of `P_mod` at `-Q`

Uses `hasProdUniformlyOn_nat_one_add` (from Mathlib) on a closed ball around `-Q`. -/

/-! ### Phase 2 finish: derivative of `jacobiInfiniteProduct` at `-Q` -/

/-! ### Phase 4: Jacobi's identity in Q-parameterised form -/

/-! ### Phase 4: q-parameterised Jacobi's identity -/

end Theorem43

end Ch04
end PartI
end QseriesFormalization
