/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.CVaRDenseSupremum
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentRioMartingale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Confidence form of Rio's strong-moment bound

The optimized martingale endpoint is naturally stated with a free truncation
level `y` subject to `Q / alpha <= y^q`.  This file makes the canonical choice

`y = Q^(1/q) * alpha^(-1/q)`

and absorbs the exact residual into one additional `y / q`.  It also packages
the atomless CVaR-to-tail conversion used by continuous empirical-process
applications.
-/

open Real Set MeasureTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The canonical order-`q` confidence scale associated with aggregate
moment `Q` and upper-tail mass `alpha`.-/
def rioConfidenceScale (q : Nat) (Q alpha : Real) : Real :=
  strongMomentQScale q Q * (1 / alpha) ^ (1 / (q : Real))

theorem rioConfidenceScale_pos
    {q : Nat} {Q alpha : Real}
    (hQ : 0 < Q) (halpha : 0 < alpha) :
    0 < rioConfidenceScale q Q alpha := by
  unfold rioConfidenceScale
  exact mul_pos (strongMomentQScale_pos hQ)
    (Real.rpow_pos_of_pos (one_div_pos.mpr halpha) _)

/-- Raising the canonical confidence scale to order `q` gives exactly
`Q / alpha`.-/
theorem rioConfidenceScale_pow
    {q : Nat} (hq : 1 <= q) {Q alpha : Real}
    (hQ : 0 < Q) (halpha : 0 < alpha) :
    rioConfidenceScale q Q alpha ^ q = Q * alpha⁻¹ := by
  have hroot : ((1 / alpha) ^ (1 / (q : Real))) ^ q = 1 / alpha := by
    simpa only [one_div] using
      (Real.rpow_inv_natCast_pow (le_of_lt (one_div_pos.mpr halpha))
        (by omega : q ≠ 0))
  unfold rioConfidenceScale
  rw [mul_pow, strongMomentQScale_pow hq hQ, hroot]
  simp only [one_div]

/-- The canonical confidence scale satisfies Rio's scale constraint with
equality.-/
theorem rio_scale_condition
    {q : Nat} (hq : 1 <= q) {Q alpha : Real}
    (hQ : 0 < Q) (halpha : 0 < alpha) :
    Q * Real.exp (-Real.log alpha) <=
      rioConfidenceScale q Q alpha ^ q := by
  rw [rioConfidenceScale_pow hq hQ halpha, Real.exp_neg,
    Real.exp_log halpha]

/-- Explicit confidence radius obtained from Rio's exact CVaR endpoint after
the canonical choice of truncation scale.-/
def rioStrongMomentConfidenceRadius
    (q : Nat) (V Q alpha : Real) : Real :=
  Real.sqrt (2 * V * (-Real.log alpha)) +
    (1 + 2 / (q : Real)) * rioConfidenceScale q Q alpha +
      Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3

/-- The exact residual term in Rio's endpoint is absorbed by the confidence
radius.-/
theorem rio_explicit_bound_le_confidenceRadius
    {q : Nat} (hq : 3 <= q) {V Q alpha : Real}
    (hQ : 0 < Q) (halpha0 : 0 < alpha) :
    Real.sqrt (2 * V * (-Real.log alpha)) +
          (1 + 1 / (q : Real)) * rioConfidenceScale q Q alpha +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
          alpha⁻¹ *
            (Q / ((q : Real) * rioConfidenceScale q Q alpha ^ (q - 1))) <=
      rioStrongMomentConfidenceRadius q V Q alpha := by
  have hy : 0 < rioConfidenceScale q Q alpha :=
    rioConfidenceScale_pos hQ halpha0
  have hresidual :
      alpha⁻¹ *
          (Q / ((q : Real) * rioConfidenceScale q Q alpha ^ (q - 1))) <=
        rioConfidenceScale q Q alpha / (q : Real) :=
    inv_mul_strongMomentResidual_le_div q (by omega) hy halpha0
      (rio_scale_condition (by omega) hQ halpha0)
  calc
    Real.sqrt (2 * V * (-Real.log alpha)) +
          (1 + 1 / (q : Real)) * rioConfidenceScale q Q alpha +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
          alpha⁻¹ *
            (Q / ((q : Real) * rioConfidenceScale q Q alpha ^ (q - 1))) <=
        Real.sqrt (2 * V * (-Real.log alpha)) +
          (1 + 1 / (q : Real)) * rioConfidenceScale q Q alpha +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
          rioConfidenceScale q Q alpha / (q : Real) :=
      add_le_add_right hresidual _
    _ = rioStrongMomentConfidenceRadius q V Q alpha := by
      unfold rioStrongMomentConfidenceRadius
      ring

/-- Any CVaR estimate in the exact Rio form implies the packaged confidence
radius.-/
theorem conditionalValueAtRisk_le_rioStrongMomentConfidenceRadius
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {X : Omega -> Real} {q : Nat} (hq : 3 <= q) {V Q alpha : Real}
    (hQ : 0 < Q) (halpha0 : 0 < alpha)
    (hRio :
      conditionalValueAtRisk alpha X mu <=
        Real.sqrt (2 * V * (-Real.log alpha)) +
          (1 + 1 / (q : Real)) * rioConfidenceScale q Q alpha +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
          alpha⁻¹ *
            (Q / ((q : Real) * rioConfidenceScale q Q alpha ^ (q - 1)))) :
    conditionalValueAtRisk alpha X mu <=
      rioStrongMomentConfidenceRadius q V Q alpha :=
  hRio.trans (rio_explicit_bound_le_confidenceRadius hq hQ halpha0)

/-- On an atomless probability space, the packaged Rio CVaR estimate gives
the corresponding strict upper-tail probability bound.-/
theorem measureReal_rioStrongMomentConfidenceRadius_lt_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    (hmu : RandomSetTheory.IsAtomlessMeasure mu)
    {X : Omega -> Real} (hXmeas : Measurable X) (hX : Integrable X mu)
    {q : Nat} (hq : 3 <= q) {V Q alpha : Real}
    (hQ : 0 < Q) (halpha0 : 0 < alpha) (halpha1 : alpha <= 1)
    (hRio :
      conditionalValueAtRisk alpha X mu <=
        Real.sqrt (2 * V * (-Real.log alpha)) +
          (1 + 1 / (q : Real)) * rioConfidenceScale q Q alpha +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
          alpha⁻¹ *
            (Q / ((q : Real) * rioConfidenceScale q Q alpha ^ (q - 1)))) :
    mu.real {omega |
      rioStrongMomentConfidenceRadius q V Q alpha < X omega} <= alpha := by
  apply measureReal_lt_le_of_conditionalValueAtRisk_le_of_atomless
    hmu hXmeas hX halpha0 halpha1
  exact conditionalValueAtRisk_le_rioStrongMomentConfidenceRadius
    hq hQ halpha0 hRio

end ProbabilityTheory
