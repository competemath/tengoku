/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentMartingale
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentChernoff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From one-sided MGF certificates to optimized CVaR bounds

This module connects the probabilistic certificate API to the deterministic
Chernoff calculus.  It contains no martingale-specific construction: any
integrable random variable with the appropriate one-sided MGF certificate
inherits the optimized bound.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A one-sided MGF certificate may be enlarged pointwise on nonnegative
Laplace parameters.-/
theorem HasOneSidedMGF.mono_exponent
    {X : Omega → ℝ} {psi phi : ℝ → ℝ}
    (hmgf : HasOneSidedMGF X psi mu)
    (hpsi : ∀ t, 0 ≤ t → psi t ≤ phi t) :
    HasOneSidedMGF X phi mu := by
  refine
    { aemeasurable := hmgf.aemeasurable
      integrable_exp_mul := hmgf.integrable_exp_mul
      mgf_le := ?_ }
  intro t ht
  exact (hmgf.mgf_le t ht).trans (Real.exp_monotone (hpsi t ht))

/-- Taking the infimum over all positive Laplace parameters turns the
parameterized exponential CVaR estimate into a Chernoff transform.-/
theorem HasOneSidedMGF.conditionalValueAtRisk_le_chernoffTransform
    [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {psi : ℝ → ℝ}
    (hmgf : HasOneSidedMGF X psi mu) (hX : Integrable X mu)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    conditionalValueAtRisk alpha X mu ≤
      chernoffTransform psi (-Real.log alpha) := by
  unfold chernoffTransform
  apply le_csInf (Set.range_nonempty _)
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  unfold chernoffObjective
  have h := hmgf.conditionalValueAtRisk_le
    hX halpha0 halpha1 t.property
  rw [← sub_eq_add_neg]
  exact h

/-- Optimized exact-series CVaR bound after interpolation of all moments
between orders two and `q`.  The sole remaining deterministic term is Rio's
finite intermediate series; it vanishes at `q = 3`.-/
theorem HasOneSidedMGF.conditionalValueAtRisk_le_rioStrongMoment
    [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : Integrable X mu)
    (q : ℕ) (hq : 3 ≤ q)
    {y second V Q alpha : ℝ} {moment : ℕ → ℝ}
    (hy : 0 < y) (hV : 0 < V) (hQ : 0 ≤ Q)
    (hsecond : second ≤ V)
    (hmiddle : ∀ k ∈ Finset.Ico 3 q,
      moment k ≤ interpolatedStrongMomentCoefficient q V Q k)
    (hmomentQ : moment q ≤ Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hscale : Q * Real.exp (-Real.log alpha) ≤ y ^ q)
    (hmgf : HasOneSidedMGF X
      (strongMomentSeriesExponent q · y second moment) mu) :
    conditionalValueAtRisk alpha X mu ≤
      Real.sqrt (2 * V * (-Real.log alpha)) +
        y + y / (q : ℝ) +
          (y / (-Real.log alpha)) *
            strongMomentIntermediateExponent q V Q
              ((-Real.log alpha) / y) := by
  have hx : 0 < -Real.log alpha := neg_pos.mpr
    (Real.log_neg halpha0 halpha1)
  have hseriesLe : ∀ t : ℝ, 0 ≤ t →
      strongMomentSeriesExponent q t y second moment ≤
        rioStrongMomentExponent q V Q y t := by
    intro t ht
    exact strongMomentSeriesExponent_le_rioStrongMomentExponent
      q ht hy hsecond hmiddle hmomentQ
  have hrio : HasOneSidedMGF X (rioStrongMomentExponent q V Q y) mu :=
    hmgf.mono_exponent hseriesLe
  have hcvar := hrio.conditionalValueAtRisk_le_chernoffTransform
    hX halpha0 halpha1.le
  exact hcvar.trans
    (chernoffTransform_rioStrongMomentExponent_le q hq hV hQ hy hx hscale)

end ProbabilityTheory
