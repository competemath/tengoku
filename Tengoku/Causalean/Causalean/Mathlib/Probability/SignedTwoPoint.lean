/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.BernoulliMeasure
public import Tengoku

/-! # Symmetric signed two-point mean channel

The symmetric two-point outcome law `twoPointMean B u` supported on `{−B, B}` with mean `u`:
`Q_u(B) = (1 + u/B)/2`, `Q_u(−B) = (1 − u/B)/2`.  It is the affine image of the `{0,1}` Bernoulli
law `bernoulliLaw` under `x ↦ 2Bx − B`, which lets its Kullback–Leibler divergence inherit the
quadratic band of the Bernoulli KL.

This file provides:

* `twoPointMean` — the signed two-point channel, with `measurable_twoPointMean`,
  `twoPointMean_isProbabilityMeasure`, `twoPointMean_integral`, `twoPointMean_mean`,
  `twoPointMean_bad_support_zero`;
* `klDiv_map_measurableEquiv` — KL-divergence invariance under a measurable equivalence;
* `twoPointMean_eq_map_bernoulli` — the affine-image representation;
* `bernoulli_mean_channel_kl` — the KL band `KL(Q_u, Q_v) ≤ (u − v)²/B²` for `|u|,|v| ≤ B/2`.

It is the reusable least-favorable outcome channel for two-point / Le Cam minimax lower bounds in
a mean-estimation setting.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability

open MeasureTheory

open scoped ENNReal

/-- For [a real scale](hyp:B) and [a real target mean](hyp:u), [the symmetric two-point mean
measure](goal) is the sum of a point mass at $B$ weighted by $\max((1+u/B)/2,0)$ and a point
mass at $-B$ weighted by $\max((1-u/B)/2,0)$. -/
noncomputable def twoPointMean (B u : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 + u / B) / 2) • Measure.dirac B
    + ENNReal.ofReal ((1 - u / B) / 2) • Measure.dirac (-B)

/-- When the scale is positive and the target mean lies within that scale, both
weights in the signed two-point distribution are nonnegative. -/
lemma twoPointMean_coef_nonneg {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B) :
    0 ≤ (1 + u / B) / 2 ∧ 0 ≤ (1 - u / B) / 2 := by
  have hbounds := abs_le.mp hu
  constructor <;> field_simp [ne_of_gt hB] <;> nlinarith [hbounds.1, hbounds.2, hB]

/-- **KL-divergence is invariant under a measurable equivalence.**  Pushing both finite measures
`μ, ν` forward through a measurable equivalence `e` leaves their Kullback–Leibler divergence
unchanged: `KL(e_* μ, e_* ν) = KL(μ, ν)`. -/
lemma klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv (Measure.map e μ) (Measure.map e ν) =
      InformationTheory.klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  · have hmap : Measure.map e μ ≪ Measure.map e ν := hμν.map e.measurable
    rw [InformationTheory.klDiv_eq_lintegral_klFun,
      InformationTheory.klDiv_eq_lintegral_klFun, ite_eq_left hmap, ite_eq_left hμν]
    rw [e.measurableEmbedding.lintegral_map]
    refine lintegral_congr_ae ?_
    exact (e.measurableEmbedding.rnDeriv_map μ ν).mono fun _ hx => by
      simpa using congrArg
        (fun y : ℝ≥0∞ => ENNReal.ofReal (InformationTheory.klFun y.toReal)) hx
  · have hmap_not : ¬ Measure.map e μ ≪ Measure.map e ν := by
      intro hmap
      apply hμν
      have hback :
          Measure.map e.symm (Measure.map e μ) ≪ Measure.map e.symm (Measure.map e ν) :=
        hmap.map e.symm.measurable
      simpa [Measure.map_map, Function.comp_def] using hback
    rw [InformationTheory.klDiv_eq_lintegral_klFun,
      InformationTheory.klDiv_eq_lintegral_klFun, ite_eq_right hmap_not, ite_eq_right hμν]

end Causalean.Mathlib.Probability
