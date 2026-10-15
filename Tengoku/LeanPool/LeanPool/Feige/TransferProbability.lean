/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku

/-!
# Exponential tail formulas used by the transfer identity

This file supplies the reusable one-dimensional probability calculations
behind the local exponential transfer step.  They are stated for Mathlib's
rate-one exponential measure.  In particular, the strict and non-strict
tails agree, since this measure has no atoms.
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal

namespace Feige

open ProbabilityTheory

namespace ExponentialTransfer

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- The rate-one exponential distribution has no atoms.
@isnad1 id=eq.0h1v.s5.4abc5a526c17 from=translated src=- shape=4c88cf79 vocab=2498c623
-/
theorem expMeasure_one_singleton (x : ℝ) :
    expMeasure 1 {x} = 0 := by
  simp [expMeasure, gammaMeasure]

/-- The rate-one exponential upper tail, in strict form.
@isnad1 id=eq.1h1v.s5.237123a898a8 from=translated src=- shape=7e028e7d vocab=ec1ca806
-/
theorem expMeasure_one_Ioi {x : ℝ} (hx : 0 ≤ x) :
    expMeasure 1 (Ioi x) = ENNReal.ofReal (exp (-x)) := by
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
    measure_univ, ← ofReal_cdf, cdf_expMeasure_eq one_pos, ite_eq_left hx]
  simp only [one_mul]
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr (exp_le_one_iff.mpr (by linarith)))]
  congr 1
  ring

/-- The rate-one exponential upper tail, in non-strict form.
@isnad1 id=eq.1h1v.s5.4797fb8384ea from=translated src=- shape=7e028e7d vocab=8d96f394
-/
theorem expMeasure_one_Ici {x : ℝ} (hx : 0 ≤ x) :
    expMeasure 1 (Ici x) = ENNReal.ofReal (exp (-x)) := by
  have hdecomp : Ici x = {x} ∪ Ioi x := by ext y; simp [le_iff_eq_or_lt]
  rw [hdecomp, measure_union (by simp) measurableSet_Ioi]
  rw [expMeasure_one_singleton, zero_add, expMeasure_one_Ioi hx]

/-- Conditional `u`-integrand calculation.  If `d > 0`, the exponential
probability of `z < dE'`, subject to `z ≥ 0`, is `exp (-z/d)`.
@isnad1 id=eq.1h2v.s6.bb118d44b7fe from=translated src=- shape=4d074d37 vocab=160555c1
-/
theorem measure_lt_mul_exp
    {z d : ℝ} (hd : 0 < d) :
    expMeasure 1 {e : ℝ | 0 ≤ z ∧ z < d * e} =
      ENNReal.ofReal (if 0 ≤ z then exp (-z / d) else 0) := by
  by_cases hz : 0 ≤ z
  · have hset : {e : ℝ | 0 ≤ z ∧ z < d * e} = Ioi (z / d) := by
      ext e
      simp only [mem_ofPred_eq, hz, true_and, mem_Ioi]
      exact (div_lt_iff₀' hd).symm
    rw [hset, expMeasure_one_Ioi (div_nonneg hz hd.le), ite_eq_left hz]
    congr 2
    ring
  · simp [hz]

/-- Conditional `v`-integrand calculation.  If `c > 0`, the exponential
probability of `z ≥ -cE'`, subject to `z < 0`, is `exp (z/c)`.
@isnad1 id=eq.1h2v.s6.2a83c66c4069 from=translated src=- shape=eaa35e07 vocab=160555c1
-/
theorem measure_neg_mul_le
    {z c : ℝ} (hc : 0 < c) :
    expMeasure 1 {e : ℝ | z < 0 ∧ -c * e ≤ z} =
      ENNReal.ofReal (if z < 0 then exp (z / c) else 0) := by
  by_cases hz : z < 0
  · have hset : {e : ℝ | z < 0 ∧ -c * e ≤ z} = Ici (-z / c) := by
      ext e
      simp only [mem_ofPred_eq, hz, true_and, mem_Ici]
      constructor <;> intro h
      · apply (div_le_iff₀ hc).2
        linarith
      · have := (div_le_iff₀ hc).1 h
        linarith
    rw [hset, expMeasure_one_Ici (div_nonneg (neg_nonneg.mpr hz.le) hc.le),
      ite_eq_left hz]
    congr 2
    ring
  · simp [hz]

section ProductFormulas

variable (μ : Measure ℝ)

/-- Product-measure/Tonelli form of the lower-tail transfer probability.  On
the canonical product space, the first coordinate is `Z` with law `μ` and
the second coordinate is an independent rate-one exponential variable.
@isnad1 id=eq.1h2v.s7.4caa9406c3be from=translated src=- shape=de804444 vocab=6e9c7981
-/
theorem prod_measure_u (d : ℝ) (hd : 0 < d) :
    μ.prod (expMeasure 1)
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < d * p.2} =
      ∫⁻ z, ENNReal.ofReal (if 0 ≤ z then exp (-z / d) else 0) ∂μ := by
  have hs : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < d * p.2} := by
    exact (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst (measurable_const.mul measurable_snd))
  rw [Measure.prod_apply hs]
  apply lintegral_congr
  intro z
  exact measure_lt_mul_exp hd

/-- Product-measure/Tonelli form of the upper-tail transfer probability.
This is the mass between the threshold `-cE'` and zero.
@isnad1 id=eq.1h2v.s7.5c062bec3fd6 from=translated src=- shape=c61d70e8 vocab=6e9c7981
-/
theorem prod_measure_v (c : ℝ) (hc : 0 < c) :
    μ.prod (expMeasure 1)
        {p : ℝ × ℝ | p.1 < 0 ∧ -c * p.2 ≤ p.1} =
      ∫⁻ z, ENNReal.ofReal (if z < 0 then exp (z / c) else 0) ∂μ := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 < 0 ∧ -c * p.2 ≤ p.1} := by
    exact (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_le (measurable_const.mul measurable_snd) measurable_fst)
  rw [Measure.prod_apply hs]
  apply lintegral_congr
  intro z
  exact measure_neg_mul_le hc

end ProductFormulas

section Positivity

/-- Conditional width of the random interval `[-cE', dE']` at a fixed
value `z`; this is the integrand for `w = u + v`. -/
noncomputable def bandIntegrand (c d z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (if 0 ≤ z then exp (-z / d) else exp (z / c))

/--
@isnad1 id=measurab.0h2v.s3.b53ff08937e4 from=translated src=- shape=30e1f344 vocab=8c121a11
-/
theorem measurable_bandIntegrand (c d : ℝ) :
    Measurable (bandIntegrand c d) := by
  unfold bandIntegrand
  exact ENNReal.measurable_ofReal.comp
    (Measurable.ite measurableSet_Ici (by fun_prop) (by fun_prop))

/--
@isnad1 id=lt.0h3v.s4.9bb6878ed07b from=translated src=- shape=1995cd38 vocab=a72cea8c
-/
theorem bandIntegrand_pos (c d z : ℝ) :
    0 < bandIntegrand c d z := by
  unfold bandIntegrand
  split_ifs <;> exact ENNReal.ofReal_pos.mpr (exp_pos _)

/-- The interval width `w` is strictly positive under every probability
law for `Z`.
@isnad1 id=lt.0h3v.s5.f3b78ad6df15 from=translated src=- shape=e9b2e5b4 vocab=64f13017
-/
theorem lintegral_bandIntegrand_pos
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (c d : ℝ) :
    0 < ∫⁻ z, bandIntegrand c d z ∂μ := by
  rw [lintegral_pos_iff_support (measurable_bandIntegrand c d)]
  have hs : Function.support (bandIntegrand c d) = Set.univ := by
    ext z
    simp only [Function.mem_support, mem_univ, iff_true]
    exact ne_of_gt (bandIntegrand_pos c d z)
  rw [hs, measure_univ]
  exact zero_lt_one

end Positivity

end ExponentialTransfer

end Feige
