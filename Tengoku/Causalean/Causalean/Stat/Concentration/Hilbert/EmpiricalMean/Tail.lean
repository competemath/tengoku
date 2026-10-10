/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Stat.Concentration.Hilbert.EmpiricalMean.Basic
public import Tengoku.Causalean.Causalean.Mathlib.Probability.LimitTheorems.Approximation.CharFunBound
public import Tengoku.Causalean.Causalean.Stat.Concentration.TailBounds.McDiarmid

/-!
# Dimension-free Hilbert empirical-mean concentration

This module turns the Hilbert empirical-mean second-moment identity into an
expected-norm bound and a scalar McDiarmid tail bound.  A unit-norm feature map
therefore has centered empirical mean within the standard dimension-free
radius with high probability in every complete real Hilbert space.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace Causalean.Stat.Concentration.HilbertEmpiricalMean

variable {Ω X H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- Under [a probability law](hyp:μ), [a strongly measurable Hilbert-valued
random variable](hyp:g,hg) with [integrable squared norm](hyp:hg_sq) has
[expected norm at most the square root of its expected squared norm](goal). -/
theorem integral_norm_le_sqrt_integral_norm_sq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → H)
    (hg : StronglyMeasurable g)
    (hg_sq : Integrable (fun ω => ‖g ω‖ ^ 2) μ) :
    ∫ ω, ‖g ω‖ ∂μ ≤ Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
  have hg_L2 : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg_sq
  exact
    Causalean.Mathlib.Probability.ConvergingTogether.integral_abs_le_sqrt_integral_sq
      μ g hg_L2

/-- For [a probability law](hyp:P), [a strongly measurable Hilbert-valued
feature map](hyp:f,hf) with [unit-norm bound at every observation](hyp:hbound),
and [a nonempty sample size](hyp:hm), [the expected norm of the centered
empirical mean is at most one divided by the square root of the sample size](goal). -/
theorem centeredEmpiricalMean_norm_integral_le_inv_sqrt
    (P : Measure X) [IsProbabilityMeasure P] (f : X → H)
    (hf : StronglyMeasurable f) (hbound : ∀ x, ‖f x‖ ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    ∫ z : Fin m → X, ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖
        ∂(Measure.pi (fun _ : Fin m => P)) ≤
      1 / Real.sqrt m := by
  let Q : Measure (Fin m → X) := Measure.pi (fun _ : Fin m => P)
  have hf_L2 : MemLp f 2 P := memLp_two_of_norm_le_one P f hf hbound
  have hcoord_L2 (i : Fin m) :
      MemLp (fun z : Fin m → X => f (z i)) 2 Q := by
    change MemLp (f ∘ (Function.eval i : (Fin m → X) → X)) 2 Q
    exact hf_L2.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m => P) i)
  have hsum_L2 :
      MemLp (fun z : Fin m → X => ∑ r, f (z r)) 2 Q := by
    simpa only [Finset.sum_apply] using
      memLp_finsetSum Finset.univ (fun i _ => hcoord_L2 i)
  have hmean_L2 : MemLp (centeredEmpiricalMean P f m) 2 Q := by
    unfold centeredEmpiricalMean empiricalMean populationMean
    exact (hsum_L2.const_smul (m : ℝ)⁻¹).sub (memLp_const _)
  have hsum_sm :
      StronglyMeasurable (fun z : Fin m → X => ∑ r, f (z r)) := by
    rw [← Finset.sum_fn]
    apply Finset.stronglyMeasurable_sum
    intro i _
    exact hf.comp_measurable (measurable_pi_apply i)
  have hmean_sm : StronglyMeasurable (centeredEmpiricalMean P f m) := by
    unfold centeredEmpiricalMean empiricalMean populationMean
    exact (hsum_sm.const_smul (m : ℝ)⁻¹).sub stronglyMeasurable_const
  have hmean_sq :
      Integrable (fun z => ‖centeredEmpiricalMean P f m z‖ ^ 2) Q :=
    (memLp_two_iff_integrable_sq_norm hmean_sm.aestronglyMeasurable).1 hmean_L2
  have hraw_sq :
      Integrable (fun x => ‖f x‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf_L2
  have hraw : (∫ x, ‖f x‖ ^ 2 ∂P) ≤ 1 := by
    calc
      (∫ x, ‖f x‖ ^ 2 ∂P) ≤ ∫ _x : X, (1 : ℝ) ∂P := by
        apply integral_mono hraw_sq (integrable_const _)
        intro x
        nlinarith [norm_nonneg (f x), hbound x]
      _ = 1 := by simp
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hsecond :
      (∫ z, ‖centeredEmpiricalMean P f m z‖ ^ 2 ∂Q) ≤ (m : ℝ)⁻¹ := by
    calc
      (∫ z, ‖centeredEmpiricalMean P f m z‖ ^ 2 ∂Q)
          ≤ (m : ℝ)⁻¹ * ∫ x, ‖f x‖ ^ 2 ∂P := by
            simpa only [Q] using
              centeredEmpiricalMean_secondMoment_le P f hf hf_L2 hm_pos
      _ ≤ (m : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = (m : ℝ)⁻¹ := mul_one _
  calc
    (∫ z : Fin m → X, ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖
        ∂(Measure.pi (fun _ : Fin m => P)))
        ≤ Real.sqrt (∫ z, ‖centeredEmpiricalMean P f m z‖ ^ 2 ∂Q) := by
          simpa only [Q, centeredEmpiricalMean, empiricalMean, populationMean] using
            integral_norm_le_sqrt_integral_norm_sq Q
              (centeredEmpiricalMean P f m) hmean_sm hmean_sq
    _ ≤ Real.sqrt ((m : ℝ)⁻¹) := Real.sqrt_le_sqrt hsecond
    _ = 1 / Real.sqrt m := by rw [Real.sqrt_inv]; simp

end Causalean.Stat.Concentration.HilbertEmpiricalMean
