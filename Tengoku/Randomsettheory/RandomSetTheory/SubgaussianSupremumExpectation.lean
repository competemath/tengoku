/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals
import Tengoku.Seed.MeasureTheory.Integral.Layercake
import Tengoku.Randomsettheory.RandomSetTheory.BoundedSupportChaining
import Tengoku.Randomsettheory.RandomSetTheory.CVaRDenseSupremum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Expected suprema from sub-Gaussian chaining tails

The geometric chaining theorem in `BoundedSupportChaining` already proves a
uniform tail on a Euclidean unit ball.  This file integrates that tail, using
the layer-cake formula, instead of duplicating the chaining construction.

For a continuous process with sub-Gaussian increment scale `sigma`, the final
bound is

`84 * sigma * sqrt (finrank R E + 1)`.

Measurability and integrability of the full supremum are obtained from an
explicit integrable pathwise envelope.  This assumption is deliberately
visible: scalar increment tails alone do not justify integrating an
uncountable supremum.
-/

open Filter Real Set MeasureTheory TopologicalSpace Module
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Integrating a shifted exponential tail.  The positive-part reduction is
what avoids paying an artificial exponential factor in the shift `A`.
@isnad1 id=le.3h5v.s7.a55be2f803dc from=translated src=- shape=a806c25c vocab=5f8bdbde
-/
theorem integral_le_add_of_shifted_exponential_tail
    [IsProbabilityMeasure mu]
    (S : Omega → ℝ) (hS : Integrable S mu)
    {A b : ℝ} (hb : 0 < b)
    (htail : ∀ x : ℝ, 0 ≤ x →
      mu.real {omega | A + b * x < S omega} ≤ Real.exp (-x)) :
    (∫ omega, S omega ∂mu) ≤ A + b := by
  let R : Omega → ℝ := fun omega ↦ max (S omega - A) 0
  have hR : Integrable R mu := by
    exact (hS.sub (integrable_const A)).sup (integrable_const 0)
  have hRnonneg : ∀ᵐ omega ∂mu, 0 ≤ R omega :=
    ae_of_all mu fun omega ↦ le_max_right _ _
  have hpoint : ∀ omega, S omega ≤ A + R omega := by
    intro omega
    dsimp only [R]
    have hmax := le_max_left (S omega - A) 0
    linarith
  have hSle : (∫ omega, S omega ∂mu) ≤
      ∫ omega, A + R omega ∂mu := by
    exact integral_mono hS ((integrable_const A).add hR) hpoint
  have htailR : ∀ t : ℝ, 0 < t →
      mu.real {omega | t < R omega} ≤ Real.exp (-b⁻¹ * t) := by
    intro t ht
    have hx : 0 ≤ t / b := (div_pos ht hb).le
    have hbase := htail (t / b) hx
    have hevent : {omega | t < R omega} =
        {omega | A + b * (t / b) < S omega} := by
      ext omega
      simp only [R, lt_max_iff, not_lt_of_ge ht.le, or_false,
        lt_sub_iff_add_lt]
      rw [mul_div_cancel₀ t hb.ne']
      simp only [Set.mem_ofPred_eq, add_comm]
    rw [hevent]
    calc
      mu.real {omega | A + b * (t / b) < S omega} ≤
          Real.exp (-(t / b)) := hbase
      _ = Real.exp (-b⁻¹ * t) := by
        congr 1
        rw [div_eq_mul_inv]
        ring
  have hExpInt : IntegrableOn (fun t : ℝ ↦ Real.exp (-b⁻¹ * t))
      (Set.Ioi 0) := by
    exact exp_neg_integrableOn_Ioi 0 (inv_pos.mpr hb)
  have htailIntegral :
      (∫ t in Set.Ioi (0 : ℝ), mu.real {omega | t < R omega}) ≤ b := by
    have hmono :
        (∫ t in Set.Ioi (0 : ℝ), mu.real {omega | t < R omega}) ≤
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-b⁻¹ * t) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun _ ↦ measureReal_nonneg
      · exact hExpInt
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact htailR t ht
    have hExpIntegral :
        (∫ t in Set.Ioi (0 : ℝ), Real.exp (-b⁻¹ * t)) = b := by
      have hcoef : -b⁻¹ < 0 := neg_lt_zero.mpr (inv_pos.mpr hb)
      rw [integral_exp_mul_Ioi hcoef 0]
      simp only [mul_zero, Real.exp_zero, neg_div, one_div]
      field_simp
    exact hmono.trans_eq hExpIntegral
  have hRIntegral : (∫ omega, R omega ∂mu) ≤ b := by
    rw [hR.integral_eq_integral_meas_lt hRnonneg]
    exact htailIntegral
  calc
    (∫ omega, S omega ∂mu) ≤
        ∫ omega, A + R omega ∂mu := hSle
    _ = A + ∫ omega, R omega ∂mu := by
      rw [integral_add (integrable_const A) hR, integral_const,
        probReal_univ, one_smul]
    _ ≤ A + b := add_le_add le_rfl hRIntegral

end ProbabilityTheory

namespace RandomSetTheory

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {mu : Measure Omega}

/-- Expected absolute supremum of a continuous sub-Gaussian process on a
finite-dimensional Euclidean unit ball.  The proof integrates the existing
chaining tail; it does not repeat the construction of nets or edge graphs.
@isnad1 id=le.7h6v.s8.eed58f7c224c from=translated src=- shape=8febf81a vocab=34776d49
-/
theorem integral_iSup_abs_unitBall_subgaussianProcess_le
    [IsProbabilityMeasure mu]
    (Z : Omega → EuclideanUnitBall E → ℝ) (B : Omega → ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hcontinuous : ∀ omega, Continuous (Z omega))
    (hmeas : ∀ t, Measurable (fun omega ↦ Z omega t))
    (hB : Integrable B mu)
    (hdom : ∀ omega t, |Z omega t| ≤ |B omega|)
    (hzero : ∀ omega, Z omega ⟨0, by simp⟩ = 0)
    (hsubgaussian : ∀ (s t : EuclideanUnitBall E) (y : ℝ), 0 ≤ y →
      mu.real {omega |
        sigma * dist s t * Real.sqrt (2 * y) <
          |Z omega s - Z omega t|} ≤
        2 * Real.exp (-y)) :
    (∫ omega, (⨆ t : EuclideanUnitBall E, |Z omega t|) ∂mu) ≤
      84 * sigma * Real.sqrt (finrank ℝ E + 1 : ℝ) := by
  let S : Omega → ℝ := fun omega ↦
    ⨆ t : EuclideanUnitBall E, |Z omega t|
  have hSmeas : Measurable S := by
    apply measurable_iSup_continuous_of_measurable_dense
      (fun omega t ↦ |Z omega t|)
    · intro omega
      exact (hcontinuous omega).abs
    · intro k
      exact (hmeas _).abs
  have hSbdd : ∀ omega,
      BddAbove (Set.range fun t : EuclideanUnitBall E ↦ |Z omega t|) := by
    intro omega
    exact ⟨|B omega|, by
      rintro _ ⟨t, rfl⟩
      exact hdom omega t⟩
  have hSnonneg : ∀ omega, 0 ≤ S omega := by
    intro omega
    let zero : EuclideanUnitBall E := ⟨0, by simp⟩
    exact (abs_nonneg (Z omega zero)).trans (le_ciSup (hSbdd omega) zero)
  have hSdom : ∀ omega, S omega ≤ |B omega| := by
    intro omega
    exact ciSup_le fun t ↦ hdom omega t
  have hSint : Integrable S mu := by
    apply hB.abs.mono' hSmeas.aestronglyMeasurable
    exact ae_of_all mu fun omega ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hSnonneg omega)]
      exact hSdom omega
  let droot : ℝ := Real.sqrt (finrank ℝ E + 1 : ℝ)
  let A : ℝ := 72 * sigma * droot + 6 * sigma
  let b : ℝ := 6 * sigma
  have hdrootOne : 1 ≤ droot := by
    dsimp only [droot]
    have hdnonneg : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt (finrank ℝ E + 1 : ℝ) :=
        Real.sqrt_le_sqrt (by linarith)
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have htail : ∀ x : ℝ, 0 ≤ x →
      mu.real {omega | A + b * x < S omega} ≤ Real.exp (-x) := by
    intro x hx
    have hsqrt : Real.sqrt (2 * x) ≤ x + 1 := by
      have hsqrtSq : (Real.sqrt (2 * x)) ^ 2 = 2 * x := by
        rw [Real.sq_sqrt]
        positivity
      have hsqrtNonneg := Real.sqrt_nonneg (2 * x)
      nlinarith [sq_nonneg x]
    have hthreshold :
        6 * sigma * Real.sqrt (2 * x) + 72 * sigma * droot ≤
          A + b * x := by
      have hsix : 0 ≤ 6 * sigma := mul_nonneg (by norm_num) hsigma.le
      have hmul := mul_le_mul_of_nonneg_left hsqrt hsix
      dsimp only [A, b]
      linarith
    have hchain :=
      measureReal_unitBall_subgaussianProcess_largeDeviation_le
        Z hsigma.le hx hcontinuous hzero hsubgaussian
    apply (measureReal_mono ?_).trans hchain
    intro omega homega
    have hlarge :
        6 * sigma * Real.sqrt (2 * x) + 72 * sigma * droot < S omega :=
      hthreshold.trans_lt homega
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup hlarge
    exact ⟨t, by simpa only [droot] using ht⟩
  have hbase := ProbabilityTheory.integral_le_add_of_shifted_exponential_tail
    S hSint hb htail
  change (∫ omega, S omega ∂mu) ≤ _
  calc
    (∫ omega, S omega ∂mu) ≤ A + b := hbase
    _ ≤ 84 * sigma * droot := by
      dsimp only [A, b]
      nlinarith [mul_le_mul_of_nonneg_left hdrootOne hsigma.le]

/-- Rescaled form of
`integral_iSup_abs_unitBall_subgaussianProcess_le`.  It displays the scale
`K2 * sqrt(d+1) / sqrt(n)` when the *original process* is already known to
have sub-Gaussian increments at scale `K2 / sqrt n`.

This theorem deliberately does not claim that an `L²` envelope implies its
`hsubgaussian` hypothesis.  For heavy-tailed empirical processes that step
must instead pass through ghost-sample symmetrization and a conditionally
Rademacher process.
@isnad1 id=le.8h7v.s8.248c0039f527 from=translated src=- shape=d556c70b vocab=da2aa005
-/
theorem integral_iSup_abs_unitBall_subgaussianEmpiricalProcess_le
    [IsProbabilityMeasure mu]
    (Z : Omega → EuclideanUnitBall E → ℝ) (B : Omega → ℝ)
    (n : ℕ) (hn : 0 < n) {K2 : ℝ} (hK2 : 0 < K2)
    (hcontinuous : ∀ omega, Continuous (Z omega))
    (hmeas : ∀ t, Measurable (fun omega ↦ Z omega t))
    (hB : Integrable B mu)
    (hdom : ∀ omega t, |Z omega t| ≤ |B omega|)
    (hzero : ∀ omega, Z omega ⟨0, by simp⟩ = 0)
    (hsubgaussian : ∀ (s t : EuclideanUnitBall E) (y : ℝ), 0 ≤ y →
      mu.real {omega |
        (K2 / Real.sqrt n) * dist s t * Real.sqrt (2 * y) <
          |Z omega s - Z omega t|} ≤
        2 * Real.exp (-y)) :
    (∫ omega, (⨆ t : EuclideanUnitBall E, |Z omega t|) ∂mu) ≤
      84 * (K2 / Real.sqrt n) *
        Real.sqrt (finrank ℝ E + 1 : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
  exact integral_iSup_abs_unitBall_subgaussianProcess_le
    Z B (div_pos hK2 hsqrt) hcontinuous hmeas hB hdom hzero hsubgaussian

end RandomSetTheory
