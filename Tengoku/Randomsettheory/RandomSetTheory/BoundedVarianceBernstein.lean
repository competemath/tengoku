/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.BernsteinConcentration
import Tengoku.Seed.Probability.Moments.Variance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bernstein certificates from a bound and a second moment

This file supplies the variance-sensitive bounded-variable estimate needed
for truncation arguments.  Hoeffding's lemma only remembers the deterministic
bound; after truncating an empirical process at height `a * sqrt n`, that
would give a variance proxy growing with `n`.  The lemmas below retain the
second moment and put the deterministic bound only in Bernstein's linear
term.

The numerical factor `2` in the variance proxy is deliberately conservative.
It follows from Mathlib's second-order remainder estimate for the exponential
and is sufficient for empirical-process chaining.
-/

open Real Set Finset MeasureTheory
open scoped ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Multiplication by a deterministic scalar multiplies the variance proxy by
its square and the Bernstein scale proxy by its absolute value.-/
theorem HasBernsteinMGF.const_mul {X : Ω → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ) (a : ℝ) :
    HasBernsteinMGF (fun ω ↦ a * X ω)
      ⟨a ^ 2 * (v : ℝ), mul_nonneg (sq_nonneg a) v.coe_nonneg⟩
      ⟨|a| * (b : ℝ), mul_nonneg (abs_nonneg a) b.coe_nonneg⟩ μ := by
  refine
    { aemeasurable := hX.aemeasurable.const_mul a
      integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t ht
    change |a| * (b : ℝ) * |t| < 1 at ht
    have hdomain : (b : ℝ) * |a * t| < 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg t, b.coe_nonneg]
    simpa only [mul_assoc, mul_left_comm] using
      hX.integrable_exp_mul (a * t) hdomain
  · intro t ht
    change |a| * (b : ℝ) * |t| < 1 at ht
    have hdomain : (b : ℝ) * |a * t| < 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg t, b.coe_nonneg]
    change mgf (fun ω ↦ a * X ω) μ t ≤
      Real.exp ((a ^ 2 * (v : ℝ)) * t ^ 2 /
        (2 * (1 - (|a| * (b : ℝ)) * |t|)))
    rw [mgf_const_mul]
    convert hX.mgf_le (a * t) hdomain using 1
    · simp only [abs_mul]
      ring

/-- Nonnegative-scalar version of `HasBernsteinMGF.const_mul`, expressed
with the native multiplication on `ℝ≥0`.  This form composes cleanly with
finite sums of variance proxies.-/
theorem HasBernsteinMGF.nnreal_mul {X : Ω → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ) (a : ℝ≥0) :
    HasBernsteinMGF (fun ω ↦ (a : ℝ) * X ω) (a ^ 2 * v) (a * b) μ := by
  refine
    { aemeasurable := hX.aemeasurable.const_mul (a : ℝ)
      integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t ht
    have hdomain : (b : ℝ) * |(a : ℝ) * t| < 1 := by
      rw [abs_mul, abs_of_nonneg a.coe_nonneg]
      push_cast at ht ⊢
      nlinarith [a.coe_nonneg, abs_nonneg t, b.coe_nonneg]
    simpa only [mul_assoc, mul_left_comm] using
      hX.integrable_exp_mul ((a : ℝ) * t) hdomain
  · intro t ht
    have hdomain : (b : ℝ) * |(a : ℝ) * t| < 1 := by
      rw [abs_mul, abs_of_nonneg a.coe_nonneg]
      push_cast at ht ⊢
      nlinarith [a.coe_nonneg, abs_nonneg t, b.coe_nonneg]
    rw [mgf_const_mul]
    convert hX.mgf_le ((a : ℝ) * t) hdomain using 1
    push_cast
    rw [abs_mul, abs_of_nonneg a.coe_nonneg]
    ring

/-- A convenient second-order upper bound for the real exponential on the
unit interval.-/
theorem exp_le_one_add_add_three_quarters_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + (3 / 4 : ℝ) * x ^ 2 := by
  have h := (abs_le.mp (Real.exp_bound hx (n := 2) (by norm_num))).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  nlinarith

/-- A centered `L²` variable bounded by `b` has a Bernstein MGF certificate
whose variance proxy is twice any upper bound for its second moment.

The denominator in `HasBernsteinMGF` absorbs the restriction `b * |t| < 1`.
No higher moment assumption is used.-/
theorem hasBernsteinMGF_of_memLp_two_of_ae_abs_le_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hcenter : ∫ ω, X ω ∂μ = 0)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ ≤ v) :
    HasBernsteinMGF X
      ⟨2 * v, mul_nonneg (by norm_num) hv⟩ ⟨b, hb⟩ μ := by
  have hXint : Integrable X μ := hX.integrable (by norm_num)
  have hXsq : Integrable (fun ω ↦ X ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).1 hX
  refine
    { aemeasurable := hX.aemeasurable
      integrable_exp_mul := ?_
      mgf_le := ?_ }
  · intro t ht
    apply Integrable.of_bound
      ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
      (Real.exp (|t| * b))
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t * X ω ≤ |t * X ω| := le_abs_self _
      _ = |t| * |X ω| := abs_mul _ _
      _ ≤ |t| * b := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  · intro t ht
    have hdomain : 0 < 1 - b * |t| := sub_pos.mpr ht
    have hpoint : ∀ᵐ ω ∂μ,
        Real.exp (t * X ω) ≤
          1 + t * X ω + (3 / 4 : ℝ) * (t * X ω) ^ 2 := by
      filter_upwards [hbound] with ω hω
      apply exp_le_one_add_add_three_quarters_sq
      calc
        |t * X ω| = |t| * |X ω| := abs_mul _ _
        _ ≤ |t| * b := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
        _ = b * |t| := mul_comm _ _
        _ ≤ 1 := ht.le
    have hexp : Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
      apply Integrable.of_bound
        ((hX.aemeasurable.const_mul t).exp.aestronglyMeasurable)
        (Real.exp (|t| * b))
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        t * X ω ≤ |t * X ω| := le_abs_self _
        _ = |t| * |X ω| := abs_mul _ _
        _ ≤ |t| * b := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
    have hlin : Integrable (fun ω ↦ t * X ω) μ := hXint.const_mul t
    have hsqscaled : Integrable (fun ω ↦ (t * X ω) ^ 2) μ := by
      convert hXsq.const_mul (t ^ 2) using 1
      ext ω
      ring
    have hsqterm : Integrable
        (fun ω ↦ (3 / 4 : ℝ) * (t * X ω) ^ 2) μ :=
      hsqscaled.const_mul (3 / 4 : ℝ)
    have hfirst : Integrable (fun ω ↦ 1 + t * X ω) μ :=
      (integrable_const (1 : ℝ)).add hlin
    have hquad : Integrable
        (fun ω ↦ 1 + t * X ω + (3 / 4 : ℝ) * (t * X ω) ^ 2) μ :=
      hfirst.add hsqterm
    have hsqIntegral :
        (∫ ω, (3 / 4 : ℝ) * (t * X ω) ^ 2 ∂μ) =
          (3 / 4 : ℝ) * t ^ 2 * (∫ ω, X ω ^ 2 ∂μ) := by
      calc
        (∫ ω, (3 / 4 : ℝ) * (t * X ω) ^ 2 ∂μ) =
            (3 / 4 : ℝ) * ∫ ω, (t * X ω) ^ 2 ∂μ :=
          integral_const_mul _ _
        _ = (3 / 4 : ℝ) * (t ^ 2 * ∫ ω, X ω ^ 2 ∂μ) := by
          congr 1
          convert integral_const_mul (t ^ 2) (fun ω ↦ X ω ^ 2) using 1
          ring
        _ = (3 / 4 : ℝ) * t ^ 2 * (∫ ω, X ω ^ 2 ∂μ) := by ring
    have hmgf : mgf X μ t ≤ 1 + (3 / 4 : ℝ) * t ^ 2 * v := by
      calc
        mgf X μ t ≤ ∫ ω,
            (1 + t * X ω + (3 / 4 : ℝ) * (t * X ω) ^ 2) ∂μ :=
          integral_mono_ae hexp hquad hpoint
        _ = 1 + (3 / 4 : ℝ) * t ^ 2 *
            (∫ ω, X ω ^ 2 ∂μ) := by
          rw [integral_add hfirst hsqterm,
            integral_add (integrable_const (1 : ℝ)) hlin,
            integral_const_mul, hcenter, hsqIntegral]
          simp
        _ ≤ 1 + (3 / 4 : ℝ) * t ^ 2 * v := by gcongr
    calc
      mgf X μ t ≤ 1 + (3 / 4 : ℝ) * t ^ 2 * v := hmgf
      _ ≤ Real.exp ((3 / 4 : ℝ) * t ^ 2 * v) := by
        simpa [add_comm] using
          Real.add_one_le_exp ((3 / 4 : ℝ) * t ^ 2 * v)
      _ ≤ Real.exp
          (((⟨2 * v, mul_nonneg (by norm_num) hv⟩ : ℝ≥0) : ℝ) * t ^ 2 /
            (2 * (1 - ((⟨b, hb⟩ : ℝ≥0) : ℝ) * |t|))) := by
        apply Real.exp_le_exp.mpr
        change (3 / 4 : ℝ) * t ^ 2 * v ≤
          (2 * v) * t ^ 2 / (2 * (1 - b * |t|))
        rw [le_div_iff₀ (mul_pos (by norm_num) hdomain)]
        have hz : 0 ≤ b * |t| := mul_nonneg hb (abs_nonneg t)
        have hA : 0 ≤ (3 / 4 : ℝ) * t ^ 2 * v := by positivity
        calc
          (3 / 4 : ℝ) * t ^ 2 * v * (2 * (1 - b * |t|)) ≤
              (3 / 4 : ℝ) * t ^ 2 * v * 2 := by
            gcongr
            linarith
          _ ≤ 2 * v * t ^ 2 := by nlinarith [sq_nonneg t]

/-- Centered form of the bounded-variance Bernstein estimate.  If `X` is
bounded by `b`, centering costs only a factor `2` in the scale proxy, while
the variance proxy remains controlled by the uncentered second moment.-/
theorem hasBernsteinMGF_centered_of_memLp_two_of_ae_abs_le
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ ≤ v) :
    HasBernsteinMGF (fun ω ↦ X ω - ∫ z, X z ∂μ)
      ⟨2 * v, mul_nonneg (by norm_num) hv⟩
      ⟨2 * b, mul_nonneg (by norm_num) hb⟩ μ := by
  let m : ℝ := ∫ z, X z ∂μ
  let Xc : Ω → ℝ := fun ω ↦ X ω - m
  have hXint : Integrable X μ := hX.integrable (by norm_num)
  have hXc : MemLp Xc 2 μ := by
    exact hX.sub (memLp_const m)
  have hm : |m| ≤ b := by
    have h := norm_integral_le_of_norm_le_const
      (μ := μ) (f := X) (C := b) (by
        filter_upwards [hbound] with ω hω
        simpa only [Real.norm_eq_abs] using hω)
    simpa only [m, Real.norm_eq_abs, probReal_univ, mul_one] using h
  have hXcbound : ∀ᵐ ω ∂μ, |Xc ω| ≤ 2 * b := by
    filter_upwards [hbound] with ω hω
    calc
      |Xc ω| = |X ω - m| := rfl
      _ ≤ |X ω| + |m| := abs_sub _ _
      _ ≤ b + b := add_le_add hω hm
      _ = 2 * b := by ring
  have hXccenter : ∫ ω, Xc ω ∂μ = 0 := by
    change (∫ ω, X ω - m ∂μ) = 0
    rw [integral_sub hXint (integrable_const m)]
    simp [m]
  have hXcsecond : ∫ ω, Xc ω ^ 2 ∂μ ≤ v := by
    change (∫ ω, (X ω - ∫ z, X z ∂μ) ^ 2 ∂μ) ≤ v
    rw [← variance_eq_integral hX.aemeasurable]
    exact (variance_le_expectation_sq hX.aestronglyMeasurable).trans hsecond
  exact hasBernsteinMGF_of_memLp_two_of_ae_abs_le_of_integral_eq_zero
    Xc hXc hv (mul_nonneg (by norm_num) hb) hXcbound hXccenter hXcsecond

end ProbabilityTheory
