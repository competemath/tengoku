/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.IidBernsteinConcentration
import Tengoku.Randomsettheory.RandomSetTheory.FiniteNetConcentration
import Tengoku.Seed.Analysis.Convex.SpecificFunctions.Basic
import Tengoku.Seed.Probability.Moments.MGFAnalytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From a psi-one bound to Bernstein concentration

This file supplies the missing bridge between the standard exponential
integrability certificate

`E[exp (|X| / K)] ≤ 2`

and `HasBernsteinMGF`.  No separate Orlicz-space API is introduced: the
certificate records exactly the inequality used in probability theory to
express `‖X‖_{ψ₁} ≤ K`.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Real Set Metric Finset MeasureTheory ProbabilityTheory Module
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The concrete exponential-integrability certificate usually written
`‖X‖_{ψ₁} ≤ K`: the scale is positive and
`E[exp (|X| / K)] ≤ 2`.

The definition deliberately records the integral and its integrability
instead of defining an Orlicz norm, for which Mathlib currently has no API.-/
structure HasPsiOneNormBound (X : Ω → ℝ) (K : ℝ≥0)
    (μ : Measure Ω := by volume_tac) : Prop where
  aemeasurable : AEMeasurable X μ
  scale_pos : 0 < (K : ℝ)
  integrable_exp_abs_div :
    Integrable (fun ω => exp (|X ω| / (K : ℝ))) μ
  integral_exp_abs_div_le_two :
    (∫ ω, exp (|X ω| / (K : ℝ)) ∂μ) ≤ 2

namespace HasPsiOneNormBound

/-- A `psi₁` certificate depends only on the law of the random variable.
This transports the report's one-observation envelope assumption to every
member of an identically distributed sample.
@isnad1 id=haspsion.2h7v.s5.dfe8d9c002a1 from=translated src=- shape=223227eb vocab=aec017e4
-/
theorem identDistrib
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    {X : Ω → ℝ} {Y : Ω' → ℝ} {K : ℝ≥0}
    (hX : HasPsiOneNormBound X K μ)
    (hXY : IdentDistrib X Y μ ν) :
    HasPsiOneNormBound Y K ν := by
  let transform : ℝ → ℝ := fun x => exp (|x| / (K : ℝ))
  have htransform : Measurable transform := by
    dsimp only [transform]
    fun_prop
  have hdist : IdentDistrib (transform ∘ X) (transform ∘ Y) μ ν :=
    hXY.comp htransform
  refine
    { aemeasurable := hXY.aemeasurable_snd
      scale_pos := hX.scale_pos
      integrable_exp_abs_div := ?_
      integral_exp_abs_div_le_two := ?_ }
  · change Integrable (transform ∘ Y) ν
    apply hdist.integrable_snd
    change Integrable (transform ∘ X) μ
    exact hX.integrable_exp_abs_div
  · calc
      (∫ ω, exp (|Y ω| / (K : ℝ)) ∂ν) =
          ∫ ω, exp (|X ω| / (K : ℝ)) ∂μ := by
            simpa only [transform, Function.comp_apply] using
              hdist.integral_eq.symm
      _ ≤ 2 := hX.integral_exp_abs_div_le_two

private lemma exp_scaled_sub_one_sub_id_le
    {r z : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hz : 0 ≤ z) :
    exp (r * z) - 1 - r * z ≤ r ^ 2 * exp z := by
  have hsum_rz : Summable (fun n : ℕ => (r * z) ^ n / n.factorial) :=
    Real.summable_pow_div_factorial (r * z)
  have hsum_z : Summable (fun n : ℕ => z ^ n / n.factorial) :=
    Real.summable_pow_div_factorial z
  have htail_rz :
      Summable (fun n : ℕ => (r * z) ^ (n + 2) / (n + 2).factorial) :=
    (summable_nat_add_iff 2).2 hsum_rz
  have htail_z :
      Summable (fun n : ℕ => z ^ (n + 2) / (n + 2).factorial) :=
    (summable_nat_add_iff 2).2 hsum_z
  have hterm (n : ℕ) :
      (r * z) ^ (n + 2) / (n + 2).factorial ≤
        r ^ 2 * (z ^ (n + 2) / (n + 2).factorial) := by
    rw [mul_pow]
    have hrpow : r ^ (n + 2) ≤ r ^ 2 :=
      pow_le_pow_of_le_one hr0 hr1 (by omega)
    have hquot : 0 ≤ z ^ (n + 2) / (n + 2).factorial := by positivity
    calc
      r ^ (n + 2) * z ^ (n + 2) / (n + 2).factorial =
          r ^ (n + 2) * (z ^ (n + 2) / (n + 2).factorial) := by ring
      _ ≤ r ^ 2 * (z ^ (n + 2) / (n + 2).factorial) :=
        mul_le_mul_of_nonneg_right hrpow hquot
  have htail_le :
      (∑' n : ℕ, (r * z) ^ (n + 2) / (n + 2).factorial) ≤
        ∑' n : ℕ, r ^ 2 * (z ^ (n + 2) / (n + 2).factorial) := by
    exact Summable.tsum_le_tsum hterm htail_rz
      (htail_z.mul_left (r ^ 2))
  have hexp_rz :
      exp (r * z) - 1 - r * z =
        ∑' n : ℕ, (r * z) ^ (n + 2) / (n + 2).factorial := by
    rw [show exp (r * z) =
        ∑' n : ℕ, (r * z) ^ n / n.factorial by
      simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]]
    have hsplit := hsum_rz.sum_add_tsum_nat_add 2
    simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
      Nat.factorial_one] at hsplit
    linarith
  rw [hexp_rz]
  calc
    _ ≤ ∑' n : ℕ,
        r ^ 2 * (z ^ (n + 2) / (n + 2).factorial) := htail_le
    _ = r ^ 2 * (∑' n : ℕ,
        z ^ (n + 2) / (n + 2).factorial) := tsum_mul_left
    _ ≤ r ^ 2 * exp z := by
      gcongr
      have hsplit := hsum_z.sum_add_tsum_nat_add 2
      simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
        Nat.factorial_one] at hsplit
      rw [show exp z = ∑' n : ℕ, z ^ n / n.factorial by
        simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]]
      linarith [hsplit]

private lemma abs_exp_sub_one_sub_id_le_exp_abs_sub_one_sub_abs (y : ℝ) :
    |exp y - 1 - y| ≤ exp |y| - 1 - |y| := by
  have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (y : ℂ) 2
  norm_num [Finset.sum_range_succ] at h ⊢
  have hleft : |exp y - 1 - y| =
      ‖Complex.exp (y : ℂ) - (1 + (y : ℂ))‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    push_cast
    ring
  rw [hleft]
  linarith

private lemma exp_mul_le_one_add_add_sq_mul_exp_abs_div
    {K t x : ℝ} (hK : 0 < K) (ht : K * |t| ≤ 1) :
    exp (t * x) ≤
      1 + t * x + (K * |t|) ^ 2 * exp (|x| / K) := by
  let r := K * |t|
  let z := |x| / K
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have habs : |t * x| = r * z := by
    dsimp [r, z]
    rw [abs_mul]
    field_simp
  have hrem := abs_exp_sub_one_sub_id_le_exp_abs_sub_one_sub_abs (t * x)
  have hscaled := exp_scaled_sub_one_sub_id_le hr0 ht hz
  rw [habs] at hrem
  have hle : exp (t * x) - 1 - t * x ≤ r ^ 2 * exp z := by
    calc
      _ ≤ |exp (t * x) - 1 - t * x| := le_abs_self _
      _ ≤ exp (r * z) - 1 - r * z := hrem
      _ ≤ r ^ 2 * exp z := hscaled
  dsimp [r, z] at hle ⊢
  linarith

/-- A psi-one certificate implies integrability of every exponential tilt
strictly inside its natural domain.
@isnad1 id=integrab.2h5v.s6.5bad5312358f from=translated src=- shape=08399019 vocab=6e90b41d
-/
theorem integrable_exp_mul
    {X : Ω → ℝ} {K : ℝ≥0} (hX : HasPsiOneNormBound X K μ)
    {t : ℝ} (ht : (K : ℝ) * |t| < 1) :
    Integrable (fun ω => exp (t * X ω)) μ := by
  apply hX.integrable_exp_abs_div.mono'
  · exact (hX.aemeasurable.const_mul t).exp.aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      t * X ω ≤ |t * X ω| := le_abs_self _
      _ = |t| * |X ω| := abs_mul _ _
      _ ≤ (1 / (K : ℝ)) * |X ω| := by
        gcongr
        rw [le_div_iff₀ hX.scale_pos]
        simpa [mul_comm] using ht.le
      _ = |X ω| / (K : ℝ) := by ring

/-- A psi-one certificate in particular gives genuine integrability of the
random variable, so the centering hypothesis below is not vacuous.
@isnad1 id=integrab.1h4v.s5.3bd35f5120f4 from=translated src=- shape=63c0410f vocab=2f398932
-/
theorem integrable
    {X : Ω → ℝ} {K : ℝ≥0} (hX : HasPsiOneNormBound X K μ) :
    Integrable X μ := by
  apply (hX.integrable_exp_abs_div.const_mul (K : ℝ)).mono'
  · exact hX.aemeasurable.aestronglyMeasurable
  · filter_upwards with ω
    simp only [Real.norm_eq_abs]
    have hz : 0 ≤ |X ω| / (K : ℝ) := by positivity
    have hzexp : |X ω| / (K : ℝ) ≤ exp (|X ω| / (K : ℝ)) := by
      have := Real.pow_div_factorial_le_exp (|X ω| / (K : ℝ)) hz 1
      simpa using this
    calc
      |X ω| = (K : ℝ) * (|X ω| / (K : ℝ)) := by
        field_simp [hX.scale_pos.ne']
      _ ≤ (K : ℝ) * exp (|X ω| / (K : ℝ)) := by
        gcongr

/-- A concrete `psi₁` certificate controls the first absolute moment by
its scale.  With the normalization `E exp (|X| / K) ≤ 2`, the constant is
exactly `1`.
@isnad1 id=le.1h4v.s5.1dc061c0cc11 from=translated src=- shape=4a0d480e vocab=4d4a9afb
-/
theorem integral_abs_le_scale
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0} (hX : HasPsiOneNormBound X K μ) :
    (∫ ω, |X ω| ∂μ) ≤ (K : ℝ) := by
  let G : Ω → ℝ := fun ω => exp (|X ω| / (K : ℝ))
  have hGint : Integrable G μ := by
    simpa only [G] using hX.integrable_exp_abs_div
  have habsInt : Integrable (fun ω => |X ω|) μ := hX.integrable.abs
  have hpoint : ∀ ω, |X ω| ≤ (K : ℝ) * (G ω - 1) := by
    intro ω
    have hz : 0 ≤ |X ω| / (K : ℝ) := by positivity
    have hexp := Real.add_one_le_exp (|X ω| / (K : ℝ))
    calc
      |X ω| = (K : ℝ) * (|X ω| / (K : ℝ)) := by
        field_simp [hX.scale_pos.ne']
      _ ≤ (K : ℝ) * (G ω - 1) := by
        dsimp only [G]
        gcongr
        linarith
  have hrightInt : Integrable (fun ω => (K : ℝ) * (G ω - 1)) μ :=
    (hGint.sub (integrable_const 1)).const_mul _
  have hmono : (∫ ω, |X ω| ∂μ) ≤
      ∫ ω, (K : ℝ) * (G ω - 1) ∂μ :=
    integral_mono habsInt hrightInt hpoint
  calc
    (∫ ω, |X ω| ∂μ) ≤
        ∫ ω, (K : ℝ) * (G ω - 1) ∂μ := hmono
    _ = (K : ℝ) * ((∫ ω, G ω ∂μ) - 1) := by
      rw [integral_const_mul, integral_sub hGint (integrable_const 1),
        integral_const]
      simp
    _ ≤ (K : ℝ) := by
      have hGle : (∫ ω, G ω ∂μ) ≤ 2 := by
        simpa only [G] using hX.integral_exp_abs_div_le_two
      nlinarith

/-- The (signed) expectation is bounded above by the `psi₁` scale.
@isnad1 id=le.1h4v.s5.6047120bfe5c from=translated src=- shape=6893e249 vocab=debd9f02
-/
theorem integral_le_scale
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0} (hX : HasPsiOneNormBound X K μ) :
    (∫ ω, X ω ∂μ) ≤ (K : ℝ) := by
  calc
    (∫ ω, X ω ∂μ) ≤ ∫ ω, |X ω| ∂μ :=
      integral_mono_ae hX.integrable hX.integrable.abs
        (Filter.Eventually.of_forall fun ω => le_abs_self (X ω))
    _ ≤ (K : ℝ) := hX.integral_abs_le_scale

/-- A `psi₁` certificate passes to every a.e. dominated random variable.

If `|Y| ≤ c |X|` and `X` has scale `K`, then `Y` has scale `c K`.
The positivity assumption on `c` is necessary because the concrete
certificate records a strictly positive denominator.
@isnad1 id=haspsion.4h6v.s6.7aadbd9d1d97 from=translated src=- shape=2fc0d820 vocab=922d48e3
-/
theorem mono_abs
    {X Y : Ω → ℝ} {K c : ℝ≥0}
    (hX : HasPsiOneNormBound X K μ) (hc : 0 < (c : ℝ))
    (hY : AEMeasurable Y μ)
    (hdom : ∀ᵐ ω ∂μ, |Y ω| ≤ (c : ℝ) * |X ω|) :
    HasPsiOneNormBound Y (c * K) μ := by
  have hscale : 0 < ((c * K : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_mul] using mul_pos hc hX.scale_pos
  have hpoint : ∀ᵐ ω ∂μ,
      exp (|Y ω| / ((c * K : ℝ≥0) : ℝ)) ≤
        exp (|X ω| / (K : ℝ)) := by
    filter_upwards [hdom] with ω hω
    apply Real.exp_le_exp.mpr
    rw [NNReal.coe_mul]
    calc
      |Y ω| / ((c : ℝ) * (K : ℝ)) ≤
          ((c : ℝ) * |X ω|) / ((c : ℝ) * (K : ℝ)) :=
        div_le_div_of_nonneg_right hω (mul_pos hc hX.scale_pos).le
      _ = |X ω| / (K : ℝ) := by
        field_simp [hc.ne', hX.scale_pos.ne']
  have hint : Integrable
      (fun ω => exp (|Y ω| / ((c * K : ℝ≥0) : ℝ))) μ := by
    apply hX.integrable_exp_abs_div.mono'
    · exact (hY.abs.div_const _).exp.aestronglyMeasurable
    · filter_upwards [hpoint] with ω hω
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hω
  refine
    { aemeasurable := hY
      scale_pos := hscale
      integrable_exp_abs_div := hint
      integral_exp_abs_div_le_two := ?_ }
  exact (integral_mono_ae hint hX.integrable_exp_abs_div hpoint).trans
    hX.integral_exp_abs_div_le_two

/-- Centering preserves a concrete `psi₁` certificate, with the explicit
universal loss `3` in the scale.

The proof uses only the defining inequality `E exp (|X| / K) ≤ 2`.
First `E|X| ≤ K`; convexity gives
`E exp (|X| / (3K)) ≤ 4/3`, while
`exp (|EX| / (3K)) ≤ exp (1/3) ≤ 3/2`.
The product is at most `2`.
@isnad1 id=haspsion.1h4v.s6.6aa103d5c33d from=translated src=- shape=f26d66c9 vocab=d4882f3e
-/
theorem center
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0} (hX : HasPsiOneNormBound X K μ) :
    HasPsiOneNormBound
      (fun ω => X ω - ∫ x, X x ∂μ) (3 * K) μ := by
  let EX : ℝ := ∫ x, X x ∂μ
  let G : Ω → ℝ := fun ω => exp (|X ω| / (K : ℝ))
  let Gthird : Ω → ℝ := fun ω => exp (|X ω| / (3 * (K : ℝ)))
  have hK0 : 0 ≤ (K : ℝ) := K.2
  have hGint : Integrable G μ := by
    simpa only [G] using hX.integrable_exp_abs_div
  have habsInt : Integrable (fun ω => |X ω|) μ := hX.integrable.abs
  have hmomentPoint : ∀ ω,
      |X ω| ≤ (K : ℝ) * (G ω - 1) := by
    intro ω
    have hz : 0 ≤ |X ω| / (K : ℝ) := by positivity
    have hexp := Real.add_one_le_exp (|X ω| / (K : ℝ))
    calc
      |X ω| = (K : ℝ) * (|X ω| / (K : ℝ)) := by
        field_simp [hX.scale_pos.ne']
      _ ≤ (K : ℝ) * (G ω - 1) := by
        dsimp only [G]
        gcongr
        linarith
  have hrightInt : Integrable (fun ω => (K : ℝ) * (G ω - 1)) μ :=
    (hGint.sub (integrable_const 1)).const_mul _
  have habsIntegral_le : (∫ ω, |X ω| ∂μ) ≤ (K : ℝ) := by
    have hmono : (∫ ω, |X ω| ∂μ) ≤
        ∫ ω, (K : ℝ) * (G ω - 1) ∂μ :=
      integral_mono habsInt hrightInt hmomentPoint
    calc
      (∫ ω, |X ω| ∂μ) ≤
          ∫ ω, (K : ℝ) * (G ω - 1) ∂μ := hmono
      _ = (K : ℝ) * ((∫ ω, G ω ∂μ) - 1) := by
        rw [integral_const_mul, integral_sub hGint (integrable_const 1),
          integral_const]
        simp
      _ ≤ (K : ℝ) := by
        have hGle : (∫ ω, G ω ∂μ) ≤ 2 := by
          simpa only [G] using hX.integral_exp_abs_div_le_two
        nlinarith
  have hEXabs : |EX| ≤ (K : ℝ) := by
    calc
      |EX| = |∫ x, X x ∂μ| := rfl
      _ ≤ ∫ x, |X x| ∂μ := abs_integral_le_integral_abs
      _ ≤ (K : ℝ) := habsIntegral_le
  have hthirdPoint (ω : Ω) :
      Gthird ω ≤ (2 / 3 : ℝ) + (1 / 3 : ℝ) * G ω := by
    have hconv := convexOn_exp.2
      (show (0 : ℝ) ∈ Set.univ by simp)
      (show |X ω| / (K : ℝ) ∈ Set.univ by simp)
      (show 0 ≤ (2 / 3 : ℝ) by norm_num)
      (show 0 ≤ (1 / 3 : ℝ) by norm_num)
      (show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num)
    calc
      Gthird ω = exp ((2 / 3 : ℝ) * 0 +
          (1 / 3 : ℝ) * (|X ω| / (K : ℝ))) := by
        dsimp only [Gthird]
        congr 1
        field_simp [hX.scale_pos.ne']
        ring
      _ ≤ (2 / 3 : ℝ) * exp 0 +
          (1 / 3 : ℝ) * exp (|X ω| / (K : ℝ)) := by
        simpa only [smul_eq_mul] using hconv
      _ = (2 / 3 : ℝ) + (1 / 3 : ℝ) * G ω := by
        simp only [Real.exp_zero, mul_one, G]
  have hGthirdInt : Integrable Gthird μ := by
    apply ((integrable_const (2 / 3 : ℝ)).add
      (hGint.const_mul (1 / 3 : ℝ))).mono'
    · exact ((hX.aemeasurable.abs.div_const _).exp).aestronglyMeasurable
    · filter_upwards with ω
      change |Gthird ω| ≤ (2 / 3 : ℝ) + (1 / 3 : ℝ) * G ω
      rw [abs_of_pos (by positivity)]
      exact hthirdPoint ω
  have hGthirdIntegral_le : (∫ ω, Gthird ω ∂μ) ≤ 4 / 3 := by
    calc
      (∫ ω, Gthird ω ∂μ) ≤
          ∫ ω, ((2 / 3 : ℝ) + (1 / 3 : ℝ) * G ω) ∂μ :=
        integral_mono hGthirdInt
          ((integrable_const (2 / 3 : ℝ)).add
            (hGint.const_mul (1 / 3 : ℝ))) hthirdPoint
      _ = (2 / 3 : ℝ) + (1 / 3 : ℝ) * (∫ ω, G ω ∂μ) := by
        rw [integral_add (integrable_const (2 / 3 : ℝ))
          (hGint.const_mul (1 / 3 : ℝ)), integral_const,
          integral_const_mul]
        simp
      _ ≤ 4 / 3 := by
        have hGle : (∫ ω, G ω ∂μ) ≤ 2 := by
          simpa only [G] using hX.integral_exp_abs_div_le_two
        linarith
  have hExpEX : exp (|EX| / (3 * (K : ℝ))) ≤ 3 / 2 := by
    calc
      exp (|EX| / (3 * (K : ℝ))) ≤ exp (1 / 3 : ℝ) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_iff₀ (mul_pos (by norm_num) hX.scale_pos)]
        nlinarith
      _ ≤ 1 / (1 - (1 / 3 : ℝ)) :=
        Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 3 / 2 := by norm_num
  have hcenterPoint (ω : Ω) :
      exp (|X ω - EX| / (3 * (K : ℝ))) ≤
        exp (|EX| / (3 * (K : ℝ))) * Gthird ω := by
    calc
      exp (|X ω - EX| / (3 * (K : ℝ))) ≤
          exp ((|X ω| + |EX|) / (3 * (K : ℝ))) := by
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right (abs_sub _ _)
          (mul_nonneg (by norm_num) hX.scale_pos.le)
      _ = exp (|EX| / (3 * (K : ℝ))) * Gthird ω := by
        rw [add_div, Real.exp_add, mul_comm]
  have hcenterInt : Integrable
      (fun ω => exp (|X ω - EX| / (3 * (K : ℝ)))) μ := by
    apply (hGthirdInt.const_mul (exp (|EX| / (3 * (K : ℝ))))).mono'
    · exact (((hX.aemeasurable.sub aemeasurable_const).abs.div_const _).exp)
        |>.aestronglyMeasurable
    · filter_upwards with ω
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (Real.exp_pos _).le, norm_eq_abs] using hcenterPoint ω
  refine
    { aemeasurable := hX.aemeasurable.sub aemeasurable_const
      scale_pos := by
        simpa only [NNReal.coe_mul] using mul_pos (by norm_num) hX.scale_pos
      integrable_exp_abs_div := by
        convert hcenterInt using 1 <;> norm_num [NNReal.coe_mul, EX]
      integral_exp_abs_div_le_two := ?_ }
  change (∫ ω, exp (|X ω - EX| / (3 * (K : ℝ))) ∂μ) ≤ 2
  calc
    (∫ ω, exp (|X ω - EX| / (3 * (K : ℝ))) ∂μ) ≤
        ∫ ω, exp (|EX| / (3 * (K : ℝ))) * Gthird ω ∂μ :=
      integral_mono hcenterInt
        (hGthirdInt.const_mul (exp (|EX| / (3 * (K : ℝ))))) hcenterPoint
    _ = exp (|EX| / (3 * (K : ℝ))) * (∫ ω, Gthird ω ∂μ) := by
      rw [integral_const_mul]
    _ ≤ (3 / 2 : ℝ) * (4 / 3 : ℝ) :=
      mul_le_mul hExpEX hGthirdIntegral_le (by positivity) (by positivity)
    _ = 2 := by norm_num

/-! ## A finite maximum under a psi-one certificate -/

/-- The direct one-sided tail bound associated with the convention
`E[exp (|X| / K)] ≤ 2`.

The constant is exactly `2`: exponential Markov at `1 / K` gives
`P(X > t) ≤ 2 exp (-t / K)`.  No sign assumption on `X` is needed, since
`X ≤ |X|`.
@isnad1 id=le.1h5v.s6.47ff35572ba8 from=translated src=- shape=53eaa524 vocab=95180bb9
-/
theorem measureReal_gt_le_two_mul_exp
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0} (hX : HasPsiOneNormBound X K μ)
    (t : ℝ) :
    μ.real {ω | t < X ω} ≤ 2 * exp (-t / (K : ℝ)) := by
  have hq : 0 ≤ (1 / (K : ℝ)) := by positivity
  have hsubset : {ω | t < X ω} ⊆ {ω | t ≤ |X ω|} := by
    intro ω hω
    exact hω.le.trans (le_abs_self (X ω))
  calc
    μ.real {ω | t < X ω} ≤ μ.real {ω | t ≤ |X ω|} :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ (∫ ω, exp ((1 / (K : ℝ)) * |X ω|) ∂μ) /
        exp ((1 / (K : ℝ)) * t) :=
      exponential_markov_real (fun ω ↦ |X ω|) (1 / (K : ℝ)) t hq
        (by simpa [div_eq_mul_inv, mul_comm] using hX.integrable_exp_abs_div)
    _ ≤ 2 / exp ((1 / (K : ℝ)) * t) := by
      have hint : (∫ ω, exp ((1 / (K : ℝ)) * |X ω|) ∂μ) ≤ 2 := by
        simpa [div_eq_mul_inv, mul_comm] using
          hX.integral_exp_abs_div_le_two
      exact div_le_div_of_nonneg_right hint
        (le_of_lt (exp_pos _))
    _ = 2 * exp (-t / (K : ℝ)) := by
      rw [div_eq_mul_inv, ← exp_neg]
      congr 1
      simp only [div_eq_mul_inv, one_mul]
      ring_nf

/-- Union bound for the upper tail of a finite family carrying a common
psi-one certificate.  Independence is not required.

For a family indexed by `s`, this is the literal bound
`P(∃ i ∈ s, Xᵢ > t) ≤ 2 |s| exp (-t / K)`.
@isnad1 id=le.1h7v.s7.9576d91b2db8 from=translated src=- shape=ad5320c6 vocab=e7829983
-/
theorem measureReal_exists_gt_le_card_mul_two_mul_exp
    {I : Type*} [IsFiniteMeasure μ]
    (s : Finset I) (X : I → Ω → ℝ) (K : ℝ≥0)
    (hX : ∀ i ∈ s, HasPsiOneNormBound (X i) K μ) (t : ℝ) :
    μ.real {ω | ∃ i ∈ s, t < X i ω} ≤
      s.card * (2 * exp (-t / (K : ℝ))) := by
  have hset : {ω | ∃ i ∈ s, t < X i ω} =
      ⋃ i ∈ s, {ω | t < X i ω} := by
    ext ω
    simp
  rw [hset]
  exact measureReal_biUnion_finset_le_card_mul s _ fun i hi ↦
    (hX i hi).measureReal_gt_le_two_mul_exp t

/-- High-probability bound for a finite maximum under the concrete
psi-one convention of this file.

If `s` is nonempty and `δ > 0`, then with probability at least `1 - δ`,
all variables are at most

`K * log (2 * |s| / δ)`.

Thus the multiplicative constant in front of `K log (2 |s| / δ)` is
exactly `1` for `HasPsiOneNormBound`.  No independence hypothesis is used.
The conclusion is stated with `Measure.real`; null-measurability follows
from the `AEMeasurable` field of each certificate.
@isnad1 id=le.3h7v.s7.0ed55ad86182 from=translated src=- shape=63f6b085 vocab=766120fa
-/
theorem one_sub_le_measureReal_forall_le_mul_log
    {I : Type*} [IsProbabilityMeasure μ]
    (s : Finset I) (hs : s.Nonempty) (X : I → Ω → ℝ) (K : ℝ≥0)
    (hX : ∀ i ∈ s, HasPsiOneNormBound (X i) K μ)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ μ.real {ω | ∀ i ∈ s,
      X i ω ≤ (K : ℝ) * log (2 * s.card / δ)} := by
  let t : ℝ := (K : ℝ) * log (2 * s.card / δ)
  let B : Set Ω := {ω | ∃ i ∈ s, t < X i ω}
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast s.card_pos.mpr hs
  have hratio : 0 < 2 * (s.card : ℝ) / δ := by positivity
  have hbad : μ.real B ≤ δ := by
    have htail := measureReal_exists_gt_le_card_mul_two_mul_exp
      s X K hX t
    calc
      μ.real B ≤ s.card * (2 * exp (-t / (K : ℝ))) := by
        simpa [B] using htail
      _ = δ := by
        have hK : 0 < (K : ℝ) := (hX hs.choose hs.choose_spec).scale_pos
        rw [show -t / (K : ℝ) = -log (2 * s.card / δ) by
          dsimp [t]
          field_simp]
        rw [exp_neg, exp_log hratio]
        field_simp
  have hBnull : NullMeasurableSet B μ := by
    have hunion : B = ⋃ i ∈ s, {ω | t < X i ω} := by
      ext ω
      simp [B]
    rw [hunion]
    apply s.nullMeasurableSet_biUnion
    intro i hi
    exact (hX i hi).aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
  have hsum := measureReal_add_measureReal_compl₀ hBnull
  have hcompl : Bᶜ = {ω | ∀ i ∈ s, X i ω ≤ t} := by
    ext ω
    simp [B, not_lt]
  rw [probReal_univ, hcompl] at hsum
  dsimp [t] at hsum ⊢
  linarith

/-- A centered psi-one variable has a Bernstein MGF certificate with
variance proxy `4 K²` and scale proxy `K`.

The constants follow directly from
`E exp (|X| / K) ≤ 2`: for `K |t| < 1`,
`mgf X t ≤ exp (2 K² t²)`, which is stronger than the requested
Bernstein denominator.
@isnad1 id=hasberns.2h4v.s6.dd54631f934f from=translated src=- shape=71dea458 vocab=a62593fd
-/
theorem hasBernsteinMGF_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0} (hX : HasPsiOneNormBound X K μ)
    (hcenter : μ[X] = 0) :
    HasBernsteinMGF X (4 * K ^ 2) K μ where
  aemeasurable := hX.aemeasurable
  integrable_exp_mul t ht := hX.integrable_exp_mul ht
  mgf_le t ht := by
    let r : ℝ := (K : ℝ) * |t|
    let G : Ω → ℝ := fun ω => exp (|X ω| / (K : ℝ))
    have hr0 : 0 ≤ r := by
      dsimp [r]
      positivity
    have hr1 : r ≤ 1 := ht.le
    have hexp_int : Integrable (fun ω => exp (t * X ω)) μ :=
      hX.integrable_exp_mul ht
    have hG_int : Integrable G μ := by
      simpa [G] using hX.integrable_exp_abs_div
    have hright_int : Integrable
        (fun ω => 1 + t * X ω + r ^ 2 * G ω) μ :=
      (integrable_const (1 : ℝ)).add
        (hX.integrable.const_mul t) |>.add
          (hG_int.const_mul (r ^ 2))
    have hint_le :
        (∫ ω, exp (t * X ω) ∂μ) ≤
          ∫ ω, (1 + t * X ω + r ^ 2 * G ω) ∂μ := by
      apply integral_mono_ae hexp_int hright_int
      filter_upwards with ω
      exact exp_mul_le_one_add_add_sq_mul_exp_abs_div
        hX.scale_pos hr1
    have hG_le : (∫ ω, G ω ∂μ) ≤ 2 := by
      simpa [G] using hX.integral_exp_abs_div_le_two
    have hmgf_quad : mgf X μ t ≤ 1 + 2 * r ^ 2 := by
      calc
        mgf X μ t = ∫ ω, exp (t * X ω) ∂μ := rfl
        _ ≤ ∫ ω, (1 + t * X ω + r ^ 2 * G ω) ∂μ := hint_le
        _ = 1 + r ^ 2 * (∫ ω, G ω ∂μ) := by
          calc
            (∫ ω, (1 + t * X ω + r ^ 2 * G ω) ∂μ) =
                (∫ ω, (1 + t * X ω) ∂μ) +
                  ∫ ω, r ^ 2 * G ω ∂μ :=
              integral_add
                ((integrable_const (1 : ℝ)).add (hX.integrable.const_mul t))
                (hG_int.const_mul (r ^ 2))
            _ = ((∫ _ω : Ω, (1 : ℝ) ∂μ) +
                  ∫ ω, t * X ω ∂μ) +
                    ∫ ω, r ^ 2 * G ω ∂μ := by
              rw [integral_add (integrable_const (1 : ℝ))
                (hX.integrable.const_mul t)]
            _ = 1 + r ^ 2 * (∫ ω, G ω ∂μ) := by
              rw [integral_const, integral_const_mul, integral_const_mul, hcenter]
              simp
        _ ≤ 1 + 2 * r ^ 2 := by nlinarith [sq_nonneg r]
    calc
      mgf X μ t ≤ 1 + 2 * r ^ 2 := hmgf_quad
      _ ≤ exp (2 * r ^ 2) := by
        simpa [add_comm] using Real.add_one_le_exp (2 * r ^ 2)
      _ ≤ exp (((4 * K ^ 2 : ℝ≥0) : ℝ) * t ^ 2 /
          (2 * (1 - (K : ℝ) * |t|))) := by
        apply Real.exp_le_exp.mpr
        have hden : 0 < 1 - r := sub_pos.mpr ht
        have hfrac : 2 * r ^ 2 ≤ 2 * r ^ 2 / (1 - r) := by
          rw [le_div_iff₀ hden]
          nlinarith [sq_nonneg r]
        calc
          2 * r ^ 2 ≤ 2 * r ^ 2 / (1 - r) := hfrac
          _ = ((4 * K ^ 2 : ℝ≥0) : ℝ) * t ^ 2 /
              (2 * (1 - (K : ℝ) * |t|)) := by
            dsimp [r] at hden ⊢
            rw [mul_pow, sq_abs]
            field_simp [hden.ne'] <;> ring_nf

/-- A high-probability upper bound for an average of independent variables
with a common `psi₁` certificate.

With the convention `E exp (|Xᵢ| / K) ≤ 2`, every expectation is at most
`K`.  Centering costs the factor `3`; Bernstein at deviation `2K` then gives
the explicit failure probability `2 exp (-|s| / 21)`.  Consequently the
sample average is at most `3K` as soon as
`21 log (2 / δ) ≤ |s|`.
@isnad1 id=le.5h7v.s7.610c8e7cc2a4 from=translated src=- shape=28c1742f vocab=cd6ec543
-/
theorem measureReal_average_gt_three_mul_scale_le
    [IsProbabilityMeasure μ]
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) (K : ℝ≥0)
    (hX : ∀ i ∈ s, HasPsiOneNormBound (X i) K μ)
    (hindep : iIndepFun X μ)
    {δ : ℝ} (hδ : 0 < δ)
    (hsize : 21 * log (2 / δ) ≤ (s.card : ℝ)) :
    μ.real {ω | 3 * (K : ℝ) <
      (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤ δ := by
  let Xc : ι → Ω → ℝ := fun i ω => X i ω - ∫ ω, X i ω ∂μ
  let B : ℝ≥0 := 3 * K
  let V : ℝ≥0 := 4 * B ^ 2
  let N : ℝ := s.card
  let t : ℝ := 2 * (K : ℝ)
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast s.card_pos.mpr hs
  have hK : 0 < (K : ℝ) := (hX hs.choose hs.choose_spec).scale_pos
  have hB : 0 < (B : ℝ) := by
    dsimp only [B]
    push_cast
    positivity
  have hV : 0 < (V : ℝ) := by
    dsimp only [V]
    push_cast
    positivity
  have hcenter : ∀ i ∈ s, μ[Xc i] = 0 := by
    intro i hi
    dsimp only [Xc]
    rw [integral_sub (hX i hi).integrable (integrable_const _),
      integral_const]
    simp
  have hpsiCenter : ∀ i ∈ s, HasPsiOneNormBound (Xc i) B μ := by
    intro i hi
    simpa only [Xc, B] using (hX i hi).center
  have hBernstein : ∀ i ∈ s, HasBernsteinMGF (Xc i) V B μ := by
    intro i hi
    simpa only [V] using
      (hpsiCenter i hi).hasBernsteinMGF_of_integral_eq_zero (hcenter i hi)
  have hindepCenter : iIndepFun Xc μ := by
    have hcomp := hindep.comp
      (fun i (x : ℝ) => x - ∫ ω, X i ω ∂μ)
      (fun _i => measurable_id.sub measurable_const)
    simpa only [Xc, Function.comp_def] using hcomp
  have hsumV :
      (((∑ _i ∈ s, V : ℝ≥0) : ℝ≥0) : ℝ) = N * (V : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, N]
    push_cast
    rfl
  have hsumVpos : 0 <
      (((∑ _i ∈ s, V : ℝ≥0) : ℝ≥0) : ℝ) := by
    rw [hsumV]
    exact mul_pos hN hV
  have htail := bernstein_finset_average_abs_real
    Xc (fun _i => V) B hindepCenter s hs hBernstein
    (show 0 ≤ t by dsimp only [t]; positivity) hsumVpos
  have hexponent :
      -((N * t) ^ 2) /
          (2 * ((((∑ _i ∈ s, V : ℝ≥0) : ℝ≥0) : ℝ) +
            (B : ℝ) * (N * t))) = -N / 21 := by
    rw [hsumV]
    dsimp only [N, t, V, B]
    push_cast
    field_simp [hK.ne', (show (s.card : ℝ) ≠ 0 by positivity)]
    <;> ring
  have htail' :
      μ.real {ω | t ≤ |(∑ i ∈ s, Xc i ω) /
        (s.card : ℝ)|} ≤
        2 * exp (-N / 21) := by
    simpa only [N, hexponent] using htail
  have hmean :
      (∑ i ∈ s, ∫ ω, X i ω ∂μ) / N ≤ (K : ℝ) := by
    rw [div_le_iff₀ hN]
    calc
      (∑ i ∈ s, ∫ ω, X i ω ∂μ) ≤
          ∑ _i ∈ s, (K : ℝ) := by
        exact Finset.sum_le_sum fun i hi => (hX i hi).integral_le_scale
      _ = (K : ℝ) * N := by
        simp [Finset.sum_const, nsmul_eq_mul, N, mul_comm]
  have hsubset :
      {ω | 3 * (K : ℝ) <
        (∑ i ∈ s, X i ω) / (s.card : ℝ)} ⊆
      {ω | t ≤ |(∑ i ∈ s, Xc i ω) /
        (s.card : ℝ)|} := by
    intro ω hω
    change 3 * (K : ℝ) <
      (∑ i ∈ s, X i ω) / (s.card : ℝ) at hω
    have hcenterAvg :
        (∑ i ∈ s, Xc i ω) / (s.card : ℝ) =
          (∑ i ∈ s, X i ω) / (s.card : ℝ) -
            (∑ i ∈ s, ∫ ω, X i ω ∂μ) / (s.card : ℝ) := by
      dsimp only [Xc]
      rw [Finset.sum_sub_distrib]
      ring
    have hdev : t <
        (∑ i ∈ s, Xc i ω) / (s.card : ℝ) := by
      dsimp only [t]
      dsimp only [N] at hmean
      rw [hcenterAvg]
      linarith
    exact hdev.le.trans (le_abs_self _)
  have hbad :
      μ.real {ω | 3 * (K : ℝ) <
        (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
        2 * exp (-N / 21) :=
    (measureReal_mono hsubset (by finiteness)).trans htail'
  have hlog : log (2 / δ) ≤ N / 21 := by
    dsimp only [N]
    linarith
  have hexp : 2 * exp (-N / 21) ≤ δ := by
    calc
      2 * exp (-N / 21) ≤ 2 * exp (-log (2 / δ)) := by
        gcongr
        linarith
      _ = δ := by
        rw [exp_neg, exp_log (by positivity : 0 < 2 / δ)]
        field_simp
  exact hbad.trans hexp

end HasPsiOneNormBound

end ProbabilityTheory

namespace RandomSetTheory

/-- Dimension-explicit iid Bernstein concentration obtained directly from a
uniform psi-one certificate for the zeroth directional deviation.

The only extra assumption beyond exponential integrability is explicit
centering.  Integrability of every deviation follows from its psi-one
certificate, so this is a genuine expectation equality.
@isnad1 id=le.12h11v.s9.9d250c56786e from=translated src=- shape=98128b8e vocab=1f14d715
-/
theorem hausdorffDist_convexified_iid_risk_bound_dimensional_psiOne
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    {R : ℝ} (hFbound : ∀ z, ∀ y ∈ F z, ‖y‖ ≤ R)
    (K : ℝ≥0)
    (hpsi₀ : ∀ w : E, ‖w‖ ≤ 1 →
      ProbabilityTheory.HasPsiOneNormBound
        (directionalSupportDeviation
          (fun i ω => closedConvexHull ℝ (F (X i ω)))
          (iidAumannTarget μ (X 0) F) w 0) K μ)
    (hcenter₀ : ∀ w : E, ‖w‖ ≤ 1 →
      μ[directionalSupportDeviation
          (fun i ω => closedConvexHull ℝ (F (X i ω)))
          (iidAumannTarget μ (X 0) F) w 0] = 0)
    {n : ℕ} (hn : 0 < n) {eps x : ℝ}
    (heps : 0 < eps) (hx : 0 ≤ x) :
    μ.real {ω |
        (Real.sqrt (2 *
              (((∑ _i ∈ Finset.range n, (4 * K ^ 2 : ℝ≥0) : ℝ≥0) : ℝ)) * x) +
            2 * (K : ℝ) * x) / (n : ℝ) + (R + R) * eps <
          hausdorffDist
            (closedConvexHull ℝ
              (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
            (iidAumannTarget μ (X 0) F)} ≤
      (1 + 2 / eps) ^ finrank ℝ E * (2 * exp (-x)) := by
  have hK : 0 < (K : ℝ) := (hpsi₀ 0 (by simp)).scale_pos
  have hv : 0 < (((4 * K ^ 2 : ℝ≥0) : ℝ)) := by
    push_cast
    positivity
  have hB₀ : ∀ w : E, ‖w‖ ≤ 1 →
      ProbabilityTheory.HasBernsteinMGF
        (directionalSupportDeviation
          (fun i ω => closedConvexHull ℝ (F (X i ω)))
          (iidAumannTarget μ (X 0) F) w 0) (4 * K ^ 2) K μ := by
    intro w hw
    exact (hpsi₀ w hw).hasBernsteinMGF_of_integral_eq_zero
      (hcenter₀ w hw)
  exact
    hausdorffDist_convexified_iid_risk_bound_dimensional_bernstein
      X hX hindep hident F hF hFcompact hFne hFbound
      (4 * K ^ 2) K hv hB₀ hn heps hx

/-- Fully automatic-centering version of the iid psi-one Bernstein bound.

The population set is `iidAumannTarget`, so its support function is the
integral of the support function of the zeroth random set.  Consequently the
directional deviations are centered; users only need to provide the psi-one
certificate itself.
@isnad1 id=le.11h11v.s9.c2b431db676d from=translated src=- shape=3269252e vocab=bc2f363e
-/
theorem hausdorffDist_convexified_iid_risk_bound_dimensional_psiOne_auto
    {Ω Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z)) (hFne : ∀ z, (F z).Nonempty)
    {R : ℝ} (hFbound : ∀ z, ∀ y ∈ F z, ‖y‖ ≤ R)
    (K : ℝ≥0)
    (hpsi₀ : ∀ w : E, ‖w‖ ≤ 1 →
      ProbabilityTheory.HasPsiOneNormBound
        (directionalSupportDeviation
          (fun i ω => closedConvexHull ℝ (F (X i ω)))
          (iidAumannTarget μ (X 0) F) w 0) K μ)
    {n : ℕ} (hn : 0 < n) {eps x : ℝ}
    (heps : 0 < eps) (hx : 0 ≤ x) :
    μ.real {ω |
        (Real.sqrt (2 *
              (((∑ _i ∈ Finset.range n, (4 * K ^ 2 : ℝ≥0) : ℝ≥0) : ℝ)) * x) +
            2 * (K : ℝ) * x) / (n : ℝ) + (R + R) * eps <
          hausdorffDist
            (closedConvexHull ℝ
              (minkowskiAverage (Finset.range n) (fun i => F (X i ω))))
            (iidAumannTarget μ (X 0) F)} ≤
      (1 + 2 / eps) ^ finrank ℝ E * (2 * exp (-x)) := by
  let S₀ : Ω → Set E := fun ω => F (X 0 ω)
  let A : Set E := closure (aumannExpectation μ S₀)
  let L : Set E := closedConvexHull ℝ A
  have hS₀Effros : RandomSet.IsEffrosMeasurable S₀ :=
    hF.comp_measurable (hX 0)
  have hS₀compact : ∀ ω, IsCompact (S₀ ω) := fun ω =>
    hFcompact (X 0 ω)
  have hS₀ne : ∀ ω, (S₀ ω).Nonempty := fun ω =>
    hFne (X 0 ω)
  have hg : Integrable (fun _ : Ω => R) μ := integrable_const R
  have hS₀dom : ∀ ω, ∀ y ∈ S₀ ω, ‖y‖ ≤ R := fun ω =>
    hFbound (X 0 ω)
  have hAcompact : IsCompact A :=
    closure_aumannExpectation_compact_of_integrable_envelope hg
      (Filter.Eventually.of_forall hS₀dom)
  have hfOne : IsIntegrableSelection μ S₀
      (supportApproximateSelection
        hS₀Effros hS₀compact hS₀ne 0 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom 0 (by norm_num)
  have hAne : A.Nonempty :=
    (aumannExpectation_nonempty_of_selection hfOne).closure
  have hbaseInt : ∀ w : E,
      Integrable (fun ω => supportFunction (F (X 0 ω)) w) μ := fun w =>
    integrable_supportFunction_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom w
  have hLsupport : ∀ w : E,
      supportFunction L w =
        ∫ ω, supportFunction (F (X 0 ω)) w ∂μ := by
    intro w
    rw [supportFunction_closedConvexHull hAcompact hAne]
    exact supportFunction_closure_aumannExpectation_of_envelope
      hS₀Effros hS₀compact hS₀ne hg hS₀dom hAcompact w
  have hcenter₀ : ∀ w : E, ‖w‖ ≤ 1 →
      μ[directionalSupportDeviation
          (fun i ω => closedConvexHull ℝ (F (X i ω)))
          (iidAumannTarget μ (X 0) F) w 0] = 0 := by
    intro w _hw
    have hzero := integral_convexifiedDirectionalSupportDeviation_eq_zero
      X hident F hF hFcompact hFne L w (hbaseInt w) (hLsupport w) 0
    simpa [L, A, S₀, iidAumannTarget] using hzero
  exact hausdorffDist_convexified_iid_risk_bound_dimensional_psiOne
    X hX hindep hident F hF hFcompact hFne hFbound K hpsi₀ hcenter₀
      hn heps hx

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
