/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Tengoku.Seed.Analysis.Calculus.ContDiff.Operations
public import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Tengoku.Seed.Analysis.Real.Sqrt

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth periodic tilt functions and their actual integral moments

This file advances the finite moment calculations in `LoopMoments` to genuine
smooth functions on the real line, with period `2π` and actual interval
integrals. The cosine construction realizes all nonnegative variances. A
separate, explicit amplitude bound is required to preserve the stress
projection. Smoothness in parameters is stated using the amplitude, avoiding
an incorrect claim of smoothness of the square root at zero variance.

The positive exponential tilt used by the manuscript is also treated below.
Neither a smooth variance-inversion theorem nor a full true-cone result is
assumed or asserted.
-/

section

/-!
# Exact moment algebra for the true-cone loop construction

This file proves the finite-distribution form of the averaging and rephasing
identities in Lemma 6.1 of the candidate manuscript. The formulas are algebraic;
no existence, smoothness, or invertibility of a circle reparametrization is
asserted here. The hypotheses of `rephased_moments` are ordinary mass, mean,
and variance constraints, not an assumption that a desired loop exists.

The final lemmas give explicit two-point distributions with prescribed variance.
They establish finite moment feasibility, including a one-sided support bound.
-/

@[expose] public section

namespace NavierStokes.LoopMoments

open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- A finite weighted average. We retain the weights explicitly, so no
probabilistic or analytic existence assertion is hidden in the notation. -/
def avg (s : Finset ι) (w f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * f i

theorem avg_add (s : Finset ι) (w f g : ι → ℝ) :
    avg s w (fun i => f i + g i) = avg s w f + avg s w g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (s : Finset ι) (w f g : ι → ℝ) :
    avg s w (fun i => f i - g i) = avg s w f - avg s w g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_const_mul (s : Finset ι) (w f : ι → ℝ) (c : ℝ) :
    avg s w (fun i => c * f i) = c * avg s w f := by
  simp only [avg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem avg_const (s : Finset ι) (w : ι → ℝ) (c : ℝ)
    (hmass : ∑ i ∈ s, w i = 1) :
    avg s w (fun _ => c) = c := by
  simp only [avg, ← Finset.sum_mul, hmass, one_mul]

theorem avg_nonneg (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ avg s w f := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hf i hi))

/-- The standard variance expansion, with mass and first moment explicit. -/
theorem variance_identity (s : Finset ι) (w t : ι → ℝ) (m : ℝ)
    (hmass : ∑ i ∈ s, w i = 1) (hmean : avg s w t = m) :
    avg s w (fun i => (t i - m) ^ 2) = avg s w (fun i => t i ^ 2) - m ^ 2 := by
  calc
    avg s w (fun i => (t i - m) ^ 2) =
        avg s w (fun i => t i ^ 2 - (2 * m) * t i + m ^ 2) := by
          congr 1
          funext i
          ring
    _ = avg s w (fun i => t i ^ 2) - (2 * m) * avg s w t + m ^ 2 := by
          rw [avg_add, avg_sub, avg_const_mul, avg_const s w (m ^ 2) hmass]
    _ = avg s w (fun i => t i ^ 2) - m ^ 2 := by rw [hmean]; ring

/-- This is `a ⟨1+t²⟩ = a(1+m²) + ρ` from the manuscript. -/
theorem energy_moment (s : Finset ι) (w t : ι → ℝ) (a m ρ : ℝ)
    (ha : a ≠ 0) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = m)
    (hvar : avg s w (fun i => (t i - m) ^ 2) = ρ / a) :
    a * avg s w (fun i => 1 + t i ^ 2) = a * (1 + m ^ 2) + ρ := by
  have hsecond : avg s w (fun i => t i ^ 2) = m ^ 2 + ρ / a := by
    have := variance_identity s w t m hmass hmean
    linarith
  rw [avg_add, avg_const s w 1 hmass, hsecond]
  field_simp; ring

/-- A nonnegative weighted variance cannot decrease the nominal speed. -/
theorem variance_nonneg (s : Finset ι) (w t : ι → ℝ) (m : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ avg s w (fun i => (t i - m) ^ 2) := by
  exact avg_nonneg s w _ hw (fun i _ => sq_nonneg (t i - m))

theorem required_variance_nonneg (s : Finset ι) (w t : ι → ℝ) (a m ρ : ℝ)
    (ha : 0 < a) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hvar : avg s w (fun i => (t i - m) ^ 2) = ρ / a) :
    0 ≤ ρ := by
  have h := variance_nonneg s w t m hw
  rw [hvar] at h
  have hmul := mul_nonneg h (le_of_lt ha)
  simpa only [div_mul_cancel₀ _ (ne_of_gt ha)] using hmul

/-- The rephasing density relative to the old averaging parameter. -/
def phaseDensity (a v t : ℝ) : ℝ := a * (1 + t ^ 2) / v

/-- The positive first component of the loop shear. -/
def loopA (v t : ℝ) : ℝ := v / (1 + t ^ 2)

/-- The signed second component; this corresponds to `-b_L`. -/
def loopC (v t : ℝ) : ℝ := v * t / (1 + t ^ 2)

theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by
  nlinarith [sq_nonneg t]

theorem loopA_pos (v t : ℝ) (hv : 0 < v) : 0 < loopA v t := by
  exact div_pos hv (one_add_sq_pos t)

theorem phaseDensity_pos (a v t : ℝ) (ha : 0 < a) (hv : 0 < v) :
    0 < phaseDensity a v t := by
  exact div_pos (mul_pos ha (one_add_sq_pos t)) hv

theorem loop_speed (v t : ℝ) : loopA v t * (1 + t ^ 2) = v := by
  unfold loopA
  exact div_mul_cancel₀ v (ne_of_gt (one_add_sq_pos t))

theorem loop_slope (v t : ℝ) (hv : v ≠ 0) : loopC v t / loopA v t = t := by
  unfold loopC loopA
  field_simp

theorem density_times_loopA (a v t : ℝ) (hv : v ≠ 0) :
    phaseDensity a v t * loopA v t = a := by
  unfold phaseDensity loopA
  field_simp

theorem density_times_loopC (a v t : ℝ) (hv : v ≠ 0) :
    phaseDensity a v t * loopC v t = a * t := by
  unfold phaseDensity loopC
  field_simp

/-- Reweighting by the manuscript's density has total mass one. -/
theorem rephased_mass (s : Finset ι) (w t : ι → ℝ) (a m ρ v : ℝ)
    (ha : a ≠ 0) (hv : v ≠ 0) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = m)
    (hvar : avg s w (fun i => (t i - m) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + m ^ 2) + ρ) :
    ∑ i ∈ s, w i * phaseDensity a v (t i) = 1 := by
  have he := energy_moment s w t a m ρ ha hmass hmean hvar
  rw [← hspeed] at he
  calc
    (∑ i ∈ s, w i * phaseDensity a v (t i)) =
        (a * avg s w (fun i => 1 + t i ^ 2)) / v := by
          simp only [phaseDensity, avg, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 1 := by rw [he, div_self hv]

/-- The radial shear has the original mean after rephasing. -/
theorem rephased_meanA (s : Finset ι) (w t : ι → ℝ) (a v : ℝ)
    (hv : v ≠ 0) (hmass : ∑ i ∈ s, w i = 1) :
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) = a := by
  calc
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) =
        avg s w (fun _ => a) := by
          unfold avg
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_assoc, density_times_loopA a v (t i) hv]
    _ = a := avg_const s w a hmass

/-- The signed axial shear has the original mean after rephasing. -/
theorem rephased_meanC (s : Finset ι) (w t : ι → ℝ) (a v m : ℝ)
    (hv : v ≠ 0) (hmean : avg s w t = m) :
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) = a * m := by
  calc
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) =
        avg s w (fun i => a * t i) := by
          unfold avg
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_assoc, density_times_loopC a v (t i) hv]
    _ = a * m := by rw [avg_const_mul, hmean]

/-- With `m = -b/a`, the two rephased means are exactly `(a,-b)`. -/
theorem rephased_moments (s : Finset ι) (w t : ι → ℝ) (a b ρ v : ℝ)
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = -b / a)
    (hvar : avg s w (fun i => (t i - (-b / a)) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + (-b / a) ^ 2) + ρ) :
    (∑ i ∈ s, w i * phaseDensity a v (t i) = 1) ∧
      avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) = a ∧
      avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) = -b := by
  have hvpos : 0 < v := by
    rw [hspeed]
    exact add_pos_of_pos_of_nonneg (mul_pos ha (one_add_sq_pos (-b / a))) hρ
  have hv := ne_of_gt hvpos
  refine ⟨rephased_mass s w t a (-b / a) ρ v (ne_of_gt ha) hv hmass hmean hvar hspeed,
    rephased_meanA s w t a v hv hmass, ?_⟩
  rw [rephased_meanC s w t a v (-b / a) hv hmean]
  field_simp

/-- A two-point probability law. This is a concrete finite object, without
any hypothesis asserting the existence of the manuscript's smooth loop. -/
structure TwoPoint where
  /-- Left weight of `TwoPoint`, of type `ℝ`. -/
  leftWeight : ℝ
  /-- Right weight of `TwoPoint`, of type `ℝ`. -/
  rightWeight : ℝ
  /-- Left value of `TwoPoint`, of type `ℝ`. -/
  leftValue : ℝ
  /-- Right value of `TwoPoint`, of type `ℝ`. -/
  rightValue : ℝ

/-- Mean, given by `q.leftWeight * q.leftValue + q.rightWeight * q.rightValue`. -/
def TwoPoint.mean (q : TwoPoint) : ℝ :=
  q.leftWeight * q.leftValue + q.rightWeight * q.rightValue

/-- Centered second, given by `q.leftWeight * (q.leftValue - m) ^ 2 + q.rightWeight *
(q.rightValue - m) ^ 2`. -/
def TwoPoint.centeredSecond (q : TwoPoint) (m : ℝ) : ℝ :=
  q.leftWeight * (q.leftValue - m) ^ 2 + q.rightWeight * (q.rightValue - m) ^ 2

/-- Is probability, given by `0 ≤ q.leftWeight ∧ 0 ≤ q.rightWeight ∧ q.leftWeight +
q.rightWeight = 1`. -/
def TwoPoint.IsProbability (q : TwoPoint) : Prop :=
  0 ≤ q.leftWeight ∧ 0 ≤ q.rightWeight ∧ q.leftWeight + q.rightWeight = 1

/-- For any nonnegative variance, equal masses at `m ± √V` realize it. -/
def symmetricPair (m V : ℝ) : TwoPoint :=
  ⟨1 / 2, 1 / 2, m - Real.sqrt V, m + Real.sqrt V⟩

theorem symmetricPair_probability (m V : ℝ) : (symmetricPair m V).IsProbability := by
  norm_num [TwoPoint.IsProbability, symmetricPair]

theorem symmetricPair_mean (m V : ℝ) : (symmetricPair m V).mean = m := by
  dsimp [TwoPoint.mean, symmetricPair]
  ring

theorem symmetricPair_variance (m V : ℝ) (hV : 0 ≤ V) :
    (symmetricPair m V).centeredSecond m = V := by
  dsimp [TwoPoint.centeredSecond, symmetricPair]
  have hsq := Real.sq_sqrt hV
  nlinarith

/-- An asymmetric law preserves a lower bound on the projection `p*t`,
while allowing any nonnegative variance. For `p = 0`, use `symmetricPair`.
The lower projected deviation is `-d`, and the upper one is `V*p²/d`. -/
def oneSidedPair (m p d V : ℝ) : TwoPoint :=
  ⟨V * p ^ 2 / (d ^ 2 + V * p ^ 2), d ^ 2 / (d ^ 2 + V * p ^ 2),
    m - d / p, m + V * p / d⟩

theorem oneSidedPair_denom_pos (p d V : ℝ) (hd : 0 < d) (hV : 0 ≤ V) :
    0 < d ^ 2 + V * p ^ 2 := by
  have hprod := mul_nonneg hV (sq_nonneg p)
  nlinarith

theorem oneSidedPair_probability (m p d V : ℝ) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).IsProbability := by
  have hden := oneSidedPair_denom_pos p d V hd hV
  dsimp [TwoPoint.IsProbability, oneSidedPair]
  refine ⟨div_nonneg (mul_nonneg hV (sq_nonneg p)) (le_of_lt hden),
    div_nonneg (sq_nonneg d) (le_of_lt hden), ?_⟩
  field_simp; ring

theorem oneSidedPair_mean (m p d V : ℝ) (hp : p ≠ 0) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).mean = m := by
  have hden := ne_of_gt (oneSidedPair_denom_pos p d V hd hV)
  have hdne := ne_of_gt hd
  dsimp [TwoPoint.mean, oneSidedPair]
  field_simp; ring

theorem oneSidedPair_variance (m p d V : ℝ)
    (hp : p ≠ 0) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).centeredSecond m = V := by
  have hden := ne_of_gt (oneSidedPair_denom_pos p d V hd hV)
  have hdne := ne_of_gt hd
  dsimp [TwoPoint.centeredSecond, oneSidedPair]
  field_simp; ring

theorem oneSidedPair_lower_projection (m p d V : ℝ) (hp : p ≠ 0) :
    p * ((oneSidedPair m p d V).leftValue - m) = -d := by
  dsimp [oneSidedPair]
  field_simp; ring

theorem oneSidedPair_upper_projection (m p d V : ℝ) :
    p * ((oneSidedPair m p d V).rightValue - m) = V * p ^ 2 / d := by
  dsimp [oneSidedPair]
  ring

/-- Every mean whose stress projection is strictly above `2` has a finite
two-point distribution with any prescribed nonnegative variance, with both
support points still strictly above that same projection threshold. This is
a feasibility statement for the tilt moments, not the full true-cone test. -/
theorem exists_projected_twoPoint (p₁ p₂ m V : ℝ)
    (hP : 2 < p₁ + p₂ * m) (hV : 0 ≤ V) :
    ∃ q : TwoPoint, q.IsProbability ∧ q.mean = m ∧ q.centeredSecond m = V ∧
      2 < p₁ + p₂ * q.leftValue ∧ 2 < p₁ + p₂ * q.rightValue := by
  by_cases hp : p₂ = 0
  · refine ⟨symmetricPair m V, symmetricPair_probability m V,
      symmetricPair_mean m V, symmetricPair_variance m V hV, ?_, ?_⟩ <;>
      simpa only [hp, zero_mul, add_zero] using hP
  · let d := (p₁ + p₂ * m - 2) / 2
    have hd : 0 < d := by dsimp [d]; linarith
    refine ⟨oneSidedPair m p₂ d V, oneSidedPair_probability m p₂ d V hd hV,
      oneSidedPair_mean m p₂ d V hp hd hV,
      oneSidedPair_variance m p₂ d V hp hd hV, ?_, ?_⟩
    · have hleft := oneSidedPair_lower_projection m p₂ d V hp
      dsimp [d] at hleft
      linarith
    · have hright := oneSidedPair_upper_projection m p₂ d V
      have hinc : 0 ≤ V * p₂ ^ 2 / d :=
        div_nonneg (mul_nonneg hV (sq_nonneg p₂)) (le_of_lt hd)
      linarith

/-- The cutoff correction used by the manuscript remains between the old
speed and the target speed whenever the old speed is below that target. -/
theorem corrected_speed_bounds (v₀ vstar ζ : ℝ)
    (hz₀ : 0 ≤ ζ) (hz₁ : ζ ≤ 1) (hv : v₀ ≤ vstar) :
    v₀ ≤ v₀ + ζ ^ 2 * (vstar - v₀) ∧
      v₀ + ζ ^ 2 * (vstar - v₀) ≤ vstar := by
  have hs : ζ ^ 2 ≤ 1 := by nlinarith
  have hlow := mul_nonneg (sq_nonneg ζ) (sub_nonneg.mpr hv)
  have hupp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hv)
  constructor <;> nlinarith

end

end NavierStokes.LoopMoments

end

end

@[expose] public section

namespace NavierStokes.SmoothLoop

noncomputable section

open MeasureTheory
open scoped Interval ContDiff

/-- Angular average over one full turn. -/
def angularMean (f : ℝ → ℝ) : ℝ := (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) / (2 * Real.pi)

theorem period_pos : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos

theorem period_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt period_pos

theorem angularMean_const (c : ℝ) : angularMean (fun _ => c) = c := by
  simp only [angularMean, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp [period_ne_zero]

theorem angularMean_add (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    angularMean (fun θ => f θ + g θ) = angularMean f + angularMean g := by
  unfold angularMean
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

theorem angularMean_sub (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    angularMean (fun θ => f θ - g θ) = angularMean f - angularMean g := by
  unfold angularMean
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

theorem angularMean_const_mul (c : ℝ) (f : ℝ → ℝ) :
    angularMean (fun θ => c * f θ) = c * angularMean f := by
  unfold angularMean
  rw [intervalIntegral.integral_const_mul]
  ring

theorem angularMean_div_const (f : ℝ → ℝ) (c : ℝ) :
    angularMean (fun θ => f θ / c) = angularMean f / c := by
  simp only [div_eq_mul_inv, mul_comm _ c⁻¹, angularMean_const_mul]

theorem angularMean_nonneg (f : ℝ → ℝ) (hf : ∀ θ, 0 ≤ f θ) :
    0 ≤ angularMean f := by
  exact div_nonneg
    (intervalIntegral.integral_nonneg_of_forall (le_of_lt period_pos) hf)
    (le_of_lt period_pos)

theorem angularMean_pos (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ θ, 0 < f θ) :
    0 < angularMean f := by
  exact div_pos (intervalIntegral.intervalIntegral_pos_of_pos
    (hf.intervalIntegrable _ _) hpos period_pos) period_pos

theorem angularMean_cos : angularMean Real.cos = 0 := by
  simp [angularMean, Real.sin_two_pi]

theorem angularMean_cos_sq : angularMean (fun θ => Real.cos θ ^ 2) = 1 / 2 := by
  simp only [angularMean, integral_cos_sq, Real.sin_two_pi, Real.sin_zero,
    mul_zero, sub_zero, zero_add]
  field_simp [Real.pi_ne_zero]

/-- A smooth tilt parametrized by its mean and its (signed) amplitude. -/
def cosineTilt (m amplitude θ : ℝ) : ℝ := m + amplitude * Real.cos θ

theorem cosineTilt_periodic (m amplitude : ℝ) :
    Function.Periodic (cosineTilt m amplitude) (2 * Real.pi) := by
  intro θ
  simp only [cosineTilt, Real.cos_periodic θ]

theorem cosineTilt_contDiff (m amplitude : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (cosineTilt m amplitude) := by
  exact contDiff_const.add (contDiff_const.mul Real.contDiff_cos)

theorem cosineTilt_mean (m amplitude : ℝ) : angularMean (cosineTilt m amplitude) = m := by
  unfold cosineTilt
  rw [angularMean_add _ _ continuous_const (continuous_const.fun_mul Real.continuous_cos),
    angularMean_const, angularMean_const_mul, angularMean_cos]
  ring

theorem cosineTilt_variance (m amplitude : ℝ) :
    angularMean (fun θ => (cosineTilt m amplitude θ - m) ^ 2) = amplitude ^ 2 / 2 := by
  have heq : (fun θ => (cosineTilt m amplitude θ - m) ^ 2) =
      fun θ => amplitude ^ 2 * Real.cos θ ^ 2 := by
    funext θ
    dsimp [cosineTilt]
    ring
  rw [heq, angularMean_const_mul, angularMean_cos_sq]
  ring

/-- Variance expansion for actual angular integrals. -/
theorem angular_variance_identity (t : ℝ → ℝ) (m : ℝ)
    (ht : Continuous t) (hmean : angularMean t = m) :
    angularMean (fun θ => (t θ - m) ^ 2) = angularMean (fun θ => t θ ^ 2) - m ^ 2 := by
  have heq : (fun θ => (t θ - m) ^ 2) =
      (fun θ => (t θ ^ 2 - (2 * m) * t θ) + m ^ 2) := by
    funext θ
    ring
  rw [heq, angularMean_add _ _ ((ht.fun_pow 2).fun_sub (continuous_const.fun_mul ht))
      continuous_const,
    angularMean_sub _ _ (ht.fun_pow 2) (continuous_const.fun_mul ht), angularMean_const_mul,
    angularMean_const, hmean]
  ring

theorem angular_energy_moment (t : ℝ → ℝ) (a m ρ : ℝ) (ha : a ≠ 0)
    (ht : Continuous t) (hmean : angularMean t = m)
    (hvar : angularMean (fun θ => (t θ - m) ^ 2) = ρ / a) :
    a * angularMean (fun θ => 1 + t θ ^ 2) = a * (1 + m ^ 2) + ρ := by
  have hv := angular_variance_identity t m ht hmean
  have hsecond : angularMean (fun θ => t θ ^ 2) = m ^ 2 + ρ / a := by linarith
  rw [angularMean_add _ _ continuous_const (ht.fun_pow 2), angularMean_const, hsecond]
  field_simp; ring

open LoopMoments in
theorem angular_rephasing_moments (t : ℝ → ℝ) (a m ρ v : ℝ)
    (ha : a ≠ 0) (hv : v ≠ 0) (ht : Continuous t) (hmean : angularMean t = m)
    (hvar : angularMean (fun θ => (t θ - m) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + m ^ 2) + ρ) :
    angularMean (fun θ => phaseDensity a v (t θ)) = 1 ∧
      angularMean (fun θ => phaseDensity a v (t θ) * loopA v (t θ)) = a ∧
      angularMean (fun θ => phaseDensity a v (t θ) * loopC v (t θ)) = a * m := by
  constructor
  · have he := angular_energy_moment t a m ρ ha ht hmean hvar
    rw [← hspeed] at he
    simp only [phaseDensity, angularMean_div_const, angularMean_const_mul, he, div_self hv]
  constructor
  · simp_rw [density_times_loopA a v _ hv]
    exact angularMean_const a
  · simp_rw [density_times_loopC a v _ hv]
    rw [angularMean_const_mul, hmean]

open LoopMoments in
theorem smooth_loop_shears (t : ℝ → ℝ) (v : ℝ)
    (ht : ContDiff ℝ (∞ : WithTop ℕ∞) t) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fun θ => loopA v (t θ)) ∧
      ContDiff ℝ (∞ : WithTop ℕ∞) (fun θ => loopC v (t θ)) := by
  have hden : ContDiff ℝ (∞ : WithTop ℕ∞) (fun θ => 1 + t θ ^ 2) :=
    contDiff_const.add (ht.pow 2)
  have hnz : ∀ θ, 1 + t θ ^ 2 ≠ 0 := fun θ => ne_of_gt (one_add_sq_pos (t θ))
  exact ⟨contDiff_const.div hden hnz, (contDiff_const.mul ht).div hden hnz⟩

open LoopMoments in
theorem periodic_loop_shears (t : ℝ → ℝ) (v : ℝ)
    (ht : Function.Periodic t (2 * Real.pi)) :
    Function.Periodic (fun θ => loopA v (t θ)) (2 * Real.pi) ∧
      Function.Periodic (fun θ => loopC v (t θ)) (2 * Real.pi) := by
  constructor <;> intro θ <;> dsimp only <;> rw [ht θ]

/-- The normalizing angular mean in the manuscript's exponential family,
using cosine instead of sine (a translation of the angular origin). -/
def expNormalizer (s : ℝ) : ℝ := angularMean (fun θ => Real.exp (s * Real.cos θ))

theorem expNormalizer_pos (s : ℝ) : 0 < expNormalizer s := by
  apply angularMean_pos
  · exact Real.continuous_exp.comp (continuous_const.fun_mul Real.continuous_cos)
  · intro θ
    exact Real.exp_pos _

theorem expNormalizer_zero : expNormalizer 0 = 1 := by
  simp only [expNormalizer, zero_mul, Real.exp_zero, angularMean_const]

/-- Normalized exp, given by `Real.exp (s * Real.cos θ) / expNormalizer s`. -/
def normalizedExp (s θ : ℝ) : ℝ := Real.exp (s * Real.cos θ) / expNormalizer s

theorem normalizedExp_pos (s θ : ℝ) : 0 < normalizedExp s θ :=
  div_pos (Real.exp_pos _) (expNormalizer_pos s)

theorem normalizedExp_contDiff (s : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (normalizedExp s) := by
  exact (Real.contDiff_exp.comp (contDiff_const.mul Real.contDiff_cos)).div_const _

theorem normalizedExp_periodic (s : ℝ) :
    Function.Periodic (normalizedExp s) (2 * Real.pi) := by
  intro θ
  simp only [normalizedExp, Real.cos_periodic θ]

theorem normalizedExp_mean (s : ℝ) : angularMean (normalizedExp s) = 1 := by
  unfold normalizedExp
  rw [angularMean_div_const]
  exact div_self (ne_of_gt (expNormalizer_pos s))

theorem normalizedExp_second_moment (s : ℝ) :
    angularMean (fun θ => normalizedExp s θ ^ 2) =
      expNormalizer (2 * s) / expNormalizer s ^ 2 := by
  have heq : (fun θ => normalizedExp s θ ^ 2) =
      (fun θ => Real.exp ((2 * s) * Real.cos θ) / expNormalizer s ^ 2) := by
    funext θ
    dsimp [normalizedExp]
    rw [div_pow, show (2 * s) * Real.cos θ = s * Real.cos θ + s * Real.cos θ by ring,
      Real.exp_add, pow_two]
  rw [heq, angularMean_div_const]
  rfl

theorem normalizedExp_variance (s : ℝ) :
    angularMean (fun θ => (normalizedExp s θ - 1) ^ 2) =
      expNormalizer (2 * s) / expNormalizer s ^ 2 - 1 := by
  rw [angular_variance_identity _ 1 (normalizedExp_contDiff s).continuous (normalizedExp_mean s),
    normalizedExp_second_moment]
  norm_num

/-- The divided exponential tilt. Its smooth extension at `p=0` is handled
separately below; this expression by itself is not that extension. -/
def expTilt (m d μ p θ : ℝ) : ℝ := m + (d / p) * (normalizedExp (μ * p) θ - 1)

theorem expTilt_contDiff (m d μ p : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (expTilt m d μ p) := by
  exact contDiff_const.add (contDiff_const.mul ((normalizedExp_contDiff _).sub contDiff_const))

theorem expTilt_periodic (m d μ p : ℝ) :
    Function.Periodic (expTilt m d μ p) (2 * Real.pi) := by
  intro θ
  simp only [expTilt, normalizedExp_periodic (μ * p) θ]

theorem expTilt_mean (m d μ p : ℝ) : angularMean (expTilt m d μ p) = m := by
  unfold expTilt
  rw [angularMean_add _ _ continuous_const
      (continuous_const.fun_mul ((normalizedExp_contDiff _).continuous.fun_sub continuous_const)),
    angularMean_const, angularMean_const_mul,
    angularMean_sub _ _ (normalizedExp_contDiff _).continuous continuous_const,
    normalizedExp_mean, angularMean_const]
  ring

theorem expTilt_variance (m d μ p : ℝ) :
    angularMean (fun θ => (expTilt m d μ p θ - m) ^ 2) =
      (d / p) ^ 2 * (expNormalizer (2 * (μ * p)) / expNormalizer (μ * p) ^ 2 - 1) := by
  have heq : (fun θ => (expTilt m d μ p θ - m) ^ 2) =
      fun θ => (d / p) ^ 2 * (normalizedExp (μ * p) θ - 1) ^ 2 := by
    funext θ
    dsimp [expTilt]
    ring
  rw [heq, angularMean_const_mul, normalizedExp_variance]

theorem expTilt_projection (p₁ p₂ m d μ θ : ℝ) (hp : p₂ ≠ 0) :
    p₁ + p₂ * expTilt m d μ p₂ θ =
      (p₁ + p₂ * m - d) + d * normalizedExp (μ * p₂) θ := by
  unfold expTilt
  field_simp; ring

theorem expTilt_projection_lower (p₁ p₂ m d μ : ℝ) (hp : p₂ ≠ 0) (hd : 0 < d) :
    ∀ θ, p₁ + p₂ * m - d < p₁ + p₂ * expTilt m d μ p₂ θ := by
  intro θ
  rw [expTilt_projection p₁ p₂ m d μ θ hp]
  exact lt_add_of_pos_right _ (mul_pos hd (normalizedExp_pos _ _))

/-- Correct value at vanishing transverse stress. Smooth dependence across
`p=0` is a separate analytic obligation; only angular smoothness is proved. -/
def extendedExpTilt (m d μ p : ℝ) : ℝ → ℝ :=
  if p = 0 then cosineTilt m (d * μ) else expTilt m d μ p

theorem extendedExpTilt_contDiff (m d μ p : ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (extendedExpTilt m d μ p) := by
  by_cases hp : p = 0
  · simpa only [extendedExpTilt, ite_eq_left hp] using cosineTilt_contDiff m (d * μ)
  · simpa only [extendedExpTilt, ite_eq_right hp] using expTilt_contDiff m d μ p

theorem extendedExpTilt_periodic (m d μ p : ℝ) :
    Function.Periodic (extendedExpTilt m d μ p) (2 * Real.pi) := by
  by_cases hp : p = 0
  · simpa only [extendedExpTilt, ite_eq_left hp] using cosineTilt_periodic m (d * μ)
  · simpa only [extendedExpTilt, ite_eq_right hp] using expTilt_periodic m d μ p

theorem extendedExpTilt_mean (m d μ p : ℝ) :
    angularMean (extendedExpTilt m d μ p) = m := by
  by_cases hp : p = 0
  · simpa only [extendedExpTilt, ite_eq_left hp] using cosineTilt_mean m (d * μ)
  · simpa only [extendedExpTilt, ite_eq_right hp] using expTilt_mean m d μ p

theorem extendedExpTilt_variance_zero (m d μ : ℝ) :
    angularMean (fun θ => (extendedExpTilt m d μ 0 θ - m) ^ 2) = d ^ 2 * μ ^ 2 / 2 := by
  simp [extendedExpTilt, cosineTilt_variance, mul_pow]

theorem extendedExpTilt_projection_positive (p₁ p₂ m d μ : ℝ)
    (hd : 0 < d) (hmargin : 2 ≤ p₁ + p₂ * m - d) :
    ∀ θ, 2 < p₁ + p₂ * extendedExpTilt m d μ p₂ θ := by
  intro θ
  by_cases hp : p₂ = 0
  · simp only [hp, zero_mul, add_zero]
      at hmargin ⊢
    linarith
  · simp only [extendedExpTilt, ite_eq_right hp]
    exact lt_of_le_of_lt hmargin (expTilt_projection_lower p₁ p₂ m d μ hp hd θ)

/-- A positive normalized density on a circle, given as a smooth periodic
function on its universal covering line. The construction `densityOfTilt`
below supplies these data from the already proved moment identity. -/
structure CircleDensity where
  /-- Rate of `CircleDensity`, of type `ℝ → ℝ`. -/
  rate : ℝ → ℝ
  smooth : ContDiff ℝ (∞ : WithTop ℕ∞) rate
  positive : ∀ θ, 0 < rate θ
  periodic : Function.Periodic rate (2 * Real.pi)
  integral_one : (∫ θ in (0 : ℝ)..(2 * Real.pi), rate θ) = 1

/-- Phase map, given by `∫ x in (0 : ℝ)..θ, d.rate x`. -/
def phaseMap (d : CircleDensity) (θ : ℝ) : ℝ := ∫ x in (0 : ℝ)..θ, d.rate x

theorem phaseMap_hasDerivAt (d : CircleDensity) (θ : ℝ) :
    HasDerivAt (phaseMap d) (d.rate θ) θ := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact d.smooth.continuous.intervalIntegrable _ _
  · exact d.smooth.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact d.smooth.continuous.continuousAt

theorem phaseMap_contDiff (d : CircleDensity) : ContDiff ℝ (∞ : WithTop ℕ∞) (phaseMap d) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun θ => (phaseMap_hasDerivAt d θ).differentiableAt, ?_⟩
  have heq : deriv (phaseMap d) = d.rate := funext (fun θ => (phaseMap_hasDerivAt d θ).deriv)
  rw [heq]
  exact d.smooth

theorem phaseMap_strictMono (d : CircleDensity) : StrictMono (phaseMap d) :=
  strictMono_of_hasDerivAt_pos (phaseMap_hasDerivAt d) d.positive

theorem phaseMap_zero (d : CircleDensity) : phaseMap d 0 = 0 := by simp [phaseMap]

theorem phaseMap_fullTurn (d : CircleDensity) : phaseMap d (2 * Real.pi) = 1 := d.integral_one

theorem phaseMap_add_fullTurn (d : CircleDensity) (θ : ℝ) :
    phaseMap d (θ + 2 * Real.pi) = phaseMap d θ + 1 := by
  have h := d.periodic.intervalIntegral_add_eq_add 0 θ
    (fun a b => d.smooth.continuous.intervalIntegrable a b)
  simpa only [phaseMap, zero_add, d.integral_one] using h

theorem phaseMap_int_fullTurn (d : CircleDensity) (n : ℤ) :
    phaseMap d ((n : ℝ) * (2 * Real.pi)) = (n : ℝ) := by
  have h := d.periodic.intervalIntegral_add_zsmul_eq n 0
    (fun a b => d.smooth.continuous.intervalIntegrable a b)
  simpa only [phaseMap, zero_add, d.integral_one, zsmul_eq_mul, mul_one] using h

theorem phaseMap_surjective (d : CircleDensity) : Function.Surjective (phaseMap d) := by
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt |y|
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy : -(n : ℝ) ≤ y ∧ y ≤ (n : ℝ) := by
    have h₁ := neg_abs_le y
    have h₂ := le_abs_self y
    constructor <;> linarith
  have hlo : phaseMap d (-(n : ℝ) * (2 * Real.pi)) = -(n : ℝ) := by
    simpa only [Int.cast_neg, Int.cast_natCast] using phaseMap_int_fullTurn d (-(n : ℤ))
  have hhi : phaseMap d ((n : ℝ) * (2 * Real.pi)) = (n : ℝ) := by
    simpa only [Int.cast_natCast] using phaseMap_int_fullTurn d (n : ℤ)
  have hab : -(n : ℝ) * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right (by linarith) (le_of_lt period_pos)
  have hmem : y ∈ Set.Icc (phaseMap d (-(n : ℝ) * (2 * Real.pi)))
      (phaseMap d ((n : ℝ) * (2 * Real.pi))) := by
    simpa only [hlo, hhi, Set.mem_Icc] using hy
  obtain ⟨θ, _, heq⟩ :=
    intermediate_value_Icc hab (phaseMap_contDiff d).continuous.continuousOn hmem
  exact ⟨θ, heq⟩

/-- The phase map is an actual global homeomorphism, not an assumed inverse. -/
def phaseHomeomorph (d : CircleDensity) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (phaseMap d) (phaseMap_strictMono d)
    (phaseMap_surjective d)).toHomeomorph

theorem phaseHomeomorph_apply (d : CircleDensity) (θ : ℝ) :
    phaseHomeomorph d θ = phaseMap d θ := rfl

theorem phaseInverse_add_one (d : CircleDensity) (φ : ℝ) :
    (phaseHomeomorph d).symm (φ + 1) = (phaseHomeomorph d).symm φ + 2 * Real.pi := by
  apply (phaseHomeomorph d).injective
  rw [(phaseHomeomorph d).apply_symm_apply, phaseHomeomorph_apply, phaseMap_add_fullTurn]
  change φ + 1 = phaseHomeomorph d ((phaseHomeomorph d).symm φ) + 1
  rw [(phaseHomeomorph d).apply_symm_apply]

/-- Rephase, given by `f ((phaseHomeomorph d).symm φ)`. -/
def rephase (d : CircleDensity) (f : ℝ → ℝ) (φ : ℝ) : ℝ :=
  f ((phaseHomeomorph d).symm φ)

theorem rephase_periodic (d : CircleDensity) (f : ℝ → ℝ)
    (hf : Function.Periodic f (2 * Real.pi)) : Function.Periodic (rephase d f) 1 := by
  intro φ
  dsimp [rephase]
  rw [phaseInverse_add_one]
  exact hf _

theorem rephase_phaseMap (d : CircleDensity) (f : ℝ → ℝ) (θ : ℝ) :
    rephase d f (phaseMap d θ) = f θ := by
  change f ((phaseHomeomorph d).symm (phaseHomeomorph d θ)) = f θ
  rw [(phaseHomeomorph d).symm_apply_apply]

/-- The actual change of variables for the constructed smooth inverse. -/
theorem integral_rephase (d : CircleDensity) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ φ in (0 : ℝ)..1, rephase d f φ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * d.rate θ := by
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 2 * Real.pi) (f := phaseMap d) (f' := d.rate)
    (g := rephase d f) (fun θ _ => phaseMap_hasDerivAt d θ)
    d.smooth.continuous.continuousOn (hf.comp (phaseHomeomorph d).symm.continuous)
  simpa only [Function.comp_apply, rephase_phaseMap, phaseMap_zero, phaseMap_fullTurn] using
      hsub.symm

open LoopMoments in
/-- Density of tilt, bundling `rate`, `smooth`, `positive`, `periodic` and the required
compatibility proofs. -/
def densityOfTilt (t : ℝ → ℝ) (a m ρ v : ℝ)
    (ha : 0 < a) (hv : 0 < v) (ht : ContDiff ℝ (∞ : WithTop ℕ∞) t)
    (hperiodic : Function.Periodic t (2 * Real.pi))
    (hmean : angularMean t = m)
    (hvar : angularMean (fun θ => (t θ - m) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + m ^ 2) + ρ) : CircleDensity where
  rate θ := phaseDensity a v (t θ) / (2 * Real.pi)
  smooth := ((contDiff_const.mul (contDiff_const.add (ht.pow 2))).div_const v).div_const _
  positive θ := div_pos (phaseDensity_pos a v (t θ) ha hv) period_pos
  periodic := by intro θ; dsimp only; rw [hperiodic θ]
  integral_one := by
    rw [intervalIntegral.integral_div]
    exact (angular_rephasing_moments t a m ρ v (ne_of_gt ha) (ne_of_gt hv)
      ht.continuous hmean hvar hspeed).1

end

end NavierStokes.SmoothLoop
