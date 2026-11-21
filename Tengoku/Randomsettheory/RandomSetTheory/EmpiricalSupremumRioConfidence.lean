/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.ContinuousSupremumRioConfidence
import Tengoku.Randomsettheory.RandomSetTheory.EmpiricalEnvelopeMomentScaling
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentRioRate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rio confidence bounds for continuous empirical averages

This file combines the continuous-supremum Rio endpoint with the elementary
moment scaling of empirically normalized envelopes.  It is the generic
high-level interface for a process of the form

`n⁻¹ ∑ i, W i (Y i) t`.

The user supplies only ordinary coordinate-envelope moments.  The aggregate
replace-one parameters are then fixed internally to

`V = 4 K₂² / n` and `Q = 2^q Kq^q / n^(q - 1)`.

In particular, the statement exposes neither free Rio moment parameters nor
a free truncation scale.
-/

open Real Set Finset MeasureTheory TopologicalSpace
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega T Z : Type*} {mOmega : MeasurableSpace Omega}
  [MeasurableSpace Z]
  [TopologicalSpace T] [SeparableSpace T] [Nonempty T]

/-- Coordinate kernel normalized by the empirical-average factor `1 / n`.-/
def empiricalNormalizedKernel (n : Nat) (W : Fin n → Z → T → Real)
    (i : Fin n) (z : Z) (t : T) : Real :=
  ((n : Real)⁻¹) * W i z t

omit [MeasurableSpace Z] [TopologicalSpace T] [SeparableSpace T] [Nonempty T] in
@[simp]
theorem empiricalNormalizedKernel_apply
    (n : Nat) (W : Fin n → Z → T → Real)
    (i : Fin n) (z : Z) (t : T) :
    empiricalNormalizedKernel n W i z t = W i z t / (n : Real) := by
  simp only [empiricalNormalizedKernel, div_eq_mul_inv, mul_comm]

omit [MeasurableSpace Z] [TopologicalSpace T] [SeparableSpace T] [Nonempty T] in
@[simp]
theorem finiteCoordinateSumProcess_empiricalNormalizedKernel
    (n : Nat) (Y : Nat → Omega → Z) (W : Fin n → Z → T → Real)
    (t : T) (omega : Omega) :
    finiteCoordinateSumProcess Y (empiricalNormalizedKernel n W) t omega =
      ((n : Real)⁻¹) * finiteCoordinateSumProcess Y W t omega := by
  unfold finiteCoordinateSumProcess empiricalNormalizedKernel
  rw [Finset.mul_sum]

/-- Rio's confidence bound for the centered supremum of a continuous
empirical average, stated directly from uniform raw envelope moments.

The strict positivity assumptions on `Ktwo` and `Kq` make the positive Rio
parameters required by the underlying endpoint explicit.  They are harmless
in applications, where one may always enlarge a non-strict moment bound.-/
theorem conditionalValueAtRisk_iSup_empiricalAverageProcess_le_rioConfidence
    {mu : Measure Omega} {nu : Measure Z}
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [StandardBorelSpace Z] [Nonempty Z] [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat → Omega → Z)
    (hY : forall i, Measurable (Y i)) (hIndep : iIndepFun Y mu)
    (n q : Nat) (hn : 0 < n) (hq : 3 ≤ q)
    (W : Fin n → Z → T → Real) (A : Fin n → Z → Real)
    (hYlaw : forall i, i < n → mu.map (Y i) = nu)
    (hWmeas : forall i t, Measurable (fun z ↦ W i z t))
    (hWcontinuous : forall i z, Continuous (W i z))
    (hAq : forall i, MemLp (A i) q nu)
    (hA : forall i z, 0 ≤ A i z)
    (hdom : forall i z t, abs (W i z t) ≤ A i z)
    (Ktwo Kq : Real) (hKtwo : 0 < Ktwo) (hKq : 0 < Kq)
    (hsecond : forall i, (∫ z, A i z ^ 2 ∂nu) ≤ Ktwo ^ 2)
    (hqmoment : forall i, (∫ z, A i z ^ q ∂nu) ≤ Kq ^ q)
    {alpha : Real} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    conditionalValueAtRisk alpha
        (fun omega ↦
          (⨆ t, finiteCoordinateSumProcess Y
              (empiricalNormalizedKernel n W) t omega) -
            ∫ z, (⨆ t, finiteCoordinateSumProcess Y
              (empiricalNormalizedKernel n W) t z) ∂mu) mu ≤
      rioStrongMomentConfidenceRadius q
        (4 * Ktwo ^ 2 / (n : Real))
        ((2 : Real) ^ q * Kq ^ q / (n : Real) ^ (q - 1)) alpha := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hV : 0 < 4 * Ktwo ^ 2 / (n : Real) := by positivity
  have hQ :
      0 < (2 : Real) ^ q * Kq ^ q / (n : Real) ^ (q - 1) := by
    positivity
  have hsecondNormalized :
      (∑ i : Fin n, replaceOneCenteredMoment nu
        (empiricalNormalizedEnvelope n (A i)) 2) ≤
        4 * Ktwo ^ 2 / (n : Real) :=
    sum_replaceOneCenteredMoment_empiricalNormalizedEnvelope_two_le
      n q hn (by omega) A Ktwo hAq hA hsecond
  have hqmomentNormalized :
      (∑ i : Fin n, replaceOneCenteredMoment nu
        (empiricalNormalizedEnvelope n (A i)) q) ≤
        (2 : Real) ^ q * Kq ^ q / (n : Real) ^ (q - 1) :=
    sum_replaceOneCenteredMoment_empiricalNormalizedEnvelope_q_le
      n q hn (by omega) A Kq hAq hA hqmoment
  have hdomNormalized : forall i z t,
      abs (empiricalNormalizedKernel n W i z t) ≤
        empiricalNormalizedEnvelope n (A i) z := by
    intro i z t
    have hscale : 0 ≤ (n : Real)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    change abs (((n : Real)⁻¹ * W i z t)) ≤ (n : Real)⁻¹ * A i z
    rw [abs_mul, abs_inv, abs_of_nonneg hnReal.le]
    exact mul_le_mul_of_nonneg_left (hdom i z t) hscale
  exact conditionalValueAtRisk_iSup_finiteCoordinateSumProcess_le_rioConfidence
    z0 Y hY hIndep n q hq (empiricalNormalizedKernel n W)
      (fun i ↦ empiricalNormalizedEnvelope n (A i)) hYlaw
      (fun i t ↦ measurable_const.mul (hWmeas i t))
      (fun i z ↦ continuous_const.mul (hWcontinuous i z))
      (fun i ↦ memLp_empiricalNormalizedEnvelope n (A i) q (hAq i))
      (fun i z ↦ empiricalNormalizedEnvelope_nonneg n (A i) (hA i) z)
      hdomNormalized
      (V := 4 * Ktwo ^ 2 / (n : Real))
      (Q := (2 : Real) ^ q * Kq ^ q / (n : Real) ^ (q - 1))
      hV hQ hsecondNormalized hqmomentNormalized halpha0 halpha1

/-- Polynomial-rate form of the preceding empirical-supremum estimate.
The Gaussian contribution has scale `Ktwo / sqrt n`, while the strong-moment
contribution has scale `Kq / n^(1 - 1/q) * alpha^(-1/q)`.-/
theorem conditionalValueAtRisk_iSup_empiricalAverageProcess_le_polynomialRate
    {mu : Measure Omega} {nu : Measure Z}
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [StandardBorelSpace Z] [Nonempty Z] [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat → Omega → Z)
    (hY : forall i, Measurable (Y i)) (hIndep : iIndepFun Y mu)
    (n q : Nat) (hn : 0 < n) (hq : 3 ≤ q)
    (W : Fin n → Z → T → Real) (A : Fin n → Z → Real)
    (hYlaw : forall i, i < n → mu.map (Y i) = nu)
    (hWmeas : forall i t, Measurable (fun z ↦ W i z t))
    (hWcontinuous : forall i z, Continuous (W i z))
    (hAq : forall i, MemLp (A i) q nu)
    (hA : forall i z, 0 ≤ A i z)
    (hdom : forall i z t, abs (W i z t) ≤ A i z)
    (Ktwo Kq : Real) (hKtwo : 0 < Ktwo) (hKq : 0 < Kq)
    (hsecond : forall i, (∫ z, A i z ^ 2 ∂nu) ≤ Ktwo ^ 2)
    (hqmoment : forall i, (∫ z, A i z ^ q ∂nu) ≤ Kq ^ q)
    {alpha : Real} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    conditionalValueAtRisk alpha
        (fun omega ↦
          (⨆ t, finiteCoordinateSumProcess Y
              (empiricalNormalizedKernel n W) t omega) -
            ∫ z, (⨆ t, finiteCoordinateSumProcess Y
              (empiricalNormalizedKernel n W) t z) ∂mu) mu ≤
      Real.sqrt
          (2 * (4 * Ktwo ^ 2 / (n : Real)) * (-Real.log alpha)) +
        rioPolynomialCoefficient q * empiricalPolynomialScale q n Kq *
          (1 / alpha) ^ (1 / (q : Real)) := by
  exact (conditionalValueAtRisk_iSup_empiricalAverageProcess_le_rioConfidence
    z0 Y hY hIndep n q hn hq W A hYlaw hWmeas hWcontinuous hAq hA hdom
      Ktwo Kq hKtwo hKq hsecond hqmoment halpha0 halpha1).trans
    (rioStrongMomentConfidenceRadius_empiricalMoment_le
      (by omega) hn hKq halpha0)

end ProbabilityTheory
