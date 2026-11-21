/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.L2LipschitzProcessTightness
import Tengoku.Seed.MeasureTheory.Measure.AEMeasurable
import Tengoku.Seed.MeasureTheory.Measure.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing the truncation from an `L²` Lipschitz empirical process

The truncated process used in the Bernstein chaining argument is compared
pathwise with the original centered process.  At the natural truncation level
`sqrt (n + 1)`, the Lipschitz coefficient of the remainder is bounded by

`(n + 1)⁻¹ * ∑ i < n + 1, R(Xᵢ)² + K²`.

Markov's inequality makes this coefficient bounded in probability uniformly
in `n`.  Hence the remainder laws are tight in the continuous path space, and
tightness transfers from the truncated processes to the original ones.
-/

open Filter Real Set Finset MeasureTheory Module
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology
open RandomSetTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega Z T iota : Type*} [MeasurableSpace Omega] [MeasurableSpace Z]
  [PseudoMetricSpace T] {mu : Measure Omega}

/-- The increment of one untruncated process-valued observation.-/
def lipschitzIncrement
    (H : Z → T → ℝ) (X : iota → Omega → Z) (i : iota)
    (s t : T) (omega : Omega) : ℝ :=
  H (X i omega) s - H (X i omega) t

/-- The original centered empirical process, anchored at `o`.-/
def centeredAnchoredEmpiricalProcess
    (H : Z → T → ℝ) (c : ℝ)
    (X : iota → Omega → Z) (I : Finset iota) (o : T)
    (omega : Omega) (t : T) : ℝ :=
  c * ∑ i ∈ I,
    (lipschitzIncrement H X i t o omega -
      ∫ xi, lipschitzIncrement H X i t o xi ∂mu)

omit [PseudoMetricSpace T] in
/--
@isnad1 id=measurab.2h9v.s6.22eddd8ef4f3 from=translated src=- shape=4b8cc326 vocab=e364d095
-/
theorem measurable_lipschitzIncrement
    (H : Z → T → ℝ) (X : iota → Omega → Z)
    (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t))
    (i : iota) (s t : T) :
    Measurable (lipschitzIncrement H X i s t) := by
  exact ((hH s).comp (hX i)).sub ((hH t).comp (hX i))

/-- An `L¹` envelope makes every untruncated increment integrable.
@isnad1 id=integrab.4h11v.s7.0a03b766fcd2 from=translated src=- shape=89089f00 vocab=e07c9df7
-/
theorem integrable_lipschitzIncrement
    (H : Z → T → ℝ) (R : Z → ℝ)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t))
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (i : iota) (hRint : Integrable (fun omega ↦ R (X i omega)) mu)
    (s t : T) :
    Integrable (lipschitzIncrement H X i s t) mu := by
  apply Integrable.mono'
    (hRint.const_mul (dist s t))
    (measurable_lipschitzIncrement H X hX hH i s t).aestronglyMeasurable
  filter_upwards with omega
  simpa only [lipschitzIncrement, Real.norm_eq_abs, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg dist_nonneg, mul_comm] using
      hLip (X i omega) s t

/-- The expected untruncated increment is Lipschitz in its free index.
@isnad1 id=lipschit.5h10v.s7.63745a97204c from=translated src=- shape=27e8562e vocab=e37337a9
-/
theorem lipschitzWith_integral_lipschitzIncrement
    (H : Z → T → ℝ) (R : Z → ℝ)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t))
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (i : iota) (hRint : Integrable (fun omega ↦ R (X i omega)) mu)
    (o : T) :
    LipschitzWith
      (nnrealOfNonneg (∫ omega, R (X i omega) ∂mu)
        (integral_nonneg fun omega ↦ hR (X i omega)))
      (fun t ↦ ∫ xi, lipschitzIncrement H X i t o xi ∂mu) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have hs := integrable_lipschitzIncrement
    H R X hX hH hLip i hRint s o
  have ht := integrable_lipschitzIncrement
    H R X hX hH hLip i hRint t o
  rw [Real.dist_eq, ← integral_sub hs ht]
  have hbound : ∀ᵐ xi ∂mu,
      ‖lipschitzIncrement H X i s o xi -
          lipschitzIncrement H X i t o xi‖ ≤
        dist s t * R (X i xi) := by
    filter_upwards with xi
    rw [Real.norm_eq_abs]
    calc
      |lipschitzIncrement H X i s o xi -
          lipschitzIncrement H X i t o xi| =
          |H (X i xi) s - H (X i xi) t| := by
            congr 1
            unfold lipschitzIncrement
            ring
      _ ≤ R (X i xi) * dist s t := hLip (X i xi) s t
      _ = dist s t * R (X i xi) := mul_comm _ _
  have hint := norm_integral_le_of_norm_le
    (hRint.const_mul (dist s t)) hbound
  rw [integral_const_mul] at hint
  simpa only [coe_nnrealOfNonneg, Real.norm_eq_abs, mul_comm] using hint

/-- Continuity of every sample path of the original anchored process.
@isnad1 id=continuo.6h12v.s7.397a90c98329 from=translated src=- shape=dd364197 vocab=60ef14a6
-/
theorem continuous_centeredAnchoredEmpiricalProcess
    (H : Z → T → ℝ) (R : Z → ℝ) (c : ℝ)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z))
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRint : ∀ i, Integrable (fun omega ↦ R (X i omega)) mu)
    (I : Finset iota) (o : T) (omega : Omega) :
    Continuous
      (centeredAnchoredEmpiricalProcess
        (mu := mu) H c X I o omega) := by
  unfold centeredAnchoredEmpiricalProcess
  apply continuous_const.mul
  apply continuous_finsetSum I
  intro i hi
  apply Continuous.sub
  · exact (hHcont (X i omega)).sub continuous_const
  · exact (lipschitzWith_integral_lipschitzIncrement
      H R X hX hHmeas hR hLip i (hRint i) o).continuous

omit [MeasurableSpace Z] [PseudoMetricSpace T] in
/--
@isnad1 id=eq.0h11v.s5.7005a3734987 from=translated src=- shape=d0d42a64 vocab=31858c9a
-/
@[simp]
theorem centeredAnchoredEmpiricalProcess_anchor
    (H : Z → T → ℝ) (c : ℝ)
    (X : iota → Omega → Z) (I : Finset iota) (o : T) (omega : Omega) :
    centeredAnchoredEmpiricalProcess
      (mu := mu) H c X I o omega o = 0 := by
  simp [centeredAnchoredEmpiricalProcess, lipschitzIncrement]

/-- The random Lipschitz envelope left after truncation.-/
def truncationTailEnvelope (R : Z → ℝ) (M : ℝ) (z : Z) : ℝ :=
  if M < R z then R z else 0

omit [MeasurableSpace Z] in
/--
@isnad1 id=le.1h8v.s7.04a43c925bac from=translated src=- shape=077f3673 vocab=429bf3b0
-/
theorem abs_lipschitzObservation_sub_truncated_sub_le
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (z : Z) (s t : T) :
    |(H z s - H z t) -
        (truncatedLipschitzObservation H R M z s -
          truncatedLipschitzObservation H R M z t)| ≤
      truncationTailEnvelope R M z * dist s t := by
  by_cases hz : R z ≤ M
  · have hz' : ¬ M < R z := not_lt_of_ge hz
    simp only [truncatedLipschitzObservation, ite_eq_left hz,
      truncationTailEnvelope, hz', ite_false, zero_mul, sub_self, abs_zero,
      le_refl]
  · have hz' : M < R z := lt_of_not_ge hz
    simp only [truncatedLipschitzObservation, ite_eq_right hz,
      truncationTailEnvelope, hz', ite_true, sub_zero]
    exact hLip z s t

/-- The increment discarded by truncation.-/
def truncationResidualIncrement
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ)
    (X : iota → Omega → Z) (i : iota) (s t : T) (omega : Omega) : ℝ :=
  lipschitzIncrement H X i s t omega -
    truncatedLipschitzIncrement H R M X i s t omega

/--
@isnad1 id=measurab.3h11v.s6.d42213539bba from=translated src=- shape=12f68799 vocab=172e1d8c
-/
theorem measurable_truncationResidualIncrement
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (i : iota) (s t : T) :
    Measurable (truncationResidualIncrement H R M X i s t) := by
  exact (measurable_lipschitzIncrement H X hX hH i s t).sub
    (measurable_truncatedLipschitzIncrement
      H R M X hX hH hRmeas i s t)

omit [MeasurableSpace Omega] [MeasurableSpace Z] in
/--
@isnad1 id=le.1h12v.s6.d979657fd2df from=translated src=- shape=c26f885a vocab=e0d216a9
-/
theorem abs_truncationResidualIncrement_le
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (X : iota → Omega → Z) (i : iota) (s t : T) (omega : Omega) :
    |truncationResidualIncrement H R M X i s t omega| ≤
      truncationTailEnvelope R M (X i omega) * dist s t := by
  exact abs_lipschitzObservation_sub_truncated_sub_le
    H R M hLip (X i omega) s t

omit [PseudoMetricSpace T] in
/--
@isnad1 id=measurab.1h3v.s4.96f72ceffe34 from=translated src=- shape=f90732d9 vocab=6d5b5f9f
-/
theorem measurable_truncationTailEnvelope
    (R : Z → ℝ) (M : ℝ) (hRmeas : Measurable R) :
    Measurable (truncationTailEnvelope R M) := by
  unfold truncationTailEnvelope
  exact Measurable.ite (measurableSet_lt measurable_const hRmeas)
    hRmeas measurable_const

omit [MeasurableSpace Z] [PseudoMetricSpace T] in
/--
@isnad1 id=le.1h4v.s5.5eeb28fd7e1c from=translated src=- shape=cd1a8a34 vocab=5393d4a0
-/
theorem truncationTailEnvelope_nonneg
    (R : Z → ℝ) (M : ℝ) (hR : ∀ z, 0 ≤ R z) (z : Z) :
    0 ≤ truncationTailEnvelope R M z := by
  unfold truncationTailEnvelope
  split_ifs
  · exact hR z
  · exact le_rfl

omit [MeasurableSpace Z] [PseudoMetricSpace T] in
/--
@isnad1 id=le.1h4v.s5.786c6541ec50 from=translated src=- shape=3a6c4715 vocab=5393d4a0
-/
theorem truncationTailEnvelope_le
    (R : Z → ℝ) (M : ℝ) (hR : ∀ z, 0 ≤ R z) (z : Z) :
    truncationTailEnvelope R M z ≤ R z := by
  unfold truncationTailEnvelope
  split_ifs
  · exact le_rfl
  · exact hR z

omit [PseudoMetricSpace T] in
/-- Integrability of the discarded envelope follows from integrability of
the original one.
@isnad1 id=integrab.4h6v.s6.e96272190fb3 from=translated src=- shape=c052dc49 vocab=94611b77
-/
theorem integrable_truncationTailEnvelope_comp
    (R : Z → ℝ) (M : ℝ) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z) (X : Omega → Z)
    (hX : Measurable X) (hRint : Integrable (fun omega ↦ R (X omega)) mu) :
    Integrable (fun omega ↦ truncationTailEnvelope R M (X omega)) mu := by
  apply Integrable.mono' hRint
    ((measurable_truncationTailEnvelope R M hRmeas).comp hX).aestronglyMeasurable
  filter_upwards with omega
  simp only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (truncationTailEnvelope_nonneg R M hR (X omega))]
  exact truncationTailEnvelope_le R M hR (X omega)

/-- The discarded increment is integrable under an `L¹` envelope.
@isnad1 id=integrab.7h12v.s7.848dcb2a6e4d from=translated src=- shape=4cb54d27 vocab=a3b18043
-/
theorem integrable_truncationResidualIncrement
    [IsFiniteMeasure mu]
    (H : Z → T → ℝ) (R : Z → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (i : iota) (hRint : Integrable (fun omega ↦ R (X i omega)) mu)
    (s t : T) :
    Integrable (truncationResidualIncrement H R M X i s t) mu := by
  exact (integrable_lipschitzIncrement H R X hX hH hLip i hRint s t).sub
    (integrable_truncatedLipschitzIncrement
      H R hM X hX hH hRmeas hR hLip i s t)

/-- The centered process carried by the observations discarded at level `M`.-/
def centeredAnchoredTruncationResidualProcess
    (H : Z → T → ℝ) (R : Z → ℝ) (M c : ℝ)
    (X : iota → Omega → Z) (I : Finset iota) (o : T)
    (omega : Omega) (t : T) : ℝ :=
  c * ∑ i ∈ I,
    (truncationResidualIncrement H R M X i t o omega -
      ∫ xi, truncationResidualIncrement H R M X i t o xi ∂mu)

/-- The difference between the original and truncated centered processes is
exactly the centered truncation remainder.
@isnad1 id=eq.7h14v.s7.c714abb7911a from=translated src=- shape=3e6a47d4 vocab=7244ac78
-/
theorem centeredAnchoredEmpiricalProcess_sub_truncated
    [IsFiniteMeasure mu]
    (H : Z → T → ℝ) (R : Z → ℝ) {M c : ℝ} (hM : 0 ≤ M)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRint : ∀ i, Integrable (fun omega ↦ R (X i omega)) mu)
    (I : Finset iota) (o : T) (omega : Omega) (t : T) :
    centeredAnchoredEmpiricalProcess (mu := mu) H c X I o omega t -
        centeredAnchoredTruncatedEmpiricalProcess
          (mu := mu) H R M c X I o omega t =
      centeredAnchoredTruncationResidualProcess
        (mu := mu) H R M c X I o omega t := by
  unfold centeredAnchoredEmpiricalProcess
    centeredAnchoredTruncatedEmpiricalProcess
    centeredAnchoredTruncationResidualProcess
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hraw := integrable_lipschitzIncrement
    H R X hX hH hLip i (hRint i) t o
  have htr := integrable_truncatedLipschitzIncrement (μ := mu)
    H R hM X hX hH hRmeas hR hLip i t o
  have hint :
      ∫ xi, truncationResidualIncrement H R M X i t o xi ∂mu =
        (∫ xi, lipschitzIncrement H X i t o xi ∂mu) -
          ∫ xi, truncatedLipschitzIncrement H R M X i t o xi ∂mu := by
    unfold truncationResidualIncrement
    exact integral_sub hraw htr
  rw [hint]
  unfold truncationResidualIncrement
  ring

/-- Algebraic increment identity for the centered truncation remainder.
@isnad1 id=eq.7h15v.s8.982c458f5f31 from=translated src=- shape=e70dc087 vocab=dc8f19d6
-/
theorem centeredAnchoredTruncationResidualProcess_sub
    [IsFiniteMeasure mu]
    (H : Z → T → ℝ) (R : Z → ℝ) {M c : ℝ} (hM : 0 ≤ M)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRint : ∀ i, Integrable (fun omega ↦ R (X i omega)) mu)
    (I : Finset iota) (o : T) (omega : Omega) (s t : T) :
    centeredAnchoredTruncationResidualProcess
          (mu := mu) H R M c X I o omega s -
        centeredAnchoredTruncationResidualProcess
          (mu := mu) H R M c X I o omega t =
      c * ∑ i ∈ I,
        (truncationResidualIncrement H R M X i s t omega -
          ∫ xi, truncationResidualIncrement H R M X i s t xi ∂mu) := by
  unfold centeredAnchoredTruncationResidualProcess
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hs := integrable_truncationResidualIncrement
    H R hM X hX hH hRmeas hR hLip i (hRint i) s o
  have ht := integrable_truncationResidualIncrement
    H R hM X hX hH hRmeas hR hLip i (hRint i) t o
  have hpoint :
      truncationResidualIncrement H R M X i s o omega -
          truncationResidualIncrement H R M X i t o omega =
        truncationResidualIncrement H R M X i s t omega := by
    unfold truncationResidualIncrement lipschitzIncrement
      truncatedLipschitzIncrement
    ring
  have hint :
      (∫ xi, truncationResidualIncrement H R M X i s o xi ∂mu) -
          ∫ xi, truncationResidualIncrement H R M X i t o xi ∂mu =
        ∫ xi, truncationResidualIncrement H R M X i s t xi ∂mu := by
    rw [← integral_sub hs ht]
    apply integral_congr_ae
    filter_upwards with xi
    unfold truncationResidualIncrement lipschitzIncrement
      truncatedLipschitzIncrement
    ring
  calc
    _ = (truncationResidualIncrement H R M X i s o omega -
          truncationResidualIncrement H R M X i t o omega) -
        ((∫ xi, truncationResidualIncrement H R M X i s o xi ∂mu) -
          ∫ xi, truncationResidualIncrement H R M X i t o xi ∂mu) := by ring
    _ = _ := by rw [hpoint, hint]

/-- Random Lipschitz coefficient of the centered truncation remainder.-/
def centeredTruncationResidualCoefficient
    (R : Z → ℝ) (M c : ℝ) (X : iota → Omega → Z)
    (I : Finset iota) (omega : Omega) : ℝ :=
  |c| * ∑ i ∈ I,
    (truncationTailEnvelope R M (X i omega) +
      ∫ xi, truncationTailEnvelope R M (X i xi) ∂mu)

/-- The centered truncation remainder is Lipschitz with its explicit random
coefficient.
@isnad1 id=le.7h15v.s8.cf3beaef02a1 from=translated src=- shape=b651ba38 vocab=03b7eb42
-/
theorem abs_centeredAnchoredTruncationResidualProcess_sub_le
    [IsFiniteMeasure mu]
    (H : Z → T → ℝ) (R : Z → ℝ) {M c : ℝ} (hM : 0 ≤ M)
    (X : iota → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRint : ∀ i, Integrable (fun omega ↦ R (X i omega)) mu)
    (I : Finset iota) (o : T) (omega : Omega) (s t : T) :
    |centeredAnchoredTruncationResidualProcess
          (mu := mu) H R M c X I o omega s -
        centeredAnchoredTruncationResidualProcess
          (mu := mu) H R M c X I o omega t| ≤
      centeredTruncationResidualCoefficient
        (mu := mu) R M c X I omega * dist s t := by
  rw [centeredAnchoredTruncationResidualProcess_sub
    H R hM X hX hH hRmeas hR hLip hRint I o omega s t, abs_mul]
  rw [centeredTruncationResidualCoefficient, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  have hsum := Finset.abs_sum_le_sum_abs (s := I)
    (f := fun i ↦
      truncationResidualIncrement H R M X i s t omega -
        ∫ xi, truncationResidualIncrement H R M X i s t xi ∂mu)
  calc
    |∑ i ∈ I,
        (truncationResidualIncrement H R M X i s t omega -
          ∫ xi, truncationResidualIncrement H R M X i s t xi ∂mu)| ≤
        ∑ i ∈ I,
          |truncationResidualIncrement H R M X i s t omega -
            ∫ xi, truncationResidualIncrement H R M X i s t xi ∂mu| := hsum
    _ ≤ ∑ i ∈ I,
        (truncationTailEnvelope R M (X i omega) +
          ∫ xi, truncationTailEnvelope R M (X i xi) ∂mu) * dist s t := by
      apply Finset.sum_le_sum
      intro i hi
      have htailInt := integrable_truncationTailEnvelope_comp
        R M hRmeas hR (X i) (hX i) (hRint i)
      have hintBound :
          |∫ xi, truncationResidualIncrement H R M X i s t xi ∂mu| ≤
            dist s t *
              ∫ xi, truncationTailEnvelope R M (X i xi) ∂mu := by
        have hnorm := norm_integral_le_of_norm_le
          (htailInt.const_mul (dist s t))
          (Filter.Eventually.of_forall fun xi ↦ by
            rw [Real.norm_eq_abs]
            calc
              |truncationResidualIncrement H R M X i s t xi| ≤
                  truncationTailEnvelope R M (X i xi) * dist s t :=
                abs_truncationResidualIncrement_le H R M hLip X i s t xi
              _ = dist s t * truncationTailEnvelope R M (X i xi) :=
                mul_comm _ _)
        rw [integral_const_mul] at hnorm
        simpa only [Real.norm_eq_abs] using hnorm
      calc
        |truncationResidualIncrement H R M X i s t omega -
            ∫ xi, truncationResidualIncrement H R M X i s t xi ∂mu| ≤
            |truncationResidualIncrement H R M X i s t omega| +
              |∫ xi, truncationResidualIncrement H R M X i s t xi ∂mu| :=
          abs_sub _ _
        _ ≤ truncationTailEnvelope R M (X i omega) * dist s t +
            dist s t *
              ∫ xi, truncationTailEnvelope R M (X i xi) ∂mu :=
          add_le_add
            (abs_truncationResidualIncrement_le H R M hLip X i s t omega)
            hintBound
        _ = (truncationTailEnvelope R M (X i omega) +
              ∫ xi, truncationTailEnvelope R M (X i xi) ∂mu) *
            dist s t := by ring
    _ = (∑ i ∈ I,
        (truncationTailEnvelope R M (X i omega) +
          ∫ xi, truncationTailEnvelope R M (X i xi) ∂mu)) * dist s t := by
      rw [Finset.sum_mul]
    _ = _ := by ring

omit [MeasurableSpace Omega] [MeasurableSpace Z] [PseudoMetricSpace T] in
/-- A tail above a positive threshold is bounded by the square divided by
that threshold.
@isnad1 id=le.2h4v.s6.7ee69d295929 from=translated src=- shape=9c13126d vocab=f5450c01
-/
theorem truncationTailEnvelope_le_inv_mul_sq
    (R : Z → ℝ) {M : ℝ} (hM : 0 < M) (hR : ∀ z, 0 ≤ R z) (z : Z) :
    truncationTailEnvelope R M z ≤ M⁻¹ * R z ^ 2 := by
  unfold truncationTailEnvelope
  split_ifs with hz
  · rw [le_inv_mul_iff₀ hM]
    calc
      M * R z ≤ R z * R z :=
        mul_le_mul (le_of_lt hz) le_rfl (hR z) (hR z)
      _ = R z ^ 2 := by ring
  · exact mul_nonneg (inv_nonneg.mpr hM.le) (sq_nonneg _)

omit [PseudoMetricSpace T] in
/-- Integral version of the square-over-threshold tail estimate.
@isnad1 id=le.5h6v.s7.ea5035f1893e from=translated src=- shape=b424cf2b vocab=85c93fa7
-/
theorem integral_truncationTailEnvelope_le_inv_mul_integral_sq
    [IsFiniteMeasure mu]
    (R : Z → ℝ) {M : ℝ} (hM : 0 < M)
    (hRmeas : Measurable R) (hR : ∀ z, 0 ≤ R z)
    (X : Omega → Z) (hX : Measurable X)
    (hRL2 : MemLp (fun omega ↦ R (X omega)) 2 mu) :
    ∫ omega, truncationTailEnvelope R M (X omega) ∂mu ≤
      M⁻¹ * ∫ omega, R (X omega) ^ 2 ∂mu := by
  have hRint : Integrable (fun omega ↦ R (X omega)) mu :=
    hRL2.integrable (by norm_num)
  have htailInt := integrable_truncationTailEnvelope_comp
    R M hRmeas hR X hX hRint
  have hsq : Integrable (fun omega ↦ R (X omega) ^ 2) mu :=
    (memLp_two_iff_integrable_sq hRL2.aestronglyMeasurable).1 hRL2
  have hright : Integrable (fun omega ↦ M⁻¹ * R (X omega) ^ 2) mu :=
    hsq.const_mul M⁻¹
  calc
    ∫ omega, truncationTailEnvelope R M (X omega) ∂mu ≤
        ∫ omega, M⁻¹ * R (X omega) ^ 2 ∂mu := by
      apply integral_mono htailInt hright
      intro omega
      exact truncationTailEnvelope_le_inv_mul_sq R hM hR (X omega)
    _ = M⁻¹ * ∫ omega, R (X omega) ^ 2 ∂mu := by
      rw [integral_const_mul]

/-- Empirical average of the squared Lipschitz envelopes.-/
def empiricalEnvelopeSquareAverage
    (R : Z → ℝ) (X : ℕ → Omega → Z) (n : ℕ) (omega : Omega) : ℝ :=
  (n + 1 : ℝ)⁻¹ *
    ∑ i ∈ Finset.range (n + 1), R (X i omega) ^ 2

omit [PseudoMetricSpace T] in
/--
@isnad1 id=measurab.2h5v.s5.0185363233d3 from=translated src=- shape=dfb2bbba vocab=0acd870e
-/
theorem measurable_empiricalEnvelopeSquareAverage
    (R : Z → ℝ) (hRmeas : Measurable R)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (empiricalEnvelopeSquareAverage R X n) := by
  unfold empiricalEnvelopeSquareAverage
  apply measurable_const.mul
  exact Finset.measurable_fun_sum (Finset.range (n + 1)) fun i _hi ↦
    ((hRmeas.comp (hX i)).pow_const 2)

omit [MeasurableSpace Omega] [MeasurableSpace Z] [PseudoMetricSpace T] in
/--
@isnad1 id=le.0h6v.s5.be74dc644b5a from=translated src=- shape=0e96c4ad vocab=2a444f06
-/
theorem empiricalEnvelopeSquareAverage_nonneg
    (R : Z → ℝ) (X : ℕ → Omega → Z) (n : ℕ) (omega : Omega) :
    0 ≤ empiricalEnvelopeSquareAverage R X n omega := by
  unfold empiricalEnvelopeSquareAverage
  positivity

omit [MeasurableSpace Z] [PseudoMetricSpace T] in
/-- The empirical squared-envelope average is integrable under `L²`.
@isnad1 id=integrab.1h6v.s6.194f6f4e2b2a from=translated src=- shape=f407b3d4 vocab=fe592d1a
-/
theorem integrable_empiricalEnvelopeSquareAverage
    (R : Z → ℝ) (X : ℕ → Omega → Z)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu) (n : ℕ) :
    Integrable (empiricalEnvelopeSquareAverage R X n) mu := by
  unfold empiricalEnvelopeSquareAverage
  apply Integrable.const_mul
  exact integrable_finsetSum (Finset.range (n + 1)) fun i _hi ↦
    (memLp_two_iff_integrable_sq (hRL2 i).aestronglyMeasurable).1 (hRL2 i)

omit [MeasurableSpace Z] [PseudoMetricSpace T] in
/-- The expected empirical squared-envelope average inherits the common
second-moment bound.
@isnad1 id=le.2h7v.s7.51468766ddbd from=translated src=- shape=8129da67 vocab=011628ae
-/
theorem integral_empiricalEnvelopeSquareAverage_le
    (R : Z → ℝ) (X : ℕ → Omega → Z) {K : ℝ}
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) :
    ∫ omega, empiricalEnvelopeSquareAverage R X n omega ∂mu ≤ K ^ 2 := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hsq : ∀ i ∈ Finset.range (n + 1),
      Integrable (fun omega ↦ R (X i omega) ^ 2) mu := fun i _hi ↦
    (memLp_two_iff_integrable_sq (hRL2 i).aestronglyMeasurable).1 (hRL2 i)
  unfold empiricalEnvelopeSquareAverage
  rw [integral_const_mul, MeasureTheory.integral_finsetSum _ hsq]
  calc
    (n + 1 : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1),
          ∫ omega, R (X i omega) ^ 2 ∂mu ≤
        (n + 1 : ℝ)⁻¹ *
          ∑ _i ∈ Finset.range (n + 1), K ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun i _hi ↦ hRsecond i
      · positivity
    _ = K ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      field_simp

omit [MeasurableSpace Z] [PseudoMetricSpace T] in
/-- Uniform Markov bound for the empirical squared-envelope average.
@isnad1 id=le.3h8v.s7.c33cd5fc84f7 from=translated src=- shape=b6f6af0a vocab=254e8043
-/
theorem measureReal_empiricalEnvelopeSquareAverage_gt_le
    [IsFiniteMeasure mu]
    (R : Z → ℝ) (X : ℕ → Omega → Z) {K C : ℝ} (hC : 0 < C)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) :
    mu.real {omega | C < empiricalEnvelopeSquareAverage R X n omega} ≤
      K ^ 2 / C := by
  let Q : Omega → ℝ := empiricalEnvelopeSquareAverage R X n
  have hQint : Integrable Q mu :=
    integrable_empiricalEnvelopeSquareAverage R X hRL2 n
  have hQnonneg : ∀ omega, 0 ≤ Q omega :=
    empiricalEnvelopeSquareAverage_nonneg R X n
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hQnonneg) hQint C
  have hmono :
      mu.real {omega | C < Q omega} ≤ mu.real {omega | C ≤ Q omega} :=
    measureReal_mono (fun _omega homega ↦ by
      simpa only [Set.mem_ofPred_eq] using homega.le)
  rw [le_div_iff₀ hC]
  calc
    mu.real {omega | C < Q omega} * C =
        C * mu.real {omega | C < Q omega} := by ring
    _ ≤ C * mu.real {omega | C ≤ Q omega} :=
      mul_le_mul_of_nonneg_left hmono hC.le
    _ ≤ ∫ omega, Q omega ∂mu := hmarkov
    _ ≤ K ^ 2 := integral_empiricalEnvelopeSquareAverage_le
      R X hRL2 hRsecond n

omit [PseudoMetricSpace T] in
/-- At the natural square-root truncation level, the remainder coefficient is
bounded by the empirical second moment plus its deterministic expectation
bound.
@isnad1 id=le.5h8v.s8.4b8469d86e37 from=translated src=- shape=f5f2c0de vocab=6c3f3a13
-/
theorem centeredTruncationResidualCoefficient_sqrt_le
    [IsProbabilityMeasure mu]
    (R : Z → ℝ) (hRmeas : Measurable R) (hR : ∀ z, 0 ≤ R z)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i)) {K : ℝ}
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) (omega : Omega) :
    centeredTruncationResidualCoefficient (mu := mu) R
        (Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) omega ≤
      empiricalEnvelopeSquareAverage R X n omega + K ^ 2 := by
  let q : ℝ := Real.sqrt (n + 1 : ℝ)
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hq : 0 < q := Real.sqrt_pos.2 hn
  have hqSq : q ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt hn.le
  have hqInv : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  have hqInvSq : q⁻¹ * q⁻¹ = (n + 1 : ℝ)⁻¹ := by
    calc
      q⁻¹ * q⁻¹ = (q * q)⁻¹ := (mul_inv q q).symm
      _ = (q ^ 2)⁻¹ := by rw [pow_two]
      _ = (n + 1 : ℝ)⁻¹ := by rw [hqSq]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      truncationTailEnvelope R q (X i omega) +
          ∫ xi, truncationTailEnvelope R q (X i xi) ∂mu ≤
        q⁻¹ * R (X i omega) ^ 2 +
          q⁻¹ * ∫ xi, R (X i xi) ^ 2 ∂mu := by
    intro i hi
    exact add_le_add
      (truncationTailEnvelope_le_inv_mul_sq R hq hR (X i omega))
      (integral_truncationTailEnvelope_le_inv_mul_integral_sq
        R hq hRmeas hR (X i) (hX i) (hRL2 i))
  change centeredTruncationResidualCoefficient (mu := mu) R q q⁻¹ X
      (Finset.range (n + 1)) omega ≤ _
  rw [centeredTruncationResidualCoefficient, abs_of_pos (inv_pos.mpr hq)]
  calc
    q⁻¹ * ∑ i ∈ Finset.range (n + 1),
        (truncationTailEnvelope R q (X i omega) +
          ∫ xi, truncationTailEnvelope R q (X i xi) ∂mu) ≤
        q⁻¹ * ∑ i ∈ Finset.range (n + 1),
          (q⁻¹ * R (X i omega) ^ 2 +
            q⁻¹ * ∫ xi, R (X i xi) ^ 2 ∂mu) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hqInv
    _ = empiricalEnvelopeSquareAverage R X n omega +
        (n + 1 : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1),
          ∫ xi, R (X i xi) ^ 2 ∂mu := by
      unfold empiricalEnvelopeSquareAverage
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      calc
        q⁻¹ *
            (q⁻¹ * ∑ x ∈ Finset.range (n + 1), R (X x omega) ^ 2 +
              q⁻¹ * ∑ x ∈ Finset.range (n + 1),
                ∫ xi, R (X x xi) ^ 2 ∂mu) =
            (q⁻¹ * q⁻¹) *
                ∑ x ∈ Finset.range (n + 1), R (X x omega) ^ 2 +
              (q⁻¹ * q⁻¹) * ∑ x ∈ Finset.range (n + 1),
                ∫ xi, R (X x xi) ^ 2 ∂mu := by ring
        _ = _ := by rw [hqInvSq]
    _ ≤ empiricalEnvelopeSquareAverage R X n omega +
        (n + 1 : ℝ)⁻¹ *
          ∑ _i ∈ Finset.range (n + 1), K ^ 2 := by
      gcongr with i hi
      exact hRsecond i
    _ = empiricalEnvelopeSquareAverage R X n omega + K ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      field_simp

omit [MeasurableSpace Z] [PseudoMetricSpace T] in
/--
@isnad1 id=eq.0h13v.s6.fac24b30e416 from=translated src=- shape=058dc9f4 vocab=f0588eec
-/
@[simp]
theorem centeredAnchoredTruncationResidualProcess_anchor
    (H : Z → T → ℝ) (R : Z → ℝ) (M c : ℝ)
    (X : iota → Omega → Z) (I : Finset iota) (o : T) (omega : Omega) :
    centeredAnchoredTruncationResidualProcess
      (mu := mu) H R M c X I o omega o = 0 := by
  simp [centeredAnchoredTruncationResidualProcess,
    truncationResidualIncrement, lipschitzIncrement,
    truncatedLipschitzIncrement]

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The original centered empirical process bundled as a continuous path on
the Euclidean unit ball.-/
def centeredAnchoredEmpiricalContinuousMap
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z))
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (n : ℕ) (omega : Omega) : C(EuclideanUnitBall E, ℝ) where
  toFun t := centeredAnchoredEmpiricalProcess (mu := mu) H
    (Real.sqrt (n + 1 : ℝ))⁻¹ X (Finset.range (n + 1)) 0 omega (t : E)
  continuous_toFun :=
    (continuous_centeredAnchoredEmpiricalProcess H R
      (Real.sqrt (n + 1 : ℝ))⁻¹ X hX hHmeas hHcont hR hLip
      (fun i ↦ (hRL2 i).integrable (by norm_num))
      (Finset.range (n + 1)) 0 omega).comp continuous_subtype_val

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.6h10v.s8.e805ff8ab7e8 from=translated src=- shape=53c9f6c0 vocab=7e4cf5ff
-/
@[simp]
theorem centeredAnchoredEmpiricalContinuousMap_apply
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z))
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (n : ℕ) (omega : Omega) (t : EuclideanUnitBall E) :
    centeredAnchoredEmpiricalContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hR hLip hRL2 n omega t =
      centeredAnchoredEmpiricalProcess (mu := mu) H
        (Real.sqrt (n + 1 : ℝ))⁻¹ X (Finset.range (n + 1)) 0 omega (t : E) :=
  rfl

/-- The continuous path formed by the difference between the original
process and its square-root truncation.-/
def centeredTruncationResidualContinuousMap
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (n : ℕ) (omega : Omega) : C(EuclideanUnitBall E, ℝ) :=
  centeredAnchoredEmpiricalContinuousMap (mu := mu)
      H R X hX hHmeas hHcont hR hLip hRL2 n omega -
    centeredTruncatedEmpiricalContinuousMap (mu := mu)
      H R (a := 1) (by norm_num) X hX hHmeas hHcont hRmeas hR hLip n omega

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/--
@isnad1 id=eq.7h10v.s8.5686fa1ec63a from=translated src=- shape=a235afc2 vocab=241eef7d
-/
@[simp]
theorem centeredTruncationResidualContinuousMap_apply
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (n : ℕ) (omega : Omega) (t : EuclideanUnitBall E) :
    centeredTruncationResidualContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega t =
      centeredAnchoredTruncationResidualProcess (mu := mu) H R
        (Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) 0 omega (t : E) := by
  change centeredAnchoredEmpiricalProcess (mu := mu) H
        (Real.sqrt (n + 1 : ℝ))⁻¹ X (Finset.range (n + 1)) 0 omega (t : E) -
      centeredAnchoredTruncatedEmpiricalProcess (mu := mu) H R
        (1 * Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
        (Finset.range (n + 1)) 0 omega (t : E) = _
  simpa only [one_mul] using centeredAnchoredEmpiricalProcess_sub_truncated
    (mu := mu) H R (Real.sqrt_nonneg _) X hX hHmeas hRmeas hR hLip
      (fun i ↦ (hRL2 i).integrable (by norm_num))
      (Finset.range (n + 1)) 0 omega (t : E)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The original path is the sum of its truncated and residual parts.
@isnad1 id=eq.7h9v.s9.e7eb9383ce03 from=translated src=- shape=53dc1232 vocab=3f83876d
-/
theorem centeredTruncated_add_residual_eq_centeredAnchored
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (n : ℕ) (omega : Omega) :
    centeredTruncatedEmpiricalContinuousMap (mu := mu)
          H R (a := 1) (by norm_num) X hX hHmeas hHcont hRmeas hR hLip n omega +
        centeredTruncationResidualContinuousMap (mu := mu)
          H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega =
      centeredAnchoredEmpiricalContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hR hLip hRL2 n omega := by
  unfold centeredTruncationResidualContinuousMap
  abel

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Pathwise Lipschitz estimate for the square-root truncation remainder.
@isnad1 id=le.8h12v.s9.ada8ff0d8eba from=translated src=- shape=fbcbe80d vocab=f41dfb49
-/
theorem dist_centeredTruncationResidualContinuousMap_le
    [IsProbabilityMeasure mu]
    (H : Z → E → ℝ) (R : Z → ℝ)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    {K : ℝ}
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) (omega : Omega) (s t : EuclideanUnitBall E) :
    dist
        (centeredTruncationResidualContinuousMap (mu := mu)
          H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega s)
        (centeredTruncationResidualContinuousMap (mu := mu)
          H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega t) ≤
      (empiricalEnvelopeSquareAverage R X n omega + K ^ 2) * dist s t := by
  rw [Real.dist_eq]
  simp only [centeredTruncationResidualContinuousMap_apply]
  calc
    |centeredAnchoredTruncationResidualProcess (mu := mu) H R
          (Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
          (Finset.range (n + 1)) 0 omega (s : E) -
        centeredAnchoredTruncationResidualProcess (mu := mu) H R
          (Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
          (Finset.range (n + 1)) 0 omega (t : E)| ≤
        centeredTruncationResidualCoefficient (mu := mu) R
            (Real.sqrt (n + 1 : ℝ)) (Real.sqrt (n + 1 : ℝ))⁻¹ X
            (Finset.range (n + 1)) omega * dist (s : E) (t : E) :=
      abs_centeredAnchoredTruncationResidualProcess_sub_le
        H R (Real.sqrt_nonneg _) X hX hHmeas hRmeas hR hLip
          (fun i ↦ (hRL2 i).integrable (by norm_num))
          (Finset.range (n + 1)) 0 omega (s : E) (t : E)
    _ ≤ (empiricalEnvelopeSquareAverage R X n omega + K ^ 2) *
        dist (s : E) (t : E) :=
      mul_le_mul_of_nonneg_right
        (centeredTruncationResidualCoefficient_sqrt_le
          R hRmeas hR X hX hRL2 hRsecond n omega) dist_nonneg
    _ = _ := by rw [Subtype.dist_eq]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The sup norm of the remainder on the unit ball is controlled by the same
random Lipschitz coefficient.
@isnad1 id=le.8h10v.s8.ae7d2cd07ae7 from=translated src=- shape=262f113d vocab=b0206c63
-/
theorem norm_centeredTruncationResidualContinuousMap_le
    [IsProbabilityMeasure mu]
    [CompactSpace (EuclideanUnitBall E)]
    (H : Z → E → ℝ) (R : Z → ℝ)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    {K : ℝ}
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (n : ℕ) (omega : Omega) :
    ‖centeredTruncationResidualContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega‖ ≤
      empiricalEnvelopeSquareAverage R X n omega + K ^ 2 := by
  let D := empiricalEnvelopeSquareAverage R X n omega + K ^ 2
  have hD : 0 ≤ D := add_nonneg
    (empiricalEnvelopeSquareAverage_nonneg R X n omega) (sq_nonneg K)
  let z0 : EuclideanUnitBall E := ⟨0, by simp⟩
  have hz0 : centeredTruncationResidualContinuousMap (mu := mu)
      H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega z0 = 0 := by
    simp only [centeredTruncationResidualContinuousMap_apply]
    exact centeredAnchoredTruncationResidualProcess_anchor
      H R _ _ X (Finset.range (n + 1)) 0 omega
  rw [ContinuousMap.norm_le _ hD]
  intro t
  have hlip := dist_centeredTruncationResidualContinuousMap_le
    H R X hX hHmeas hHcont hRmeas hR hLip hRL2 hRsecond n omega t z0
  have htz : dist t z0 ≤ 1 := by
    simpa only [z0, Subtype.dist_eq, dist_zero_right] using t.property
  calc
    ‖centeredTruncationResidualContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega t‖ =
        dist
          (centeredTruncationResidualContinuousMap (mu := mu)
            H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega t)
          (centeredTruncationResidualContinuousMap (mu := mu)
            H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega z0) := by
      rw [hz0, dist_zero_right]
    _ ≤ D * dist t z0 := hlip
    _ ≤ D * 1 := mul_le_mul_of_nonneg_left htz hD
    _ = D := mul_one D

/-- Uniform tightness of the square-root truncation remainders.
@isnad1 id=istightm.10h8v.s9.f90cd1fc0e66 from=translated src=- shape=c3101646 vocab=9e28973c
-/
theorem isTightMeasureSet_range_centeredTruncationResidualContinuousMap
    [IsProbabilityMeasure mu]
    [MeasurableSpace C(EuclideanUnitBall E, ℝ)]
    [BorelSpace C(EuclideanUnitBall E, ℝ)]
    (H : Z → E → ℝ) (R : Z → ℝ) {K : ℝ} (hK : 0 < K)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (hpathMeas : ∀ n, AEMeasurable
      (centeredTruncationResidualContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n) mu) :
    IsTightMeasureSet (Set.range fun n ↦ mu.map
      (centeredTruncationResidualContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n)) := by
  letI : CompactSpace (EuclideanUnitBall E) :=
    isCompact_iff_compactSpace.mp (by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact isClosed_le continuous_norm continuous_const
      · exact (isBounded_iff_forall_norm_le.mpr
          ⟨1, fun _v hv ↦ hv⟩))
  let Y : ℕ → Omega → C(EuclideanUnitBall E, ℝ) := fun n ↦
    centeredTruncationResidualContinuousMap (mu := mu)
      H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n
  let delta : ℕ → ℝ := RandomSetTheory.dyadicResolution
  apply isTightMeasureSet_range_map_of_real_compactContainment
    mu Y hpathMeas delta RandomSetTheory.dyadicResolution_pos
  intro epsilon hepsilon
  let C : ℝ := K ^ 2 / epsilon
  have hKsq : 0 < K ^ 2 := sq_pos_of_pos hK
  have hC : 0 < C := div_pos hKsq hepsilon
  let D : ℝ := C + K ^ 2
  have hD : 0 ≤ D := add_nonneg hC.le (sq_nonneg K)
  let eta : ℕ → ℝ := fun k ↦ D * delta k
  have hdeltaSummable : Summable delta := by
    change Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k)
    exact summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have heta : Tendsto eta atTop (nhds 0) := by
    exact (hdeltaSummable.mul_left D).tendsto_atTop_zero
  refine ⟨D, hD, eta, heta, ?_⟩
  intro n
  have hsubset :
      {omega | D < ‖Y n omega‖ ∨
        ∃ k s t, dist s t < delta k ∧
          eta k < dist (Y n omega s) (Y n omega t)} ⊆
        {omega | C < empiricalEnvelopeSquareAverage R X n omega} := by
    intro omega hbad
    by_contra hnot
    have hQle : empiricalEnvelopeSquareAverage R X n omega ≤ C :=
      le_of_not_gt hnot
    have hnorm : ‖Y n omega‖ ≤ D := by
      calc
        ‖Y n omega‖ ≤ empiricalEnvelopeSquareAverage R X n omega + K ^ 2 :=
          norm_centeredTruncationResidualContinuousMap_le
            H R X hX hHmeas hHcont hRmeas hR hLip hRL2
              hRsecond n omega
        _ ≤ D := by
          simpa only [D, add_comm] using add_le_add_right hQle (K ^ 2)
    rcases hbad with hnormBad | ⟨k, s, t, hst, hmodBad⟩
    · exact (not_lt_of_ge hnorm) hnormBad
    · have hlip := dist_centeredTruncationResidualContinuousMap_le
        H R X hX hHmeas hHcont hRmeas hR hLip hRL2
          hRsecond n omega s t
      have hcoeff :
          empiricalEnvelopeSquareAverage R X n omega + K ^ 2 ≤ D :=
        by simpa only [D, add_comm] using add_le_add_right hQle (K ^ 2)
      have hdist : dist (Y n omega s) (Y n omega t) ≤ eta k := by
        calc
          dist (Y n omega s) (Y n omega t) ≤
              (empiricalEnvelopeSquareAverage R X n omega + K ^ 2) *
                dist s t := hlip
          _ ≤ D * dist s t :=
            mul_le_mul_of_nonneg_right hcoeff dist_nonneg
          _ ≤ D * delta k := mul_le_mul_of_nonneg_left hst.le hD
          _ = eta k := rfl
      exact (not_lt_of_ge hdist) hmodBad
  have hmarkov := measureReal_empiricalEnvelopeSquareAverage_gt_le
    R X hC hRL2 hRsecond n
  calc
    mu.real {omega | D < ‖Y n omega‖ ∨
        ∃ k s t, dist s t < delta k ∧
          eta k < dist (Y n omega s) (Y n omega t)} ≤
        mu.real {omega | C < empiricalEnvelopeSquareAverage R X n omega} :=
      measureReal_mono hsubset
    _ ≤ K ^ 2 / C := hmarkov
    _ = epsilon := by
      dsimp only [C]
      field_simp

/-- Uniform tightness of the original, untruncated centered empirical
process.  The proof combines the already established tightness of the
square-root truncation with tightness of the `L²` remainder and then applies
continuous addition on path space.
@isnad1 id=istightm.12h8v.s9.ac706de3999d from=translated src=- shape=969122bd vocab=bc8082f5
-/
theorem isTightMeasureSet_range_centeredAnchoredEmpiricalContinuousMap
    [IsProbabilityMeasure mu]
    [MeasurableSpace C(EuclideanUnitBall E, ℝ)]
    [BorelSpace C(EuclideanUnitBall E, ℝ)]
    (H : Z → E → ℝ) (R : Z → ℝ) {K : ℝ} (hK : 0 < K)
    (X : ℕ → Omega → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X mu)
    (hHmeas : ∀ t, Measurable (fun z ↦ H z t))
    (hHcont : ∀ z, Continuous (H z)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun omega ↦ R (X i omega)) 2 mu)
    (hRsecond : ∀ i, ∫ omega, R (X i omega) ^ 2 ∂mu ≤ K ^ 2)
    (hRawPathMeas : ∀ n, AEMeasurable
      (centeredAnchoredEmpiricalContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hR hLip hRL2 n) mu)
    (hTruncatedPathMeas : ∀ n, AEMeasurable
      (centeredTruncatedEmpiricalContinuousMap (mu := mu)
        H R (a := 1) (by norm_num) X hX hHmeas hHcont hRmeas hR hLip n) mu) :
    IsTightMeasureSet (Set.range fun n ↦ mu.map
      (centeredAnchoredEmpiricalContinuousMap (mu := mu)
        H R X hX hHmeas hHcont hR hLip hRL2 n)) := by
  letI : CompactSpace (EuclideanUnitBall E) :=
    isCompact_iff_compactSpace.mp (by
      apply Metric.isCompact_of_isClosed_isBounded
      · exact isClosed_le continuous_norm continuous_const
      · exact (isBounded_iff_forall_norm_le.mpr
          ⟨1, fun _v hv ↦ hv⟩))
  let Path := C(EuclideanUnitBall E, ℝ)
  let Yraw : ℕ → Omega → Path := fun n ↦
    centeredAnchoredEmpiricalContinuousMap (mu := mu)
      H R X hX hHmeas hHcont hR hLip hRL2 n
  let Ytr : ℕ → Omega → Path := fun n ↦
    centeredTruncatedEmpiricalContinuousMap (mu := mu)
      H R (a := 1) (by norm_num) X hX hHmeas hHcont hRmeas hR hLip n
  let Yres : ℕ → Omega → Path := fun n ↦
    centeredTruncationResidualContinuousMap (mu := mu)
      H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n
  have hresPathMeas : ∀ n, AEMeasurable (Yres n) mu := by
    intro n
    change AEMeasurable (fun omega ↦ Yraw n omega - Ytr n omega) mu
    exact (continuous_sub.measurable.comp_aemeasurable
      ((hRawPathMeas n).prodMk (hTruncatedPathMeas n)))
  have htightTr : IsTightMeasureSet
      (Set.range fun n ↦ mu.map (Ytr n)) := by
    simpa only [Ytr] using
      isTightMeasureSet_range_centeredTruncatedEmpiricalContinuousMap
        H R (a := 1) (K := K) (by norm_num) hK X hX hIndep
          hHmeas hHcont hRmeas hR hLip hRL2 hRsecond hTruncatedPathMeas
  have htightRes : IsTightMeasureSet
      (Set.range fun n ↦ mu.map (Yres n)) := by
    simpa only [Yres] using
      isTightMeasureSet_range_centeredTruncationResidualContinuousMap
        H R hK X hX hHmeas hHcont hRmeas hR hLip hRL2 hRsecond
          hresPathMeas
  let jointLaws : Set (Measure (Path × Path)) :=
    Set.range fun n ↦ mu.map (fun omega ↦ (Ytr n omega, Yres n omega))
  have htightFst : IsTightMeasureSet (Measure.fst '' jointLaws) := by
    apply htightTr.subset
    rintro m ⟨rho, ⟨n, rfl⟩, rfl⟩
    rw [Measure.fst_map_prodMk₀ (hresPathMeas n)]
    exact Set.mem_range_self n
  have htightSnd : IsTightMeasureSet (Measure.snd '' jointLaws) := by
    apply htightRes.subset
    rintro m ⟨rho, ⟨n, rfl⟩, rfl⟩
    rw [Measure.snd_map_prodMk₀ (hTruncatedPathMeas n)]
    exact Set.mem_range_self n
  have htightJoint : IsTightMeasureSet jointLaws :=
    htightFst.prodMk htightSnd
  let addPaths : Path × Path → Path := fun p ↦ p.1 + p.2
  have haddContinuous : Continuous addPaths := continuous_add
  have htightAdd : IsTightMeasureSet (Measure.map addPaths '' jointLaws) :=
    htightJoint.map haddContinuous
  apply htightAdd.subset
  rintro m ⟨n, rfl⟩
  refine ⟨mu.map (fun omega ↦ (Ytr n omega, Yres n omega)),
    Set.mem_range_self n, ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable
    haddContinuous.measurable.aemeasurable
    ((hTruncatedPathMeas n).prodMk (hresPathMeas n))]
  congr 1
  funext omega
  change Ytr n omega + Yres n omega = Yraw n omega
  exact centeredTruncated_add_residual_eq_centeredAnchored
    H R X hX hHmeas hHcont hRmeas hR hLip hRL2 n omega

end Euclidean

end ProbabilityTheory
