/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.CellLaws
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.Superposition.Retention
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Poisson.FinitePartition.KL
public import Tengoku.Causalean.Causalean.Mathlib.InformationTheory.KLBind
public import Tengoku

/-!
# Finite-sample maps and de-Poissonization

This file provides measurable maps between dependent finite samples, padded
streams, and canonical marked configurations. It also records the Poisson
count identity and a reusable exponential lower-tail bound used to transfer
random-size experiments to fixed sample sizes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Given [a map between observation spaces](hyp:f) and [a finite sample](hyp:s), the
[mapped finite sample](goal) has the same size and applies the map to every observation. -/
def finiteSampleMap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (s : FiniteSample X) : FiniteSample Y :=
  ⟨s.count, fun i => f (s.points i)⟩

/-- If [a map between observation spaces](hyp:f) [is measurable](hyp:hf),
[pointwise finite-sample mapping is measurable](goal). -/
@[fun_prop]
lemma measurable_finiteSampleMap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) :
    Measurable (finiteSampleMap f : FiniteSample X → FiniteSample Y) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs ⊢
  intro n
  let g : (Fin n → X) → (Fin n → Y) := fun x i => f (x i)
  have hg : Measurable g :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  have hsn := hs n
  change MeasurableSet (fixedSizeEmbed n ⁻¹' s) at hsn
  change MeasurableSet ((fun x : Fin n → X =>
    ⟨n, fun i => f (x i)⟩) ⁻¹' s)
  exact hsn.preimage hg

/-- For [a map between observation spaces](hyp:f), [a sample size](hyp:n), and
[a tuple of that size](hyp:x),
[mapping commutes with fixed-size embedding](goal). -/
lemma finiteSampleMap_fixedSizeEmbed {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (f : X → Y) (n : ℕ) (x : Fin n → X) :
    finiteSampleMap f (fixedSizeEmbed n x) =
      fixedSizeEmbed n (fun i => f (x i)) := rfl

/-- Given [a fallback observation](hyp:x₀), [a prefix length](hyp:n), and
[a finite sample of observation--mark pairs](hyp:s), the [canonical prefix](goal) consists of
the first `n` observations when available and otherwise repeats the fallback `n` times. -/
def canonicalPrefixObservations {X : Type*} [MeasurableSpace X]
    (x₀ : X) (n : ℕ) (s : FiniteSample (X × ℝ)) : Fin n → X :=
  if h : n ≤ s.count then fun k => (s.points (Fin.castLE h k)).1
  else fun _ => x₀

/-- For [a fallback observation](hyp:x₀) and [a prefix length](hyp:n),
[reading the canonical prefix is measurable](goal). -/
@[fun_prop]
lemma measurable_canonicalPrefixObservations {X : Type*} [MeasurableSpace X]
    (x₀ : X) (n : ℕ) :
    Measurable (canonicalPrefixObservations x₀ n :
      FiniteSample (X × ℝ) → Fin n → X) := by
  unfold canonicalPrefixObservations
  apply measurable_pi_lambda
  intro k t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((fun x : Fin m → X × ℝ =>
    (if h : n ≤ m then fun k => (x (Fin.castLE h k)).1 else fun _ => x₀) k) ⁻¹' t)
  by_cases h : n ≤ m
  · simp only [dite_eq_left h]
    exact ht.preimage ((measurable_pi_apply (Fin.castLE h k)).fst)
  · simp only [dite_eq_right h]
    exact measurable_const ht

/-- For [a target sample size](hyp:n),
[the corresponding doubled-mean Poisson lower tail has the stated exponential bound](goal). -/
lemma poisson_two_n_lower_tail (n : ℕ) :
    (poissonMeasure (2 * n)) {k | k < n} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
  rw [show {k : ℕ | k < n} = (↑(Finset.range n) : Set ℕ) by ext k; simp]
  rw [← MeasureTheory.sum_measure_singleton]
  simp_rw [poissonMeasure_singleton_eq_poissonPMF]
  have hterm : ∀ k ∈ Finset.range n,
      poissonMeasure (2 * n) k ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) * poissonMeasure n k := by
    intro k hk
    have hreal : poissonMeasure (2 * (n : ℝ≥0)) k ≤
        Real.exp (-(n : ℝ) * (1 - Real.log 2)) *
          poissonMeasure (n : ℝ≥0) k := by
      unfold poissonMeasure
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < k.factorial)).2
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hpow : (2 : ℝ) ^ k ≤ 2 ^ n :=
        pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hk).le
      have htarget : Real.exp (-(n : ℝ) * (1 - Real.log 2)) =
          Real.exp (-(n : ℝ)) * (2 : ℝ) ^ n := by
        rw [show -(n : ℝ) * (1 - Real.log 2) =
            -(n : ℝ) + Real.log 2 * n by ring,
          Real.exp_add, show Real.log 2 * (n : ℝ) = (n : ℝ) * Real.log 2 by ring,
          Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hexp2 : Real.exp (-((2 : ℝ) * (n : ℝ))) =
          Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      norm_num only [NNReal.smul_def, NNReal.coe_natCast, NNReal.coe_mul, Nat.cast_ofNat]
      rw [mul_pow, htarget]
      change Real.exp (-(2 * (n : ℝ))) * ((2 : ℝ) ^ k * (n : ℝ) ^ k) ≤ _
      rw [hexp2]
      calc
        Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) *
              ((2 : ℝ) ^ k * (n : ℝ) ^ k) =
            (Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) * (n : ℝ) ^ k) * 2 ^ k := by
              ring
        _ ≤ (Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) * (n : ℝ) ^ k) * 2 ^ n :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = Real.exp (-(n : ℝ)) * 2 ^ n *
            (Real.exp (-(n : ℝ)) * (n : ℝ) ^ k) := by ring
    unfold poissonMeasure
    change ENNReal.ofReal (poissonMeasure (2 * n) k) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) *
        ENNReal.ofReal (poissonMeasure n k)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    ∑ k ∈ Finset.range n, poissonMeasure (2 * n) k
        ≤ ∑ k ∈ Finset.range n,
            ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) * poissonMeasure n k :=
      Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) *
          ∑ k ∈ Finset.range n, poissonMeasure n k := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) * 1 := by
      gcongr
      exact ((poissonMeasure n).property.summable.sum_le_tsum _ (fun _ _ => bot_le)).trans_eq
        (poissonMeasure n).property.tsum_eq
    _ = _ := mul_one _

/-- Given [a fallback observation](hyp:x0) and [a finite sample](hyp:s), its
[padded stream representation](goal) records the sample size, then agrees with its observations
below that size and equals the fallback thereafter. -/
def finiteSamplePaddedStream {X : Type*} [MeasurableSpace X]
    (x0 : X) (s : FiniteSample X) : ℕ × (ℕ → X) :=
  (s.count, fun k => if h : k < s.count then s.points ⟨k, h⟩ else x0)

/-- Given [a fallback observation](hyp:x0),
[mapping a finite sample to its padded stream is measurable](goal). -/
@[fun_prop]
lemma finiteSamplePaddedStream_measurable {X : Type*} [MeasurableSpace X]
    (x0 : X) : Measurable (finiteSamplePaddedStream x0) := by
  intro t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((fun s : Fin n → X =>
    finiteSamplePaddedStream x0 ⟨n, s⟩) ⁻¹' t)
  apply ht.preimage
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro k
  by_cases hk : k < n
  · let i : Fin n := ⟨k, hk⟩
    simpa [finiteSamplePaddedStream, FiniteSample.count, FiniteSample.points, hk, i]
      using (measurable_pi_apply i : Measurable (fun s : Fin n → X => s i))
  · simp [finiteSamplePaddedStream, FiniteSample.count, hk]

/-- Given [a fallback observation](hyp:x0) and [a finite sample](hyp:s),
[converting its padded stream back recovers the sample](goal). -/
lemma streamToFiniteSample_paddedStream {X : Type*} [MeasurableSpace X]
    (x0 : X) (s : FiniteSample X) :
    streamToFiniteSample (finiteSamplePaddedStream x0 s) = s := by
  cases s with
  | mk n s =>
      change (⟨n, fun k => if h : k < n then s ⟨k, h⟩ else x0⟩ :
        Σ n : ℕ, Fin n → X) = ⟨n, s⟩
      congr
      funext k
      simp

/-- Given [a fallback observation](hyp:x0),
[the padded-stream range consists exactly of streams equal to it beyond their size](goal). -/
lemma finiteSamplePaddedStream_range {X : Type*} [MeasurableSpace X]
    (x0 : X) :
    Set.range (finiteSamplePaddedStream x0) =
      {z : ℕ × (ℕ → X) | ∀ k, z.1 ≤ k → z.2 k = x0} := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩ k hk
    have hnot : ¬k < s.count := Nat.not_lt_of_ge hk
    simp [finiteSamplePaddedStream, hnot]
  · intro hz
    refine ⟨streamToFiniteSample z, ?_⟩
    apply Prod.ext
    · rfl
    · funext k
      by_cases hk : k < z.1
      · simp [finiteSamplePaddedStream, FiniteSample.count,
          FiniteSample.points, streamToFiniteSample, hk]
      · simp [finiteSamplePaddedStream, FiniteSample.count,
          FiniteSample.points, streamToFiniteSample, hk, hz k (Nat.le_of_not_gt hk)]

/-- Given [a base probability law](hyp:P), [a mark probability law](hyp:R), and
[a nonnegative intensity](hyp:lam),
[the canonical marked-Poisson sample has a Poisson count with that intensity](goal). -/
lemma canonicalMarkedPoissonSampleLaw_map_count
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure.map FiniteSample.count
        (canonicalMarkedPoissonSampleLaw P R lam) = poissonMeasure lam := by
  unfold canonicalMarkedPoissonSampleLaw
  rw [Measure.map_map measurable_finiteSample_count measurable_orderByMarks]
  simpa only [Function.comp_def, orderByMarks_count] using
    finiteMarkedPoissonSampleLaw_map_count P R lam

/-- For [an intensity measure that is already a probability law](hyp:P),
[a fallback probability law](hyp:P0), [a real-valued mark law](hyp:R), and
[a nonnegative intensity](hyp:lam),
[the finite-measure wrapper equals the ordinary marked Poisson sample law](goal). -/
theorem finiteMeasureMarkedPoissonLaw_probability_eq
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    finiteMeasureMarkedPoissonLaw P P0 R lam =
      finiteMarkedPoissonSampleLaw P R lam := by
  have hP : P ≠ 0 := by
    intro h
    have : P Set.univ = 1 := by simp
    simp [h] at this
  have hnorm : normalizedFiniteMeasure P P0 = P := by
    unfold normalizedFiniteMeasure
    rw [dite_eq_right hP]
    simp
  have hmass : finiteMeasureMass P = 1 := by
    unfold finiteMeasureMass
    simp
  unfold finiteMeasureMarkedPoissonLaw
  rw [hmass, mul_one]
  congr 2

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
