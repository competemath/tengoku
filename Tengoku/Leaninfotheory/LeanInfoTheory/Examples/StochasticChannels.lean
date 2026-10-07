/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.EntropyBounds
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.DataProcessing

/-!
# Genuinely stochastic finite channels

This opt-in module exercises one-step entropy growth and KL contraction on
channels that are not deterministic relabelings. It also records a cascade in
which source support inclusion fails but intermediate support inclusion holds.
-/

namespace LeanInfoTheory
namespace Examples
namespace StochasticChannels

open Shannon

noncomputable section

local instance : MeasurableSpace Bool := ⊤

local instance : MeasurableSingletonClass Bool where
  measurableSet_singleton _ := trivial

/-- A non-permutation channel that replaces every input by a fair bit. -/
def averagingChannel (_ : Bool) : PMF Bool := PMF.uniformOfFintype Bool

private theorem bind_averagingChannel (p : PMF Bool) :
    p.bind averagingChannel = PMF.uniformOfFintype Bool := by
  change p.bind (fun _ => PMF.uniformOfFintype Bool) =
    PMF.uniformOfFintype Bool
  exact PMF.bind_const _ _

private theorem averagingChannel_column_sum (b : Bool) :
    ∑ a, averagingChannel a b = 1 := by
  classical
  rw [Fintype.sum_bool]
  simp only [averagingChannel, PMF.uniformOfFintype_apply,
    Fintype.card_bool]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Uniform invariance proves entropy growth for the averaging channel. -/
theorem entropy_le_after_averaging_via_invariant (p : PMF Bool) :
    entropy p ≤ entropy (p.bind averagingChannel) :=
  entropy_le_entropy_bind_of_uniform_invariant p averagingChannel (by
    exact bind_averagingChannel (PMF.uniformOfFintype Bool))

/-- The direct column-sum criterion proves the same entropy comparison. -/
theorem entropy_le_after_averaging_via_columns (p : PMF Bool) :
    entropy p ≤ entropy (p.bind averagingChannel) :=
  entropy_le_entropy_bind_of_doublyStochastic p averagingChannel
    averagingChannel_column_sum

/-- Averaging strictly raises the entropy of a pure binary input. -/
theorem entropy_strictly_increases_from_pure :
    entropy (PMF.pure false) <
      entropy ((PMF.pure false).bind averagingChannel) := by
  rw [bind_averagingChannel, entropy_pure, entropy_uniformOfFintype]
  exact Real.log_pos (by norm_num)

/-- A full-support nonuniform reference law. -/
def biasedLaw : PMF Bool :=
  PMF.ofFintype
    (fun b : Bool =>
      ((cond b (3 / 4 : NNReal) (1 - (3 / 4 : NNReal)) : NNReal) : ENNReal))
    (by
      have h : (3 / 4 : NNReal) <= 1 := by
        change (3 / 4 : Real) <= 1
        norm_num
      rw [Fintype.sum_bool]
      simp only [Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add]
      rw [add_tsub_cancel_of_le h]
      rfl)

/-- A channel that resets every input to the nonuniform reference law. -/
def biasedReset (_ : Bool) : PMF Bool := biasedLaw

/-- The invariant reference in this example is not the uniform law. -/
theorem biasedLaw_ne_uniform : biasedLaw ≠ PMF.uniformOfFintype Bool := by
  intro h
  have hmass := congrArg (fun p : PMF Bool => p true) h
  simp only [biasedLaw, PMF.ofFintype_apply, Bool.cond_true,
    PMF.uniformOfFintype_apply, Fintype.card_bool] at hmass
  have hreal := congrArg ENNReal.toReal hmass
  norm_num [ENNReal.toReal_inv] at hreal

/-- The nonuniform reference law is invariant under the reset channel. -/
theorem biasedLaw_invariant : biasedLaw.bind biasedReset = biasedLaw := by
  change biasedLaw.bind (fun _ => biasedLaw) = biasedLaw
  exact PMF.bind_const _ _

/-- One reset step contracts KL divergence toward the nonuniform invariant law. -/
theorem klDiv_contracts_toward_biased (p : PMF Bool) :
    InformationTheory.klDiv (p.bind biasedReset).toMeasure
        biasedLaw.toMeasure ≤
      InformationTheory.klDiv p.toMeasure biasedLaw.toMeasure :=
  klDiv_channel_invariant_le p biasedLaw biasedReset biasedLaw_invariant

/-- The first of two source laws with disjoint support. -/
def leftLaw : PMF Bool := PMF.pure false

/-- The second of two source laws with disjoint support. -/
def rightLaw : PMF Bool := PMF.pure true

/-- The source support condition for real-valued cascade contraction fails. -/
theorem source_support_not_subset :
    Not (leftLaw.support ⊆ rightLaw.support) := by
  simp [leftLaw, rightLaw]

/-- The averaging stage merges the two source laws. -/
theorem intermediate_laws_eq :
    leftLaw.bind averagingChannel = rightLaw.bind averagingChannel := by
  simp [leftLaw, rightLaw, averagingChannel]

/-- Support inclusion is restored after the averaging stage. -/
theorem intermediate_support_subset :
    (leftLaw.bind averagingChannel).support ⊆
      (rightLaw.bind averagingChannel).support := by
  rw [intermediate_laws_eq]

/-- `ENNReal`-valued KL contracts along the two stochastic stages. -/
theorem klDiv_cascade_contracts :
    InformationTheory.klDiv
        (leftLaw.bind (PMF.channelComp averagingChannel biasedReset)).toMeasure
        (rightLaw.bind (PMF.channelComp averagingChannel biasedReset)).toMeasure ≤
      InformationTheory.klDiv
        (leftLaw.bind averagingChannel).toMeasure
        (rightLaw.bind averagingChannel).toMeasure :=
  klDiv_channel_cascade_le leftLaw rightLaw averagingChannel biasedReset

/--
The one-stage theorem gives the weaker intermediate-support real cascade
contract directly, without requiring another public cascade declaration.
-/
theorem toReal_klDiv_cascade_contracts_from_intermediate :
    (InformationTheory.klDiv
        (leftLaw.bind (PMF.channelComp averagingChannel biasedReset)).toMeasure
        (rightLaw.bind (PMF.channelComp averagingChannel biasedReset)).toMeasure).toReal ≤
      (InformationTheory.klDiv
        (leftLaw.bind averagingChannel).toMeasure
        (rightLaw.bind averagingChannel).toMeasure).toReal := by
  simpa only [PMF.bind_channelComp] using
    toReal_klDiv_channel_le
      (leftLaw.bind averagingChannel) (rightLaw.bind averagingChannel)
      biasedReset intermediate_support_subset

/-- Mutual information contracts along the same two stochastic stages. -/
theorem mutualInfo_cascade_contracts :
    mutualInfo
        (PMF.channelJoint (PMF.uniformOfFintype Bool)
          (PMF.channelComp averagingChannel biasedReset)) ≤
      mutualInfo
        (PMF.channelJoint (PMF.uniformOfFintype Bool) averagingChannel) :=
  mutualInfo_channel_cascade_le
    (PMF.uniformOfFintype Bool) averagingChannel biasedReset

end

end StochasticChannels
end Examples
end LeanInfoTheory
