/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Sufficiency.KL

/-!
# Sufficient-statistics examples

This module gives compact finite examples for the principal sufficiency APIs:
fixed-prior and model-family characterizations, exact recovery, finite
Fisher-Neyman factorization, and KL-divergence preservation. It also records
two failure modes: a constant statistic that loses parameter information and a
channel that recovers only a marginal rather than the required complete law.
-/

namespace LeanInfoTheory
namespace Examples
namespace SufficientStatistics

open Shannon
open MeasureTheory

noncomputable section

local instance : MeasurableSpace Bool := ⊤

local instance : MeasurableSingletonClass Bool where
  measurableSet_singleton _ := trivial

namespace Ancillary

/-- A fair nuisance bit. -/
def fairBit : PMF Bool := PMF.uniformOfFintype Bool

/-- A channel producing an independent fair nuisance bit. -/
def noiseChannel (_ : Bool) : PMF Bool := fairBit

/-- Attach an independent fair nuisance bit to a binary signal law. -/
def observationLaw (p : PMF Bool) : PMF (Bool × Bool) :=
  PMF.channelJoint p noiseChannel

/-- Keep the signal coordinate and discard the nuisance coordinate. -/
def statistic : Bool × Bool -> Bool := Prod.fst

/-- Restore a discarded nuisance bit independently of the model parameter. -/
def recovery (b : Bool) : PMF (Bool × Bool) :=
  observationLaw (PMF.pure b)

private theorem exact_recovery (p : PMF Bool) :
    PMF.channelJoint
        ((observationLaw p).bind (PMF.deterministicChannel statistic)) recovery =
      (PMF.channelJoint
        (observationLaw p) (PMF.deterministicChannel statistic)).map Prod.swap := by
  rw [PMF.bind_deterministicChannel]
  have hstat : (observationLaw p).map statistic = p := by
    simpa only [observationLaw, statistic] using
      PMF.channelJoint_map_fst p noiseChannel
  rw [hstat]
  apply PMF.ext
  rintro ⟨b, b', n⟩
  have hswap :
      ((PMF.channelJoint
          (observationLaw p) (PMF.deterministicChannel statistic)).map
            Prod.swap) (b, (b', n)) =
        PMF.channelJoint
          (observationLaw p) (PMF.deterministicChannel statistic) ((b', n), b) := by
    simpa using
      PMF.map_apply_equiv
        (PMF.channelJoint
          (observationLaw p) (PMF.deterministicChannel statistic))
        (Equiv.prodComm (Bool × Bool) Bool) ((b', n), b)
  rw [PMF.channelJoint_apply, hswap, PMF.channelJoint_apply]
  cases b <;> cases b' <;>
    simp [recovery, observationLaw, noiseChannel, statistic,
      mul_comm]

private theorem statistic_sufficient_for
    {theta : Type*} (signalModel : theta -> PMF Bool) :
    IsSufficientStatistic
      (fun t => observationLaw (signalModel t)) statistic := by
  rw [IsSufficientStatistic, IsSufficientChannel]
  exact ⟨recovery, fun t => exact_recovery (signalModel t)⟩

/-- The midpoint model fixes the signal bit to the parameter. -/
def model (t : Bool) : PMF (Bool × Bool) :=
  observationLaw (PMF.pure t)

/-- The first-coordinate statistic is not globally injective. -/
theorem statistic_not_injective : Not (Function.Injective statistic) := by
  intro h
  have hpair : (false, false) = (false, true) := h rfl
  have : false = true := congrArg Prod.snd hpair
  cases this

/-- For each parameter, two supported observations collide under the statistic. -/
theorem statistic_collides_on_support (t : Bool) :
    ∃ x y : Bool × Bool,
      x ∈ (model t).support ∧ y ∈ (model t).support ∧
        x ≠ y ∧ statistic x = statistic y := by
  refine ⟨(t, false), (t, true), ?_, ?_, by simp, rfl⟩
  · simp [model, observationLaw, noiseChannel, fairBit]
  · simp [model, observationLaw, noiseChannel, fairBit]

/-- Discarding the nuisance bit is sufficient for the whole model family. -/
theorem statistic_isSufficient : IsSufficientStatistic model statistic := by
  change IsSufficientStatistic
    (fun t : Bool => observationLaw (PMF.pure t)) statistic
  exact statistic_sufficient_for (fun t : Bool => PMF.pure t)

/-- A full-support prior used for the fixed-prior view. -/
def fairPrior : PMF Bool := PMF.uniformOfFintype Bool

/-- The fair prior reaches both parameter values. -/
theorem fairPrior_support : fairPrior.support = Set.univ := by
  simpa only [fairPrior, Set.top_eq_univ] using
    PMF.support_uniformOfFintype Bool

/-- The generated parameter-observation law under the fair prior. -/
def experimentLaw : PMF (Bool × (Bool × Bool)) :=
  PMF.channelJoint fairPrior model

/-- Family sufficiency gives fixed-prior sufficiency under the fair prior. -/
theorem statistic_isSufficient_fixedPrior :
    IsSufficientStatisticOf experimentLaw
      (fun z => z.1) (fun z => z.2) statistic := by
  exact
    (isSufficientStatistic_iff_isSufficientStatisticOf_of_support_eq_univ
      fairPrior fairPrior_support model statistic).mp statistic_isSufficient

/-- The fixed-prior statistic preserves parameter-observation mutual information. -/
theorem mutualInfo_preserved_fixedPrior :
    mutualInfoOf experimentLaw (fun z => z.1)
        (fun z => statistic z.2) =
      mutualInfoOf experimentLaw (fun z => z.1) (fun z => z.2) := by
  exact
    (isSufficientStatisticOf_iff_mutualInfoOf_eq
      experimentLaw (fun z => z.1) (fun z => z.2) statistic).mp
        statistic_isSufficient_fixedPrior

/-- Fixed-prior sufficiency supplies an exact complete-law recovery channel. -/
theorem exists_exactRecovery_fixedPrior :
    ∃ R : Bool -> PMF (Bool × Bool),
      statisticTripleLawOf experimentLaw
          (fun z => z.1) (fun z => z.2) statistic =
        PMF.channelExtension
          (experimentLaw.map fun z => (z.1, statistic z.2)) R := by
  exact
    (isSufficientStatisticOf_iff_exists_recovery
      experimentLaw (fun z => z.1) (fun z => z.2) statistic).mp
        statistic_isSufficient_fixedPrior

/-- The same statistic is sufficient under every parameter prior. -/
theorem statistic_isSufficient_forall_prior :
    ∀ prior : PMF Bool,
      IsSufficientStatisticOf (PMF.channelJoint prior model)
        (fun z => z.1) (fun z => z.2) statistic := by
  exact
    (isSufficientStatistic_iff_forall_isSufficientStatisticOf
      model statistic).mp statistic_isSufficient

/-- The sufficient statistic satisfies the finite Fisher-Neyman factorization. -/
theorem exists_fisherNeymanFactorization :
    ∃ g : Bool -> Bool -> ENNReal, ∃ h : Bool × Bool -> ENNReal,
      (∀ t b, g t b ≠ ⊤) ∧
        (∀ a, h a ≠ ⊤) ∧
          ∀ t a, model t a = g t (statistic a) * h a := by
  exact
    (isSufficientStatistic_iff_exists_fisherNeymanFactorization
      model statistic).mp statistic_isSufficient

/-- The statistic preserves KL divergence between every pair of model laws. -/
theorem klDiv_preserved (s t : Bool) :
    InformationTheory.klDiv
        ((model s).map statistic).toMeasure
        ((model t).map statistic).toMeasure =
      InformationTheory.klDiv
        (model s).toMeasure (model t).toMeasure :=
  klDiv_eq_of_isSufficientStatistic model statistic
    statistic_isSufficient s t

/-- A full-support nonuniform signal law. -/
def biasedSignal : PMF Bool :=
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

/-- Two overlapping signal laws for the guarded binary KL characterization. -/
def overlapSignalModel : Bool -> PMF Bool
  | false => fairBit
  | true => biasedSignal

/-- Attach the same nuisance bit to each overlapping signal law. -/
def overlapModel (t : Bool) : PMF (Bool × Bool) :=
  observationLaw (overlapSignalModel t)

/-- The overlapping model has the support inclusion required by the KL converse. -/
theorem overlap_support_subset :
    (overlapModel false).support ⊆ (overlapModel true).support := by
  rintro ⟨b, n⟩ _
  simp only [overlapModel, observationLaw, PMF.mem_support_channelJoint_iff]
  constructor
  · cases b
    · simp only [overlapSignalModel, biasedSignal, PMF.mem_support_iff,
        PMF.ofFintype_apply, Bool.cond_false]
      exact ENNReal.coe_ne_zero.mpr
        (ne_of_gt (tsub_pos_iff_lt.mpr (by norm_num)))
    · simp [overlapSignalModel, biasedSignal]
  · simp [noiseChannel, fairBit]

/-- The first-coordinate statistic is sufficient for the overlapping model. -/
theorem overlap_statistic_isSufficient :
    IsSufficientStatistic overlapModel statistic := by
  change IsSufficientStatistic
    (fun t : Bool => observationLaw (overlapSignalModel t)) statistic
  exact statistic_sufficient_for overlapSignalModel

/-- The channel-facing binary KL equality characterizes this sufficient model. -/
theorem overlap_channel_iff_klDiv_eq :
    IsSufficientChannel overlapModel (PMF.deterministicChannel statistic) ↔
      InformationTheory.klDiv
          ((overlapModel false).bind (PMF.deterministicChannel statistic)).toMeasure
          ((overlapModel true).bind (PMF.deterministicChannel statistic)).toMeasure =
        InformationTheory.klDiv
          (overlapModel false).toMeasure (overlapModel true).toMeasure :=
  isSufficientChannel_iff_klDiv_eq_bool overlapModel
    (PMF.deterministicChannel statistic) overlap_support_subset

/-- The statistic-facing binary KL equality gives the same characterization. -/
theorem overlap_statistic_iff_klDiv_eq :
    IsSufficientStatistic overlapModel statistic ↔
      InformationTheory.klDiv
          ((overlapModel false).map statistic).toMeasure
          ((overlapModel true).map statistic).toMeasure =
        InformationTheory.klDiv
          (overlapModel false).toMeasure (overlapModel true).toMeasure :=
  isSufficientStatistic_iff_klDiv_eq_bool
    overlapModel statistic overlap_support_subset

end Ancillary

namespace Constant

/-- Two point-mass model laws that must remain distinguishable. -/
def model (t : Bool) : PMF Bool := PMF.pure t

/-- A statistic that discards the observation completely. -/
def statistic (_ : Bool) : Unit := ()

/-- The constant statistic is not sufficient for the separated model. -/
theorem statistic_not_sufficient : Not (IsSufficientStatistic model statistic) := by
  intro h
  rw [IsSufficientStatistic, IsSufficientChannel] at h
  obtain ⟨R, hR⟩ := h
  have hfalse : R () true = 0 := by
    simpa [model, statistic, PMF.bind_deterministicChannel,
      PMF.channelJoint_deterministicChannel, PMF.map_comp] using
        congrArg (fun q : PMF (Unit × Bool) => q ((), true)) (hR false)
  have htrue : R () true = 1 := by
    simpa [model, statistic, PMF.bind_deterministicChannel,
      PMF.channelJoint_deterministicChannel, PMF.map_comp] using
        congrArg (fun q : PMF (Unit × Bool) => q ((), true)) (hR true)
  exact zero_ne_one (hfalse.symm.trans htrue)

end Constant

namespace MarginalOnly

/-- A fair law for the marginal-only recovery counterexample. -/
def law : PMF Bool := PMF.uniformOfFintype Bool

/-- A recovery channel that forgets its input and resamples the fair law. -/
def resetRecovery (_ : Bool) : PMF Bool := law

/-- The reset channel recovers the input marginal after the identity statistic. -/
theorem recovers_marginal : (law.map id).bind resetRecovery = law := by
  rw [PMF.map_id]
  change law.bind (fun _ => law) = law
  exact PMF.bind_const _ _

/-- Marginal recovery does not reconstruct the identity input-output coupling. -/
theorem does_not_recover_fullJoint :
    PMF.channelJoint (law.map id) resetRecovery ≠
      (PMF.channelJoint law (PMF.deterministicChannel id)).map Prod.swap := by
  intro h
  have hmass := congrArg (fun q : PMF (Bool × Bool) => q (false, true)) h
  change
    PMF.channelJoint (law.map id) resetRecovery (false, true) =
      ((PMF.channelJoint law (PMF.deterministicChannel id)).map Prod.swap)
        (false, true) at hmass
  have hswap :
      ((PMF.channelJoint law (PMF.deterministicChannel id)).map Prod.swap)
          (false, true) =
        PMF.channelJoint law (PMF.deterministicChannel id) (true, false) := by
    exact
      PMF.map_apply_equiv
        (PMF.channelJoint law (PMF.deterministicChannel id))
        (Equiv.prodComm Bool Bool) (true, false)
  rw [PMF.channelJoint_apply, hswap, PMF.channelJoint_apply] at hmass
  simp [law, resetRecovery] at hmass

end MarginalOnly

end

end SufficientStatistics
end Examples
end LeanInfoTheory
