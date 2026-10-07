/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.DataProcessing

/-!
# KL divergence and finite sufficient channels

This module connects exact recovery of finite PMF channels to equality in KL
data processing. It is downstream of both the lightweight sufficient-statistic
core and the measure-theoretic data-processing layer, so kernel and KL imports
do not enter `Shannon.SemanticBridge.Sufficiency`.

The first result covers two input laws recovered by one common channel. Under
input support inclusion, the converse identifies equality in KL data processing
with the existence of such a channel. Deterministic statistics are exposed as
map-facing specializations. The final theorem band lifts exact recovery to model
families: sufficiency preserves KL divergence between every pair of model laws,
and one guarded KL equality characterizes sufficiency for a Boolean-indexed
two-law family.
-/

namespace LeanInfoTheory
namespace Shannon

open MeasureTheory

noncomputable section

universe u v w

private theorem bind_recovery_eq_of_joint_recovery
    {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (W : alpha -> PMF beta) (R : beta -> PMF alpha)
    (hR : PMF.channelJoint (p.bind W) R =
      (PMF.channelJoint p W).map Prod.swap) :
    (p.bind W).bind R = p := by
  have hmap := congrArg (fun q : PMF (beta × alpha) => q.map Prod.snd) hR
  have hcomp : Prod.snd ∘ Prod.swap = (Prod.fst : alpha × beta -> alpha) := by
    funext z
    rfl
  simpa only [PMF.channelJoint_map_snd, PMF.map_comp,
    hcomp, PMF.channelJoint_map_fst] using hmap

/--
If one channel exactly recovers the complete output-input joint law for each
of two input laws, then the forward channel preserves their `ENNReal` KL
divergence.

No support inclusion is needed: data processing through the forward and
recovery channels gives the two inequalities even when either divergence is
infinite.
-/
theorem klDiv_channel_eq_of_common_recovery
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta) (R : beta -> PMF alpha)
    (hp : PMF.channelJoint (p.bind W) R =
      (PMF.channelJoint p W).map Prod.swap)
    (hq : PMF.channelJoint (q.bind W) R =
      (PMF.channelJoint q W).map Prod.swap) :
    InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure =
      InformationTheory.klDiv p.toMeasure q.toMeasure := by
  have hforward := klDiv_channel_le p q W
  have hreverse := klDiv_channel_le (p.bind W) (q.bind W) R
  have hp_recover : (p.bind W).bind R = p :=
    bind_recovery_eq_of_joint_recovery p W R hp
  have hq_recover : (q.bind W).bind R = q :=
    bind_recovery_eq_of_joint_recovery q W R hq
  apply le_antisymm hforward
  simpa only [hp_recover, hq_recover] using hreverse

/-! ## Guarded recovery characterizations -/

/--
Under input support inclusion, equality in finite `ENNReal` KL data processing
holds exactly when one channel recovers both complete output-input joint laws.

The support hypothesis is needed only for the converse: it excludes the
uninformative case where both KL divergences are `⊤`. The recovery-to-equality
direction is the unconditional theorem above.
-/
theorem klDiv_channel_eq_iff_exists_common_recovery
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta)
    (h : p.support ⊆ q.support) :
    InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure =
        InformationTheory.klDiv p.toMeasure q.toMeasure ↔
      ∃ R : beta -> PMF alpha,
        PMF.channelJoint (p.bind W) R =
            (PMF.channelJoint p W).map Prod.swap ∧
          PMF.channelJoint (q.bind W) R =
            (PMF.channelJoint q W).map Prod.swap := by
  classical
  let := Fintype.ofFinite alpha
  constructor
  · intro heq
    have hposterior :=
      (klDiv_channel_eq_iff_posterior_eq_on_support p q W h).mp heq
    refine ⟨channelPosterior q W, ?_, channelPosterior_reconstructs_joint q W⟩
    calc
      PMF.channelJoint (p.bind W) (channelPosterior q W) =
          PMF.channelJoint (p.bind W) (channelPosterior p W) :=
        (PMF.channelJoint_eq_iff_eq_on_support
          (p.bind W) (channelPosterior q W) (channelPosterior p W)).mpr
            (fun b hb => (hposterior b hb).symm)
      _ = (PMF.channelJoint p W).map Prod.swap :=
        channelPosterior_reconstructs_joint p W
  · rintro ⟨R, hp, hq⟩
    exact klDiv_channel_eq_of_common_recovery p q W R hp hq

/--
The real-valued finite KL equality case has the same common exact-recovery
characterization under input support inclusion.
-/
theorem toReal_klDiv_channel_eq_iff_exists_common_recovery
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta)
    (h : p.support ⊆ q.support) :
    (InformationTheory.klDiv
        (p.bind W).toMeasure (q.bind W).toMeasure).toReal =
        (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal ↔
      ∃ R : beta -> PMF alpha,
        PMF.channelJoint (p.bind W) R =
            (PMF.channelJoint p W).map Prod.swap ∧
          PMF.channelJoint (q.bind W) R =
            (PMF.channelJoint q W).map Prod.swap := by
  have hinput : InformationTheory.klDiv p.toMeasure q.toMeasure ≠ ⊤ :=
    (klDiv_pmf_ne_top_iff_support_subset p q).2 h
  have houtput :
      InformationTheory.klDiv
          (p.bind W).toMeasure (q.bind W).toMeasure ≠ ⊤ :=
    ne_top_of_le_ne_top hinput (klDiv_channel_le p q W)
  rw [ENNReal.toReal_eq_toReal_iff' houtput hinput,
    klDiv_channel_eq_iff_exists_common_recovery p q W h]

private theorem map_graph_swap
    {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (T : alpha -> beta) :
    (p.map fun a => (a, T a)).map Prod.swap =
      p.map fun a => (T a, a) := by
  rw [PMF.map_comp]
  rfl

/--
Under input support inclusion, a deterministic statistic preserves `ENNReal`
KL divergence exactly when one channel recovers both input-statistic graph
laws from their statistic marginals.
-/
theorem klDiv_map_eq_iff_exists_common_recovery
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (T : alpha -> beta)
    (h : p.support ⊆ q.support) :
    InformationTheory.klDiv (p.map T).toMeasure (q.map T).toMeasure =
        InformationTheory.klDiv p.toMeasure q.toMeasure ↔
      ∃ R : beta -> PMF alpha,
        PMF.channelJoint (p.map T) R =
            p.map (fun a => (T a, a)) ∧
          PMF.channelJoint (q.map T) R =
            q.map (fun a => (T a, a)) := by
  simpa only [PMF.bind_deterministicChannel,
    PMF.channelJoint_deterministicChannel, map_graph_swap] using
      klDiv_channel_eq_iff_exists_common_recovery
        p q (PMF.deterministicChannel T) h

/--
The real-valued deterministic-statistic equality case has the same common
exact-recovery characterization under input support inclusion.
-/
theorem toReal_klDiv_map_eq_iff_exists_common_recovery
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (T : alpha -> beta)
    (h : p.support ⊆ q.support) :
    (InformationTheory.klDiv (p.map T).toMeasure (q.map T).toMeasure).toReal =
        (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal ↔
      ∃ R : beta -> PMF alpha,
        PMF.channelJoint (p.map T) R =
            p.map (fun a => (T a, a)) ∧
          PMF.channelJoint (q.map T) R =
            q.map (fun a => (T a, a)) := by
  simpa only [PMF.bind_deterministicChannel,
    PMF.channelJoint_deterministicChannel, map_graph_swap] using
      toReal_klDiv_channel_eq_iff_exists_common_recovery
        p q (PMF.deterministicChannel T) h

/-! ## Family-level KL preservation -/

/--
A sufficient channel preserves `ENNReal` KL divergence between every pair of
laws in the model family.

The family sufficiency hypothesis already supplies one recovery channel shared
by all parameter values, so no support inclusion is needed, even when the
divergence is infinite.
-/
theorem klDiv_eq_of_isSufficientChannel
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (model : theta -> PMF alpha) (W : alpha -> PMF beta)
    (h : IsSufficientChannel model W) (s t : theta) :
    InformationTheory.klDiv
        ((model s).bind W).toMeasure ((model t).bind W).toMeasure =
      InformationTheory.klDiv (model s).toMeasure (model t).toMeasure := by
  obtain ⟨R, hR⟩ := h
  exact klDiv_channel_eq_of_common_recovery
    (model s) (model t) W R (hR s) (hR t)

/--
A sufficient deterministic statistic preserves `ENNReal` KL divergence
between every pair of laws in the model family.
-/
theorem klDiv_eq_of_isSufficientStatistic
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (model : theta -> PMF alpha) (T : alpha -> beta)
    (h : IsSufficientStatistic model T) (s t : theta) :
    InformationTheory.klDiv
        ((model s).map T).toMeasure ((model t).map T).toMeasure =
      InformationTheory.klDiv (model s).toMeasure (model t).toMeasure := by
  simpa only [PMF.bind_deterministicChannel] using
    klDiv_eq_of_isSufficientChannel
      model (PMF.deterministicChannel T) h s t

/-! ## Binary-family converse -/

/--
For a Boolean-indexed model whose `false` law is supported within its `true`
law, channel sufficiency is equivalent to preservation of their directed
`ENNReal` KL divergence.

The binary index is substantive: the guarded equality produces one recovery
channel for these two laws, which therefore recovers every law in this family.
No analogous converse for unrelated pairwise witnesses in a larger family is
claimed.
-/
theorem isSufficientChannel_iff_klDiv_eq_bool
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (model : Bool -> PMF alpha) (W : alpha -> PMF beta)
    (hsupport : (model false).support ⊆ (model true).support) :
    IsSufficientChannel model W ↔
      InformationTheory.klDiv
          ((model false).bind W).toMeasure
          ((model true).bind W).toMeasure =
        InformationTheory.klDiv
          (model false).toMeasure (model true).toMeasure := by
  constructor
  · intro h
    exact klDiv_eq_of_isSufficientChannel model W h false true
  · intro heq
    obtain ⟨R, hfalse, htrue⟩ :=
      (klDiv_channel_eq_iff_exists_common_recovery
        (model false) (model true) W hsupport).mp heq
    refine ⟨R, ?_⟩
    intro t
    cases t
    · exact hfalse
    · exact htrue

/--
For a guarded Boolean-indexed model, a deterministic statistic is sufficient
exactly when it preserves the directed `ENNReal` KL divergence from the
`false` law to the `true` law.
-/
theorem isSufficientStatistic_iff_klDiv_eq_bool
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (model : Bool -> PMF alpha) (T : alpha -> beta)
    (hsupport : (model false).support ⊆ (model true).support) :
    IsSufficientStatistic model T ↔
      InformationTheory.klDiv
          ((model false).map T).toMeasure
          ((model true).map T).toMeasure =
        InformationTheory.klDiv
          (model false).toMeasure (model true).toMeasure := by
  simpa only [IsSufficientStatistic, PMF.bind_deterministicChannel] using
    isSufficientChannel_iff_klDiv_eq_bool
      model (PMF.deterministicChannel T) hsupport

end

end Shannon
end LeanInfoTheory
