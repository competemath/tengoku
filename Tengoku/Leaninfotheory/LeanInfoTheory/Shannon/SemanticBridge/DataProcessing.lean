/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Markov
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Sufficiency
import Tengoku

/-!
# Data processing for finite stochastic channels

This file bridges the project's PMF-valued finite channels to mathlib Markov
kernels. Channels remain represented publicly by functions
`W : alpha -> PMF beta`; `pmfChannelKernel W` is the measure-theoretic view used
only by the semantic data-processing layer.

The first bridge theorem identifies the induced PMF joint law with mathlib's
composition-product measure. The module then constructs the total finite
posterior channel and proves PMF-level joint reconstruction. It characterizes
family sufficiency by agreement with one common posterior on every supported
output fiber, then combines the posterior infrastructure with mathlib's KL
chain rule to obtain an exact decomposition. Its nonnegative remainder yields
the finite KL data-processing family for stochastic channels, deterministic
maps, and channel cascades, while its zero case characterizes equality through
posterior agreement on every supported output. Almost-everywhere kernel
equality remains the lower-level measure bridge. The same API then gives
one-step contraction toward an invariant reference law and entropy growth under
uniform-preserving and doubly stochastic channels. Kernel and KL imports remain
outside the lightweight finite Shannon API.
-/

namespace LeanInfoTheory
namespace Shannon

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v w

/-! ## PMF channels as Markov kernels -/

/--
The mathlib kernel associated to a countable PMF-valued channel.

This is a semantic view of the existing raw channel function, not a second
public channel representation.
-/
def pmfChannelKernel
    {alpha : Type u} {beta : Type v}
    [MeasurableSpace alpha] [Countable alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta]
    (W : alpha -> PMF beta) : Kernel alpha beta :=
  Kernel.ofFunOfCountable fun a => (W a).toMeasure

/-- A PMF-valued channel induces a Markov kernel through `pmfChannelKernel`. -/
instance pmfChannelKernel.instIsMarkovKernel
    {alpha : Type u} {beta : Type v}
    [MeasurableSpace alpha] [Countable alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta]
    (W : alpha -> PMF beta) : IsMarkovKernel (pmfChannelKernel W) :=
  ⟨fun a => by
    change IsProbabilityMeasure (W a).toMeasure
    infer_instance⟩

/-- Evaluating the kernel associated to a PMF channel recovers its PMF measure. -/
@[simp]
theorem pmfChannelKernel_apply
    {alpha : Type u} {beta : Type v}
    [MeasurableSpace alpha] [Countable alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta]
    (W : alpha -> PMF beta) (a : alpha) :
    pmfChannelKernel W a = (W a).toMeasure :=
  rfl

/--
The measure of an induced PMF joint law is the composition-product of the
input measure and the associated Markov kernel.
-/
theorem channelJoint_toMeasure
    {alpha : Type u} {beta : Type v}
    [MeasurableSpace alpha] [Countable alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [Countable beta] [MeasurableSingletonClass beta]
    (p : PMF alpha) (W : alpha -> PMF beta) :
    (PMF.channelJoint p W).toMeasure =
      p.toMeasure ⊗ₘ pmfChannelKernel W := by
  rw [Measure.ext_iff_singleton]
  rintro ⟨a, b⟩
  rw [show ({(a, b)} : Set (alpha × beta)) = {a} ×ˢ {b} by ext x; simp]
  rw [Measure.compProd_apply_prod (MeasurableSet.singleton a)
    (MeasurableSet.singleton b)]
  simp [PMF.channelJoint_apply, PMF.toMeasure_apply_singleton]

/-! ## Finite posterior channels -/

/--
The total posterior channel associated to an input law and a finite stochastic
channel.

On an output atom of positive probability this is the usual posterior input
law. On a null output fiber it uses the fallback already documented by
`condFstGivenSndChannel`; reconstruction makes that arbitrary branch
semantically irrelevant.
-/
def channelPosterior
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF alpha) (W : alpha -> PMF beta) : beta -> PMF alpha :=
  condFstGivenSndChannel (PMF.channelJoint p W)

/--
Sampling the posterior from the channel output law reconstructs the induced
joint law in output-input order.
-/
theorem channelPosterior_reconstructs_joint
    {alpha : Type u} {beta : Type v}
    [Fintype alpha]
    (p : PMF alpha) (W : alpha -> PMF beta) :
    PMF.channelJoint (p.bind W) (channelPosterior p W) =
      (PMF.channelJoint p W).map Prod.swap := by
  rw [← PMF.channelJoint_map_snd p W]
  rw [channelPosterior, channelJoint_condFstGivenSndChannel]

/--
A finite-input channel is sufficient for a model family exactly when one
parameter-independent posterior channel agrees with every model posterior on
each supported output fiber. Writing `Q_t = (model t).bind W`, the witness `R`
satisfies `channelPosterior (model t) W b = R b` whenever `Q_t b != 0`.
Consequently, two models supporting the same output have the same posterior
there. A model for which `b` is null imposes no condition, although another
supporting model may determine `R b`; if `b` is null for the entire family,
that row is wholly unconstrained. The support guard prevents the arbitrary
fallback used by the total posterior on a null fiber from acquiring
conditional-probability meaning.
-/
theorem isSufficientChannel_iff_exists_common_posterior
    {theta : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha]
    (model : theta → PMF alpha) (W : alpha → PMF beta) :
    IsSufficientChannel model W ↔
      ∃ R : beta → PMF alpha, ∀ t b,
        b ∈ ((model t).bind W).support →
          channelPosterior (model t) W b = R b := by
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro t b hb
    have hjoint :
        PMF.channelJoint ((model t).bind W) R =
          PMF.channelJoint ((model t).bind W) (channelPosterior (model t) W) :=
      (hR t).trans (channelPosterior_reconstructs_joint (model t) W).symm
    exact ((PMF.channelJoint_eq_iff_eq_on_support
      ((model t).bind W) R (channelPosterior (model t) W)).mp hjoint b hb).symm
  · rintro ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro t
    calc
      PMF.channelJoint ((model t).bind W) R =
          PMF.channelJoint ((model t).bind W) (channelPosterior (model t) W) :=
        (PMF.channelJoint_eq_iff_eq_on_support
          ((model t).bind W) R (channelPosterior (model t) W)).mpr
            (fun b hb => (hR t b hb).symm)
      _ = (PMF.channelJoint (model t) W).map Prod.swap :=
        channelPosterior_reconstructs_joint (model t) W

/-! ## Finite KL posterior decomposition -/

private theorem channelPosterior_compProd
    {alpha : Type u} {beta : Type v}
    [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [Countable beta] [MeasurableSingletonClass beta]
    (p : PMF alpha) (W : alpha -> PMF beta) :
    (p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior p W) =
      ((PMF.channelJoint p W).map Prod.swap).toMeasure := by
  rw [← channelJoint_toMeasure, channelPosterior_reconstructs_joint]

-- The posterior proof needs only equivalence invariance for the coordinate
-- swap. Keep this private until another production consumer justifies a
-- general public relabeling theorem.
private theorem klDiv_map_equiv
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (e : alpha ≃ beta) :
    InformationTheory.klDiv (p.map e).toMeasure (q.map e).toMeasure =
      InformationTheory.klDiv p.toMeasure q.toMeasure := by
  classical
  let := Fintype.ofFinite alpha
  let := Fintype.ofFinite beta
  have hsupport :
      (p.map e).support ⊆ (q.map e).support ↔ p.support ⊆ q.support := by
    simpa only [PMF.support_map] using
      (Set.image_subset_image_iff e.injective (s := p.support) (t := q.support))
  by_cases hpq : p.support ⊆ q.support
  · have hmap : (p.map e).support ⊆ (q.map e).support := hsupport.mpr hpq
    have hac : p.toMeasure ≪ q.toMeasure :=
      (toMeasure_absolutelyContinuous_iff_support_subset p q).2 hpq
    have hacMap : (p.map e).toMeasure ≪ (q.map e).toMeasure :=
      (toMeasure_absolutelyContinuous_iff_support_subset (p.map e) (q.map e)).2 hmap
    have hne : InformationTheory.klDiv p.toMeasure q.toMeasure ≠ ⊤ :=
      (klDiv_pmf_ne_top_iff_support_subset p q).2 hpq
    have hneMap :
        InformationTheory.klDiv (p.map e).toMeasure (q.map e).toMeasure ≠ ⊤ :=
      (klDiv_pmf_ne_top_iff_support_subset (p.map e) (q.map e)).2 hmap
    apply (ENNReal.toReal_eq_toReal_iff' hneMap hne).mp
    rw [toReal_klDiv_pmf_eq_sum (p.map e) (q.map e) hacMap,
      toReal_klDiv_pmf_eq_sum p q hac]
    calc
      (∑ b : beta,
          ((p.map e) b).toReal * Real.log (((p.map e) b / (q.map e) b).toReal)) =
          ∑ a : alpha,
            ((p.map e) (e a)).toReal *
              Real.log (((p.map e) (e a) / (q.map e) (e a)).toReal) :=
        (Equiv.sum_comp e _).symm
      _ = ∑ a : alpha, (p a).toReal * Real.log ((p a / q a).toReal) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [PMF.map_apply_equiv p e a, PMF.map_apply_equiv q e a]
  · have hmap : ¬ (p.map e).support ⊆ (q.map e).support :=
      fun h => hpq (hsupport.mp h)
    rw [(klDiv_pmf_eq_top_iff_not_support_subset (p.map e) (q.map e)).2 hmap,
      (klDiv_pmf_eq_top_iff_not_support_subset p q).2 hpq]

/--
Exact KL decomposition for two input laws passed through the same finite
stochastic channel.

The first term is the divergence between the output laws. The remainder is the
divergence between the two posterior kernels over the first output law, stated
with mathlib composition-product measures. No support-inclusion assumption is
needed because the identity is `ENNReal`-valued.
-/
theorem klDiv_channel_eq_add_posterior
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta) :
    InformationTheory.klDiv p.toMeasure q.toMeasure =
      InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure +
        InformationTheory.klDiv
          ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior p W))
          ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior q W)) := by
  classical
  let := Fintype.ofFinite beta
  have hsame := InformationTheory.klDiv_compProd_left
    p.toMeasure q.toMeasure (pmfChannelKernel W)
  have hjointP := channelJoint_toMeasure p W
  have hjointQ := channelJoint_toMeasure q W
  have hswap := klDiv_map_equiv
    (PMF.channelJoint p W) (PMF.channelJoint q W)
    (Equiv.prodComm alpha beta)
  have hpostP := channelPosterior_compProd p W
  have hpostQ := channelPosterior_compProd q W
  have hchain := InformationTheory.klDiv_compProd_eq_add
    (p.bind W).toMeasure (q.bind W).toMeasure
    (pmfChannelKernel (channelPosterior p W))
    (pmfChannelKernel (channelPosterior q W))
  calc
    InformationTheory.klDiv p.toMeasure q.toMeasure =
        InformationTheory.klDiv
          (p.toMeasure ⊗ₘ pmfChannelKernel W)
          (q.toMeasure ⊗ₘ pmfChannelKernel W) := hsame.symm
    _ = InformationTheory.klDiv
          (PMF.channelJoint p W).toMeasure
          (PMF.channelJoint q W).toMeasure :=
      congrArg₂ InformationTheory.klDiv hjointP.symm hjointQ.symm
    _ = InformationTheory.klDiv
          ((PMF.channelJoint p W).map Prod.swap).toMeasure
          ((PMF.channelJoint q W).map Prod.swap).toMeasure := hswap.symm
    _ = InformationTheory.klDiv
          ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior p W))
          ((q.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior q W)) :=
      congrArg₂ InformationTheory.klDiv hpostP.symm hpostQ.symm
    _ = InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure +
          InformationTheory.klDiv
            ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior p W))
            ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior q W)) := hchain

/-! ## KL data processing -/

/--
Finite relative entropy contracts when two input laws pass through the same
stochastic channel.

This is the primary channel data-processing inequality. It is unconditional
because KL divergence is valued in `ENNReal`.
-/
theorem klDiv_channel_le
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta) :
    InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure <=
      InformationTheory.klDiv p.toMeasure q.toMeasure := by
  classical
  let := Fintype.ofFinite alpha
  rw [klDiv_channel_eq_add_posterior p q W]
  exact le_add_of_nonneg_right bot_le

private theorem klDiv_channel_eq_iff_posterior_klDiv_eq_zero_of_ne_top
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta)
    (hfinite : InformationTheory.klDiv p.toMeasure q.toMeasure ≠ ⊤) :
    InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure =
        InformationTheory.klDiv p.toMeasure q.toMeasure ↔
      InformationTheory.klDiv
          ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior p W))
          ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior q W)) = 0 := by
  have hdecomp := klDiv_channel_eq_add_posterior p q W
  constructor
  · intro heq
    have houtput :
        InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure ≠ ⊤ := by
      intro htop
      exact hfinite (heq.symm.trans htop)
    apply (ENNReal.add_right_inj houtput).mp
    calc
      InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure +
            InformationTheory.klDiv
              ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior p W))
              ((p.bind W).toMeasure ⊗ₘ pmfChannelKernel (channelPosterior q W)) =
          InformationTheory.klDiv p.toMeasure q.toMeasure := hdecomp.symm
      _ = InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure := heq.symm
      _ = InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure + 0 :=
        (add_zero _).symm
  · intro hzero
    rw [hdecomp, hzero, add_zero]

/--
Equality in finite KL data processing holds exactly when the two posterior
kernels agree almost everywhere under the first output law.

Input support inclusion excludes the uninformative infinite-divergence case.
This is the measure-level equality bridge; finite pointwise posterior forms can
be derived by replacing almost-everywhere equality with equality on supported
output atoms.
-/
theorem klDiv_channel_eq_iff_posterior_ae_eq
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta)
    (h : p.support ⊆ q.support) :
    InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure =
        InformationTheory.klDiv p.toMeasure q.toMeasure ↔
      pmfChannelKernel (channelPosterior p W) =ᵐ[(p.bind W).toMeasure]
        pmfChannelKernel (channelPosterior q W) := by
  rw [klDiv_channel_eq_iff_posterior_klDiv_eq_zero_of_ne_top p q W
      ((klDiv_pmf_ne_top_iff_support_subset p q).2 h),
    InformationTheory.klDiv_eq_zero_iff, Kernel.compProd_eq_iff]

/--
Equality in finite KL data processing holds exactly when the two posterior PMFs
agree on every output atom reached by the first input law.

This is the primary finite-facing equality theorem. The input support condition
excludes infinite KL divergence, while the output support condition in the
conclusion leaves the total posterior's arbitrary null-fiber values irrelevant.
-/
theorem klDiv_channel_eq_iff_posterior_eq_on_support
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta)
    (h : p.support ⊆ q.support) :
    InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure =
        InformationTheory.klDiv p.toMeasure q.toMeasure ↔
      ∀ b, b ∈ (p.bind W).support →
        channelPosterior p W b = channelPosterior q W b := by
  rw [klDiv_channel_eq_iff_posterior_ae_eq p q W h,
    ← Kernel.compProd_eq_iff,
    ← channelJoint_toMeasure (p.bind W) (channelPosterior p W),
    ← channelJoint_toMeasure (p.bind W) (channelPosterior q W),
    PMF.toMeasure_inj, PMF.channelJoint_eq_iff_eq_on_support]

/--
Real-valued finite relative entropy contracts through a common stochastic
channel when the first input law is supported by the second.

Only the input support condition is needed; no separate support hypothesis on
the output laws is required.
-/
theorem toReal_klDiv_channel_le
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta)
    (h : p.support ⊆ q.support) :
    (InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure).toReal <=
      (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal :=
  ENNReal.toReal_mono
    ((klDiv_pmf_ne_top_iff_support_subset p q).2 h)
    (klDiv_channel_le p q W)

/--
Equality in real-valued finite KL data processing holds exactly when the two
posterior PMFs agree on every output atom reached by the first input law.

Input support inclusion makes both KL divergences finite, so this theorem has
no `ENNReal.toReal` top-branch ambiguity.
-/
theorem toReal_klDiv_channel_eq_iff_posterior_eq_on_support
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W : alpha -> PMF beta)
    (h : p.support ⊆ q.support) :
    (InformationTheory.klDiv
        (p.bind W).toMeasure (q.bind W).toMeasure).toReal =
        (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal ↔
      ∀ b, b ∈ (p.bind W).support →
        channelPosterior p W b = channelPosterior q W b := by
  have hinput : InformationTheory.klDiv p.toMeasure q.toMeasure ≠ ⊤ :=
    (klDiv_pmf_ne_top_iff_support_subset p q).2 h
  have houtput :
      InformationTheory.klDiv
          (p.bind W).toMeasure (q.bind W).toMeasure ≠ ⊤ :=
    ne_top_of_le_ne_top hinput (klDiv_channel_le p q W)
  rw [ENNReal.toReal_eq_toReal_iff' houtput hinput,
    klDiv_channel_eq_iff_posterior_eq_on_support p q W h]

/-- KL data processing for a deterministic map of a finite alphabet. -/
theorem klDiv_map_le
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (f : alpha -> beta) :
    InformationTheory.klDiv (p.map f).toMeasure (q.map f).toMeasure <=
      InformationTheory.klDiv p.toMeasure q.toMeasure := by
  simpa only [PMF.bind_deterministicChannel] using
    klDiv_channel_le p q (PMF.deterministicChannel f)

/--
Real-valued KL data processing for a deterministic map, under input support
inclusion.
-/
theorem toReal_klDiv_map_le
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (f : alpha -> beta)
    (h : p.support ⊆ q.support) :
    (InformationTheory.klDiv (p.map f).toMeasure (q.map f).toMeasure).toReal <=
      (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal := by
  simpa only [PMF.bind_deterministicChannel] using
    toReal_klDiv_channel_le p q (PMF.deterministicChannel f) h

-- A common channel preserves support inclusion. The cascade corollary is the
-- only current production consumer, so this stays private.
private theorem support_bind_mono
    {alpha : Type u} {beta : Type v}
    (p q : PMF alpha) (W : alpha -> PMF beta)
    (h : p.support ⊆ q.support) :
    (p.bind W).support ⊆ (q.bind W).support := by
  intro b hb
  rw [PMF.mem_support_bind_iff] at hb ⊢
  rcases hb with ⟨a, ha, hWa⟩
  exact ⟨a, h ha, hWa⟩

/--
Appending a common channel stage cannot increase the KL divergence between
the two intermediate output laws.
-/
theorem klDiv_channelComp_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Finite beta] [Finite gamma]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    [MeasurableSpace gamma] [MeasurableSingletonClass gamma]
    (p q : PMF alpha) (W : alpha -> PMF beta) (V : beta -> PMF gamma) :
    InformationTheory.klDiv
        (p.bind (PMF.channelComp W V)).toMeasure
        (q.bind (PMF.channelComp W V)).toMeasure <=
      InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure := by
  simpa only [PMF.bind_channelComp] using
    klDiv_channel_le (p.bind W) (q.bind W) V

/-- Textbook-facing alias for `ENNReal`-valued KL contraction along a cascade. -/
theorem klDiv_channel_cascade_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Finite beta] [Finite gamma]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    [MeasurableSpace gamma] [MeasurableSingletonClass gamma]
    (p q : PMF alpha) (W : alpha -> PMF beta) (V : beta -> PMF gamma) :
    InformationTheory.klDiv
        (p.bind (PMF.channelComp W V)).toMeasure
        (q.bind (PMF.channelComp W V)).toMeasure <=
      InformationTheory.klDiv (p.bind W).toMeasure (q.bind W).toMeasure :=
  klDiv_channelComp_le p q W V

/--
Real-valued KL contraction for a channel cascade. The original input support
condition suffices for the intermediate laws as well.
-/
theorem toReal_klDiv_channelComp_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Finite beta] [Finite gamma]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    [MeasurableSpace gamma] [MeasurableSingletonClass gamma]
    (p q : PMF alpha) (W : alpha -> PMF beta) (V : beta -> PMF gamma)
    (h : p.support ⊆ q.support) :
    (InformationTheory.klDiv
        (p.bind (PMF.channelComp W V)).toMeasure
        (q.bind (PMF.channelComp W V)).toMeasure).toReal <=
      (InformationTheory.klDiv
        (p.bind W).toMeasure (q.bind W).toMeasure).toReal := by
  simpa only [PMF.bind_channelComp] using
    toReal_klDiv_channel_le (p.bind W) (q.bind W) V
      (support_bind_mono p q W h)

/-- Textbook-facing alias for real-valued KL contraction along a cascade. -/
theorem toReal_klDiv_channel_cascade_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Finite beta] [Finite gamma]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    [MeasurableSpace gamma] [MeasurableSingletonClass gamma]
    (p q : PMF alpha) (W : alpha -> PMF beta) (V : beta -> PMF gamma)
    (h : p.support ⊆ q.support) :
    (InformationTheory.klDiv
        (p.bind (PMF.channelComp W V)).toMeasure
        (q.bind (PMF.channelComp W V)).toMeasure).toReal <=
      (InformationTheory.klDiv
        (p.bind W).toMeasure (q.bind W).toMeasure).toReal :=
  toReal_klDiv_channelComp_le p q W V h

/-! ## Invariant references and entropy growth -/

/--
KL divergence to an invariant reference law cannot increase after one step of
a finite stochastic channel.
-/
theorem klDiv_channel_invariant_le
    {alpha : Type u}
    [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p r : PMF alpha) (W : alpha -> PMF alpha)
    (hr : r.bind W = r) :
    InformationTheory.klDiv (p.bind W).toMeasure r.toMeasure <=
      InformationTheory.klDiv p.toMeasure r.toMeasure := by
  simpa only [hr] using klDiv_channel_le p r W

/--
Real-valued KL divergence to an invariant reference law contracts when the
input law is supported by that reference.
-/
theorem toReal_klDiv_channel_invariant_le
    {alpha : Type u}
    [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p r : PMF alpha) (W : alpha -> PMF alpha)
    (hr : r.bind W = r) (h : p.support ⊆ r.support) :
    (InformationTheory.klDiv (p.bind W).toMeasure r.toMeasure).toReal <=
      (InformationTheory.klDiv p.toMeasure r.toMeasure).toReal := by
  simpa only [hr] using toReal_klDiv_channel_le p r W h

/--
A finite channel that preserves the uniform law cannot decrease Shannon
entropy.

The discrete measurable structure used by the KL proof remains local, so the
statement has only the natural finite nonempty alphabet assumptions.
-/
theorem entropy_le_entropy_bind_of_uniform_invariant
    {alpha : Type u} [Fintype alpha] [Nonempty alpha]
    (p : PMF alpha) (W : alpha -> PMF alpha)
    (hW : (PMF.uniformOfFintype alpha).bind W =
      PMF.uniformOfFintype alpha) :
    entropy p <= entropy (p.bind W) := by
  let : MeasurableSpace alpha := ⊤
  have : MeasurableSingletonClass alpha := ⟨fun _ => trivial⟩
  have hkl := toReal_klDiv_channel_invariant_le
    p (PMF.uniformOfFintype alpha) W hW (by simp)
  rw [toReal_klDiv_pmf_uniformOfFintype,
    toReal_klDiv_pmf_uniformOfFintype] at hkl
  linarith

/--
A finite doubly stochastic channel cannot decrease Shannon entropy.

Each `W a` is already a probability law, hence supplies the row-stochastic
condition. The displayed hypothesis is the remaining column-sum condition.
No transition-matrix representation is introduced.
-/
theorem entropy_le_entropy_bind_of_doublyStochastic
    {alpha : Type u} [Fintype alpha] [Nonempty alpha]
    (p : PMF alpha) (W : alpha -> PMF alpha)
    (hW : ∀ b, ∑ a, W a b = 1) :
    entropy p <= entropy (p.bind W) := by
  apply entropy_le_entropy_bind_of_uniform_invariant p W
  ext b
  rw [PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ← Finset.mul_sum, hW b, mul_one]

end

end Shannon
end LeanInfoTheory
