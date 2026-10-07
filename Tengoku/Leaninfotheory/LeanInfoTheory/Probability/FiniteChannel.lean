/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.Finite

/-!
# Finite stochastic channels

This file provides the small PMF-first construction layer for finite discrete
channels. A channel from `alpha` to `beta` is represented directly by a
function `W : alpha -> PMF beta`; the alphabet finiteness assumptions belong on
the information-theoretic theorems that need them rather than in a bundled
channel structure.

The output law of an input PMF `p` through `W` is mathlib's `p.bind W`, and the
identity channel is `PMF.pure`. This module introduces names only for the
constructions that later Markov and data-processing proofs will repeat:

* `PMF.deterministicChannel` turns a function into a pure-output channel;
* `PMF.channelComp` composes two channels in sampling order;
* `PMF.channelJoint` forms the induced input-output joint law;
* `PMF.channelExtension` extends a pair law through a channel on its second
  coordinate.

The accompanying theorem layer gives their pointwise masses, natural
projections, composition laws, deterministic reductions, and support
characterizations without adding alphabet finiteness assumptions.

No entropy, measurable-space, kernel, or KL-divergence dependency is introduced
here. Those belong in the separately importable Shannon semantic bridge.
-/

namespace PMF

noncomputable section

universe u v w x

/-- The deterministic channel induced by a function. -/
def deterministicChannel {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) : alpha -> PMF beta :=
  fun a => PMF.pure (f a)

/--
Composition of two PMF-valued channels in sampling order: first sample through
`W`, then sample through `V`.
-/
def channelComp {alpha : Type u} {beta : Type v} {gamma : Type w}
    (W : alpha -> PMF beta) (V : beta -> PMF gamma) : alpha -> PMF gamma :=
  fun a => (W a).bind V

/--
The joint law of an input distributed as `p` and an output sampled from `W`.
-/
def channelJoint {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (W : alpha -> PMF beta) : PMF (Prod alpha beta) :=
  p.bind fun a => (W a).map fun b => (a, b)

/--
Extend a joint law of `(A,B)` by sampling `C` from a channel depending only on
`B`. The result uses Lean's right-associated triple type `(A, B, C)`.
-/
def channelExtension {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (Prod alpha beta)) (V : beta -> PMF gamma) :
    PMF (Prod alpha (Prod beta gamma)) :=
  p.bind fun ab => (V ab.2).map fun c => (ab.1, ab.2, c)

/-! ## Pointwise laws -/

/-- A deterministic channel returns the pure law at the function value. -/
@[simp]
theorem deterministicChannel_apply {alpha : Type u} {beta : Type v}
    (f : alpha -> beta) (a : alpha) :
    deterministicChannel f a = PMF.pure (f a) :=
  rfl

/-- Pointwise mass formula for channel composition. -/
theorem channelComp_apply {alpha : Type u} {beta : Type v} {gamma : Type w}
    (W : alpha -> PMF beta) (V : beta -> PMF gamma) (a : alpha) (c : gamma) :
    channelComp W V a c = ∑' b, W a b * V b c :=
  rfl

/-- The induced joint mass factors as input mass times channel mass. -/
@[simp]
theorem channelJoint_apply {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (W : alpha -> PMF beta) (a : alpha) (b : beta) :
    channelJoint p W (a, b) = p a * W a b := by
  classical
  rw [channelJoint, PMF.bind_apply]
  rw [tsum_eq_single a]
  · rw [PMF.map_apply_of_injective (p := W a)
      (hf := fun _ _ h => congrArg Prod.snd h) b]
  · intro a' ha'
    have hnot : (a, b) ∉ Set.range (fun b' => (a', b')) := by
      rintro ⟨b', hab⟩
      exact ha' (congrArg Prod.fst hab)
    rw [PMF.map_apply_eq_zero_of_notMem_range (W a') hnot, mul_zero]

/-- The extended triple mass factors as pair mass times channel mass. -/
@[simp]
theorem channelExtension_apply
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta)) (V : beta -> PMF gamma)
    (a : alpha) (b : beta) (c : gamma) :
    channelExtension p V (a, b, c) = p (a, b) * V b c := by
  classical
  rw [channelExtension, PMF.bind_apply]
  rw [tsum_eq_single (a, b)]
  · rw [PMF.map_apply_of_injective (p := V b)
      (hf := fun _ _ h => congrArg (fun z => z.2.2) h) c]
  · intro ab hab
    have hnot : (a, b, c) ∉ Set.range (fun c' => (ab.1, ab.2, c')) := by
      rintro ⟨c', habc⟩
      exact hab (congrArg (fun z => (z.1, z.2.1)) habc)
    rw [PMF.map_apply_eq_zero_of_notMem_range (V ab.2) hnot, mul_zero]

/-! ## Projection laws -/

/-- The first projection of an induced joint law is its input law. -/
@[simp]
theorem channelJoint_map_fst {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (W : alpha -> PMF beta) :
    (channelJoint p W).map Prod.fst = p := by
  unfold channelJoint
  calc
    (p.bind fun a => (W a).map fun b => (a, b)).map Prod.fst =
        p.bind fun a => ((W a).map fun b => (a, b)).map Prod.fst :=
      PMF.map_bind _ _ _
    _ = p.bind PMF.pure := by
      apply congrArg (PMF.bind p)
      funext a
      calc
        ((W a).map fun b => (a, b)).map Prod.fst =
            (W a).map (Prod.fst ∘ fun b => (a, b)) :=
          PMF.map_comp (p := W a) (f := fun b => (a, b)) Prod.fst
        _ = (W a).map (Function.const beta a) := rfl
        _ = PMF.pure a := PMF.map_const (p := W a) (b := a)
    _ = p := PMF.bind_pure p

/-- The second projection of an induced joint law is the channel output law. -/
@[simp]
theorem channelJoint_map_snd {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (W : alpha -> PMF beta) :
    (channelJoint p W).map Prod.snd = p.bind W := by
  unfold channelJoint
  calc
    (p.bind fun a => (W a).map fun b => (a, b)).map Prod.snd =
        p.bind fun a => ((W a).map fun b => (a, b)).map Prod.snd :=
      PMF.map_bind _ _ _
    _ = p.bind W := by
      apply congrArg (PMF.bind p)
      funext a
      calc
        ((W a).map fun b => (a, b)).map Prod.snd =
            (W a).map (Prod.snd ∘ fun b => (a, b)) :=
          PMF.map_comp (p := W a) (f := fun b => (a, b)) Prod.snd
        _ = (W a).map id := rfl
        _ = W a := PMF.map_id (p := W a)

/-- Projecting an extension to its original input pair recovers that pair law. -/
@[simp]
theorem channelExtension_map_input {alpha : Type u} {beta : Type v}
    {gamma : Type w} (p : PMF (alpha × beta)) (V : beta -> PMF gamma) :
    (channelExtension p V).map (fun z => (z.1, z.2.1)) = p := by
  unfold channelExtension
  calc
    (p.bind fun ab => (V ab.2).map fun c => (ab.1, ab.2, c)).map
          (fun z => (z.1, z.2.1)) =
        p.bind fun ab => ((V ab.2).map fun c => (ab.1, ab.2, c)).map
          (fun z => (z.1, z.2.1)) :=
      PMF.map_bind _ _ _
    _ = p.bind PMF.pure := by
      apply congrArg (PMF.bind p)
      funext ab
      calc
        ((V ab.2).map fun c => (ab.1, ab.2, c)).map
            (fun z => (z.1, z.2.1)) =
            (V ab.2).map ((fun z => (z.1, z.2.1)) ∘
              fun c => (ab.1, ab.2, c)) :=
          PMF.map_comp (p := V ab.2) (f := fun c => (ab.1, ab.2, c))
            (fun z => (z.1, z.2.1))
        _ = (V ab.2).map (Function.const gamma ab) := by
          rcases ab with ⟨a, b⟩
          rfl
        _ = PMF.pure ab := PMF.map_const (p := V ab.2) (b := ab)
    _ = p := PMF.bind_pure p

/--
Projecting an extension to the channel input-output pair gives the induced
joint law of the original second marginal and the extending channel.
-/
@[simp]
theorem channelExtension_map_outputPair
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta)) (V : beta -> PMF gamma) :
    (channelExtension p V).map (fun z => z.2) = channelJoint (p.map Prod.snd) V := by
  unfold channelExtension
  calc
    (p.bind fun ab => (V ab.2).map fun c => (ab.1, ab.2, c)).map
          (fun z => z.2) =
        p.bind fun ab => ((V ab.2).map fun c => (ab.1, ab.2, c)).map
          (fun z => z.2) :=
      PMF.map_bind _ _ _
    _ = p.bind fun ab => (V ab.2).map fun c => (ab.2, c) := by
      apply congrArg (PMF.bind p)
      funext ab
      calc
        ((V ab.2).map fun c => (ab.1, ab.2, c)).map (fun z => z.2) =
            (V ab.2).map ((fun z => z.2) ∘ fun c => (ab.1, ab.2, c)) :=
          PMF.map_comp (p := V ab.2) (f := fun c => (ab.1, ab.2, c))
            (fun z => z.2)
        _ = (V ab.2).map (fun c => (ab.2, c)) := rfl
    _ = (p.map Prod.snd).bind (fun b => (V b).map fun c => (b, c)) :=
      (PMF.bind_map p Prod.snd (fun b => (V b).map fun c => (b, c))).symm
    _ = channelJoint (p.map Prod.snd) V := rfl

/-- Projecting an extension to its new output gives the corresponding output law. -/
@[simp]
theorem channelExtension_map_output {alpha : Type u} {beta : Type v}
    {gamma : Type w} (p : PMF (alpha × beta)) (V : beta -> PMF gamma) :
    (channelExtension p V).map (fun z => z.2.2) = (p.map Prod.snd).bind V := by
  unfold channelExtension
  calc
    (p.bind fun ab => (V ab.2).map fun c => (ab.1, ab.2, c)).map
          (fun z => z.2.2) =
        p.bind fun ab => ((V ab.2).map fun c => (ab.1, ab.2, c)).map
          (fun z => z.2.2) :=
      PMF.map_bind _ _ _
    _ = p.bind fun ab => V ab.2 := by
      apply congrArg (PMF.bind p)
      funext ab
      calc
        ((V ab.2).map fun c => (ab.1, ab.2, c)).map (fun z => z.2.2) =
            (V ab.2).map ((fun z => z.2.2) ∘ fun c => (ab.1, ab.2, c)) :=
          PMF.map_comp (p := V ab.2) (f := fun c => (ab.1, ab.2, c))
            (fun z => z.2.2)
        _ = (V ab.2).map id := rfl
        _ = V ab.2 := PMF.map_id (p := V ab.2)
    _ = (p.map Prod.snd).bind V := (PMF.bind_map p Prod.snd V).symm

/--
For a two-stage channel, projecting the generated triple to its endpoints gives
the joint law induced by the composite channel.
-/
@[simp]
theorem channelExtension_map_endpoints
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF alpha) (W : alpha -> PMF beta) (V : beta -> PMF gamma) :
    (channelExtension (channelJoint p W) V).map (fun z => (z.1, z.2.2)) =
      channelJoint p (channelComp W V) := by
  calc
    (channelExtension (channelJoint p W) V).map (fun z => (z.1, z.2.2)) =
        (channelJoint p W).bind fun ab => (V ab.2).map fun c => (ab.1, c) := by
      rw [channelExtension, PMF.map_bind]
      congr 1
      funext ab
      rw [PMF.map_comp]
      rfl
    _ = p.bind fun a => (W a).bind fun b => (V b).map fun c => (a, c) := by
      rw [channelJoint, PMF.bind_bind]
      congr 1
      funext a
      rw [PMF.bind_map]
      rfl
    _ = channelJoint p (channelComp W V) := by
      rw [channelJoint]
      congr 1
      funext a
      rw [← PMF.map_bind]
      rfl

/-! ## Channel algebra -/

/-- Sending an input law through a composite channel is iterated `PMF.bind`. -/
theorem bind_channelComp {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF alpha) (W : alpha -> PMF beta) (V : beta -> PMF gamma) :
    p.bind (channelComp W V) = (p.bind W).bind V := by
  change p.bind (fun a => (W a).bind V) = (p.bind W).bind V
  exact (PMF.bind_bind p W V).symm

/-- The pure channel is a left identity for channel composition. -/
@[simp]
theorem channelComp_pure_left {alpha : Type u} {beta : Type v}
    (W : alpha -> PMF beta) :
    channelComp PMF.pure W = W := by
  funext a
  simp [channelComp]

/-- The pure channel is a right identity for channel composition. -/
@[simp]
theorem channelComp_pure_right {alpha : Type u} {beta : Type v}
    (W : alpha -> PMF beta) :
    channelComp W PMF.pure = W := by
  funext a
  simp [channelComp]

/-- Channel composition is associative. -/
theorem channelComp_assoc
    {alpha : Type u} {beta : Type v} {gamma : Type w} {delta : Type x}
    (W : alpha -> PMF beta) (V : beta -> PMF gamma) (U : gamma -> PMF delta) :
    channelComp (channelComp W V) U = channelComp W (channelComp V U) := by
  funext a
  exact PMF.bind_bind (W a) V U

/-! ## Deterministic channels -/

/-- Sending a law through a deterministic channel is `PMF.map`. -/
@[simp]
theorem bind_deterministicChannel {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (f : alpha -> beta) :
    p.bind (deterministicChannel f) = p.map f :=
  rfl

/-- A deterministic first stage evaluates the following channel at its image. -/
@[simp]
theorem channelComp_deterministic_left
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (f : alpha -> beta) (W : beta -> PMF gamma) :
    channelComp (deterministicChannel f) W = fun a => W (f a) := by
  funext a
  simp [channelComp, deterministicChannel]

/-- A deterministic second stage maps each output law. -/
@[simp]
theorem channelComp_deterministic_right
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (W : alpha -> PMF beta) (f : beta -> gamma) :
    channelComp W (deterministicChannel f) = fun a => (W a).map f :=
  rfl

/-- The joint law of a deterministic channel is the graph pushforward. -/
@[simp]
theorem channelJoint_deterministicChannel
    {alpha : Type u} {beta : Type v} (p : PMF alpha) (f : alpha -> beta) :
    channelJoint p (deterministicChannel f) = p.map fun a => (a, f a) := by
  unfold channelJoint deterministicChannel
  simp_rw [PMF.pure_map]
  rfl

/-- Extending a pair law through a deterministic channel is its graph pushforward. -/
theorem channelExtension_deterministicChannel
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta)) (f : beta -> gamma) :
    channelExtension p (deterministicChannel f) =
      p.map fun ab => (ab.1, ab.2, f ab.2) := by
  unfold channelExtension deterministicChannel
  simp_rw [PMF.pure_map]
  rfl

/-! ## Support laws -/

/-- An output lies in a composite channel's support through a supported intermediate atom. -/
@[simp]
theorem mem_support_channelComp_iff
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (W : alpha -> PMF beta) (V : beta -> PMF gamma) (a : alpha) (c : gamma) :
    c ∈ (channelComp W V a).support ↔
      ∃ b ∈ (W a).support, c ∈ (V b).support := by
  exact PMF.mem_support_bind_iff (W a) V c

/-- A pair is supported by the induced joint law exactly when both stages support it. -/
@[simp]
theorem mem_support_channelJoint_iff {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (W : alpha -> PMF beta) (a : alpha) (b : beta) :
    (a, b) ∈ (channelJoint p W).support ↔
      a ∈ p.support ∧ b ∈ (W a).support := by
  simp [PMF.mem_support_iff]

/--
Two channels induce the same joint law from an input PMF exactly when they
agree on every supported input atom. Their values away from the input support
are irrelevant.
-/
theorem channelJoint_eq_iff_eq_on_support
    {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (W V : alpha -> PMF beta) :
    channelJoint p W = channelJoint p V ↔
      ∀ a, a ∈ p.support -> W a = V a := by
  constructor
  · intro h a ha
    apply PMF.ext
    intro b
    have hmass := congrArg (fun q : PMF (alpha × beta) => q (a, b)) h
    change channelJoint p W (a, b) = channelJoint p V (a, b) at hmass
    rw [channelJoint_apply, channelJoint_apply] at hmass
    have hpa : p a ≠ 0 := (p.mem_support_iff a).1 ha
    have htop : p a ≠ ⊤ := p.apply_ne_top a
    have hcancel := congrArg (fun x : ENNReal => (p a)⁻¹ * x) hmass
    simpa only [ENNReal.inv_mul_cancel_left hpa htop] using hcancel
  · intro h
    apply PMF.ext
    rintro ⟨a, b⟩
    rw [channelJoint_apply, channelJoint_apply]
    by_cases ha : a ∈ p.support
    · rw [h a ha]
    · have hzero : p a = 0 := by
        by_contra hne
        exact ha ((p.mem_support_iff a).2 hne)
      rw [hzero, zero_mul, zero_mul]

/-- A triple is supported by an extension exactly when its pair and new output are supported. -/
@[simp]
theorem mem_support_channelExtension_iff
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta)) (V : beta -> PMF gamma)
    (a : alpha) (b : beta) (c : gamma) :
    (a, b, c) ∈ (channelExtension p V).support ↔
      (a, b) ∈ p.support ∧ c ∈ (V b).support := by
  simp [PMF.mem_support_iff]

end

end PMF
