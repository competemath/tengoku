/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.FiniteChannel
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Independence

/-!
# Finite channels and Markov structure

This file owns the channel-facing semantic layer used to formulate finite
Markov chains and data processing. It defines PMF and random-variable Markov
predicates through conditional independence, and constructs the total
conditional channel associated with a joint PMF together with its branch,
null-fiber irrelevance, and reconstruction laws. Later results in this module
characterize Markov structure by cross-product factorization, positive
conditional fibers, zero conditional mutual information, and chain reversal,
complete the channel-factorization converse, and connect channel-generated laws
to information loss.

The canonical `condFstGivenSnd p b hb` remains defined only on positive-mass
conditioning atoms. The total channel below uses it on those atoms and chooses
`fstMarginal p` on null fibers. That fallback is a technical device for making
a PMF-valued function on every input; it is not assigned conditional-probability
meaning. Public consequences are therefore weighted or support-aware so that
the null-fiber choice is irrelevant.
-/

namespace LeanInfoTheory
namespace Shannon

noncomputable section

universe u v w x

/-! ## Markov predicates -/

/--
Random variables `X`, `Y`, and `Z` form the Markov chain `X → Y → Z` when
`X` and `Z` are conditionally independent given `Y`.
-/
def IsMarkovChainOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) : Prop :=
  IsCondIndependentOf p X Z Y

/-- A triple PMF is a Markov chain in its first-to-second-to-third coordinate order. -/
def IsMarkovChain
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) : Prop :=
  IsMarkovChainOf p (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2)

/-! ## Markov characterizations -/

/--
A triple law is Markov in coordinate order exactly when every atom satisfies
the cross-product factorization

`p(a,b,c) * p_B(b) = p_AB(a,b) * p_BC(b,c)`.

The identity also covers null middle-coordinate fibers, so it requires no
finite-alphabet or measurable-space assumptions.
@isnad1 id=iff.0h4v.s7.ef41cbaf6e8d from=translated src=- shape=92ee41bc vocab=adb592ce
-/
theorem isMarkovChain_iff_crossProduct
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    IsMarkovChain p ↔
      ∀ a b c,
        p (a, b, c) * sndMarginal (fstSndMarginal p) b =
          fstSndMarginal p (a, b) * sndThirdMarginal p (b, c) := by
  let swap23 : alpha × beta × gamma → alpha × gamma × beta :=
    fun x => (x.1, x.2.2, x.2.1)
  have hswap23 : Function.Injective swap23 := by
    intro x y hxy
    apply Prod.ext
    · exact congrArg (fun z => z.1) hxy
    · apply Prod.ext
      · exact congrArg (fun z => z.2.2) hxy
      · exact congrArg (fun z => z.2.1) hxy
  have hmass (a : alpha) (b : beta) (c : gamma) :
      (p.map swap23) (a, c, b) = p (a, b, c) := by
    simpa [swap23] using
      PMF.map_apply_of_injective p hswap23 (a, b, c)
  have hmiddle :
      thirdMarginal (p.map swap23) = sndMarginal (fstSndMarginal p) := by
    change (p.map swap23).map (fun x => x.2.2) =
      (p.map fun x => (x.1, x.2.1)).map Prod.snd
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  have hfirstMiddle :
      fstThirdMarginal (p.map swap23) = fstSndMarginal p := by
    change (p.map swap23).map (fun x => (x.1, x.2.2)) =
      p.map fun x => (x.1, x.2.1)
    rw [PMF.map_comp]
    rfl
  have hlastMiddle :
      sndThirdMarginal (p.map swap23) =
        (sndThirdMarginal p).map Prod.swap := by
    change (p.map swap23).map (fun x => (x.2.1, x.2.2)) =
      (p.map fun x => (x.2.1, x.2.2)).map Prod.swap
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  have hlastMiddleMass (b : beta) (c : gamma) :
      sndThirdMarginal (p.map swap23) (c, b) =
        sndThirdMarginal p (b, c) := by
    rw [hlastMiddle]
    exact PMF.map_apply_equiv
      (sndThirdMarginal p) (Equiv.prodComm beta gamma) (b, c)
  change IsCondIndependent (p.map swap23) ↔ _
  unfold IsCondIndependent
  constructor
  · intro hp a b c
    have h := hp a c b
    rw [hmass a b c, hmiddle, hfirstMiddle,
      hlastMiddleMass b c] at h
    exact h
  · intro hp a c b
    have h := hp a b c
    rw [hmass a b c, hmiddle, hfirstMiddle,
      hlastMiddleMass b c]
    exact h

/--
A triple law is Markov exactly when its two endpoint coordinates are
independent in every positive-mass conditional fiber of the middle coordinate.
The displayed mapped law orders the coordinates as endpoint, endpoint, middle
so that it can reuse `condFstSndGivenThird` directly.
@isnad1 id=iff.0h4v.s7.fa0df0c174f1 from=translated src=- shape=84215e57 vocab=26e768b2
-/
theorem isMarkovChain_iff_isIndependent_condFstSndGivenThird
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    IsMarkovChain p ↔
      ∀ b (hb : thirdMarginal
          (p.map fun x => (x.1, x.2.2, x.2.1)) b ≠ 0),
        IsIndependent
          (condFstSndGivenThird
            (p.map fun x => (x.1, x.2.2, x.2.1)) b hb) := by
  change IsCondIndependent (p.map fun x => (x.1, x.2.2, x.2.1)) ↔ _
  exact isCondIndependent_iff_isIndependent_condFstSndGivenThird
    (p.map fun x => (x.1, x.2.2, x.2.1))

/-- Textbook-facing alias for the positive-fiber Markov characterization.
@isnad1 id=iff.0h4v.s7.fa0df0c174f1 from=translated src=- shape=84215e57 vocab=26e768b2
-/
theorem isMarkovChain_iff_fiberwise_endpoints_independent
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    IsMarkovChain p ↔
      ∀ b (hb : thirdMarginal
          (p.map fun x => (x.1, x.2.2, x.2.1)) b ≠ 0),
        IsIndependent
          (condFstSndGivenThird
            (p.map fun x => (x.1, x.2.2, x.2.1)) b hb) :=
  isMarkovChain_iff_isIndependent_condFstSndGivenThird p

/--
The Markov condition `X → Y → Z` is equivalent to the textbook zero-CMI
identity `I(X;Z | Y) = 0`.
@isnad1 id=iff.0h8v.s5.dbb56b3eeac0 from=translated src=- shape=c9497242 vocab=afbe7291
-/
theorem condMutualInfoOf_eq_zero_iff_isMarkovChainOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) :
    condMutualInfoOf p X Z Y = 0 ↔ IsMarkovChainOf p X Y Z := by
  change condMutualInfoOf p X Z Y = 0 ↔ IsCondIndependentOf p X Z Y
  exact condMutualInfoOf_eq_zero_iff_isCondIndependentOf p X Z Y

/-- Reversing a Markov chain preserves the random-variable Markov condition.
@isnad1 id=iff.0h8v.s5.7821dd0e8490 from=translated src=- shape=26f379f8 vocab=a72e99b1
-/
theorem isMarkovChainOf_reverse
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) :
    IsMarkovChainOf p Z Y X ↔ IsMarkovChainOf p X Y Z := by
  change IsCondIndependentOf p Z X Y ↔ IsCondIndependentOf p X Z Y
  exact isCondIndependentOf_swap p X Z Y

/-- Reversing the coordinates of a triple law preserves its Markov condition.
@isnad1 id=iff.0h4v.s6.25b3142a6c23 from=translated src=- shape=e9d418bc vocab=d2562fc3
-/
@[simp]
theorem isMarkovChain_map_reverse
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    IsMarkovChain (p.map fun x => (x.2.2, x.2.1, x.1)) ↔
      IsMarkovChain p := by
  unfold IsMarkovChain IsMarkovChainOf IsCondIndependentOf
  rw [PMF.map_comp]
  change IsCondIndependent (p.map fun x => (x.2.2, x.1, x.2.1)) ↔
    IsCondIndependent (p.map fun x => (x.1, x.2.2, x.2.1))
  simpa [PMF.map_comp, Function.comp_def] using
    isCondIndependent_map_swap12
      (p.map fun x => (x.1, x.2.2, x.2.1))

/--
The total channel from the second coordinate to the first associated with a
joint PMF.

For `P_B(b) != 0`, this is the canonical conditional law `P_{A | B=b}`. For a
null fiber, it is the first marginal `P_A`. The fallback supplies a PMF without
requiring an additional `Nonempty alpha` assumption; it has no intended
conditional semantics and disappears from the weighted reconstruction laws.
-/
def condFstGivenSndChannel {alpha : Type u} {beta : Type v}
    [Fintype alpha] (p : PMF (alpha × beta)) : beta -> PMF alpha :=
  fun b =>
    if hb : sndMarginal p b = 0 then
      fstMarginal p
    else
      condFstGivenSnd p b hb

/-! ## Total conditional-channel laws -/

/-- On a null conditioning fiber, the total channel uses the documented fallback.
@isnad1 id=eq.1h4v.s5.aa6d9b83daac from=translated src=- shape=44a63e13 vocab=28f23e8e
-/
@[simp]
theorem condFstGivenSndChannel_of_sndMarginal_eq_zero
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) {b : beta} (hb : sndMarginal p b = 0) :
    condFstGivenSndChannel p b = fstMarginal p := by
  rw [condFstGivenSndChannel, dite_eq_left hb]

/-- On a positive conditioning fiber, the total channel is the canonical conditional PMF.
@isnad1 id=eq.1h4v.s5.7db608aef0f7 from=translated src=- shape=f1b613e4 vocab=28dc7694
-/
theorem condFstGivenSndChannel_of_sndMarginal_ne_zero
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) {b : beta} (hb : sndMarginal p b ≠ 0) :
    condFstGivenSndChannel p b = condFstGivenSnd p b hb := by
  rw [condFstGivenSndChannel, dite_eq_right hb]

/--
The value chosen for a null conditional fiber is irrelevant after weighting by
the conditioning marginal. The PMF `q` represents any alternative fallback.
@isnad1 id=eq.1h6v.s6.2a62da7df89d from=translated src=- shape=8dbade75 vocab=873fbed4
-/
theorem condFstGivenSndChannel_null_fiber_irrelevant
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (q : PMF alpha) {b : beta}
    (hb : sndMarginal p b = 0) (a : alpha) :
    sndMarginal p b * condFstGivenSndChannel p b a =
      sndMarginal p b * q a := by
  rw [hb, zero_mul, zero_mul]

/--
The conditioning marginal times the total conditional-channel mass reconstructs
the original joint mass on every fiber, including null fibers.
@isnad1 id=eq.0h5v.s6.62024e6d3d06 from=translated src=- shape=605b2baa vocab=d7c613a6
-/
theorem sndMarginal_mul_condFstGivenSndChannel
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (b : beta) (a : alpha) :
    sndMarginal p b * condFstGivenSndChannel p b a = p (a, b) := by
  by_cases hb : sndMarginal p b = 0
  · rw [hb, zero_mul]
    exact (apply_eq_zero_of_sndMarginal_eq_zero p a hb).symm
  · rw [condFstGivenSndChannel_of_sndMarginal_ne_zero p hb]
    exact sndMarginal_mul_condFstGivenSnd p b hb a

/--
Sampling the total conditional channel from the second marginal reconstructs
the original pair law with its coordinates in channel input-output order.
@isnad1 id=eq.0h3v.s5.fc42eda9e0f9 from=translated src=- shape=48bd0385 vocab=f01dd93b
-/
theorem channelJoint_condFstGivenSndChannel
    {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) :
    PMF.channelJoint (sndMarginal p) (condFstGivenSndChannel p) =
      p.map Prod.swap := by
  apply PMF.ext
  rintro ⟨b, a⟩
  rw [PMF.channelJoint_apply, sndMarginal_mul_condFstGivenSndChannel]
  exact (PMF.map_apply_equiv p (Equiv.prodComm alpha beta) (a, b)).symm

/-! ## Channel-generated Markov chains -/

/--
Extending any pair law of `(A,B)` by sampling `C` from a channel depending only
on `B` produces the Markov chain `A → B → C`.

The result is type-generic and includes null middle-coordinate fibers through
the cross-product characterization, without requiring a conditional PMF.
@isnad1 id=ismarkov.0h5v.s4.7a2b467f6f69 from=translated src=- shape=eace8fe9 vocab=8512ed1a
-/
@[simp]
theorem isMarkovChain_channelExtension
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta)) (V : beta → PMF gamma) :
    IsMarkovChain (PMF.channelExtension p V) := by
  rw [isMarkovChain_iff_crossProduct]
  have hinput : fstSndMarginal (PMF.channelExtension p V) = p :=
    PMF.channelExtension_map_input p V
  have houtputPair :
      sndThirdMarginal (PMF.channelExtension p V) =
        PMF.channelJoint (sndMarginal p) V :=
    PMF.channelExtension_map_outputPair p V
  intro a b c
  rw [hinput, houtputPair, PMF.channelExtension_apply,
    PMF.channelJoint_apply]
  ac_rfl

/--
Deterministic post-processing of the middle variable always gives the forward
Markov chain `X → Y → f(Y)`.

Equivalently, `X` and `f(Y)` are conditionally independent given `Y`:
`X ⟂ f(Y) | Y`.
@isnad1 id=ismarkov.0h8v.s5.d231cc045361 from=translated src=- shape=44d73c9a vocab=a72e99b1
-/
theorem isMarkovChainOf_comp
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (f : beta → gamma) :
    IsMarkovChainOf p X Y (fun omega => f (Y omega)) := by
  let q : PMF (alpha × beta) := p.map fun omega => (X omega, Y omega)
  have htriple :
      p.map (fun omega => (X omega, Y omega, f (Y omega))) =
        PMF.channelExtension q (PMF.deterministicChannel f) := by
    rw [PMF.channelExtension_deterministicChannel]
    dsimp [q]
    rw [PMF.map_comp]
    rfl
  have hmarkov :
      IsMarkovChain (p.map fun omega => (X omega, Y omega, f (Y omega))) := by
    rw [htriple]
    exact isMarkovChain_channelExtension _ _
  simpa [IsMarkovChain, IsMarkovChainOf, IsCondIndependentOf,
    PMF.map_comp, Function.comp_def] using hmarkov

/--
A finite triple law is Markov exactly when its first-two marginal, extended by
the total conditional channel `P_{C | B}` extracted from its second-third
marginal, reconstructs the original law.

The second-third marginal is swapped into `(C,B)` order because
`condFstGivenSndChannel` constructs a channel from the second coordinate to the
first. Its documented null-fiber fallback is irrelevant: both the original and
reconstructed atom masses vanish whenever the middle marginal does.
@isnad1 id=iff.0h4v.s5.b703dabeb7a5 from=translated src=- shape=e47a2493 vocab=b68e5c94
-/
theorem isMarkovChain_iff_eq_channelExtension_condFstGivenSndChannel
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    IsMarkovChain p ↔
      p = PMF.channelExtension (fstSndMarginal p)
        (condFstGivenSndChannel ((sndThirdMarginal p).map Prod.swap)) := by
  classical
  constructor
  · intro hp
    rw [isMarkovChain_iff_crossProduct] at hp
    apply PMF.ext
    rintro ⟨a, b, c⟩
    rw [PMF.channelExtension_apply]
    let q : PMF (gamma × beta) := (sndThirdMarginal p).map Prod.swap
    have hmiddle : sndMarginal q = sndMarginal (fstSndMarginal p) := by
      change
        (((p.map fun x => (x.2.1, x.2.2)).map Prod.swap).map Prod.snd) =
          (p.map fun x => (x.1, x.2.1)).map Prod.snd
      simp only [PMF.map_comp]
      rfl
    have hreconstruct :
        sndMarginal (fstSndMarginal p) b * condFstGivenSndChannel q b c =
          sndThirdMarginal p (b, c) := by
      rw [← hmiddle, sndMarginal_mul_condFstGivenSndChannel]
      exact PMF.map_apply_equiv
        (sndThirdMarginal p) (Equiv.prodComm beta gamma) (b, c)
    by_cases hb : sndMarginal (fstSndMarginal p) b = 0
    · have hab : fstSndMarginal p (a, b) = 0 := by
        by_contra hab
        have hbmem : b ∈ (sndMarginal (fstSndMarginal p)).support := by
          rw [PMF.mem_support_map_iff]
          exact ⟨(a, b), hab, rfl⟩
        exact hbmem hb
      have habc : p (a, b, c) = 0 := by
        by_contra habc
        have hbmem : b ∈ (sndMarginal (fstSndMarginal p)).support := by
          rw [PMF.mem_support_map_iff]
          refine ⟨(a, b), ?_, rfl⟩
          rw [PMF.mem_support_map_iff]
          exact ⟨(a, b, c), habc, rfl⟩
        exact hbmem hb
      rw [hab, habc, zero_mul]
    · have hcancel :
          p (a, b, c) * sndMarginal (fstSndMarginal p) b =
            (fstSndMarginal p (a, b) * condFstGivenSndChannel q b c) *
              sndMarginal (fstSndMarginal p) b := by
        calc
          p (a, b, c) * sndMarginal (fstSndMarginal p) b =
              fstSndMarginal p (a, b) * sndThirdMarginal p (b, c) :=
            hp a b c
          _ = fstSndMarginal p (a, b) *
                (sndMarginal (fstSndMarginal p) b *
                  condFstGivenSndChannel q b c) := by rw [hreconstruct]
          _ = (fstSndMarginal p (a, b) * condFstGivenSndChannel q b c) *
                sndMarginal (fstSndMarginal p) b := by ac_rfl
      have htop : sndMarginal (fstSndMarginal p) b ≠ ⊤ :=
        (sndMarginal (fstSndMarginal p)).apply_ne_top b
      calc
        p (a, b, c) =
            p (a, b, c) * sndMarginal (fstSndMarginal p) b *
              (sndMarginal (fstSndMarginal p) b)⁻¹ :=
          (ENNReal.mul_inv_cancel_right hb htop).symm
        _ = (fstSndMarginal p (a, b) * condFstGivenSndChannel q b c) *
              sndMarginal (fstSndMarginal p) b *
                (sndMarginal (fstSndMarginal p) b)⁻¹ := by rw [hcancel]
        _ = fstSndMarginal p (a, b) * condFstGivenSndChannel q b c :=
          ENNReal.mul_inv_cancel_right hb htop
  · intro hp
    rw [hp]
    exact isMarkovChain_channelExtension _ _

/-- Compatibility alias for reconstruction by the canonical total conditional channel.
@isnad1 id=iff.0h4v.s5.b703dabeb7a5 from=translated src=- shape=e47a2493 vocab=b68e5c94
-/
theorem isMarkovChain_iff_canonical_channelExtension
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    IsMarkovChain p ↔
      p = PMF.channelExtension (fstSndMarginal p)
        (condFstGivenSndChannel ((sndThirdMarginal p).map Prod.swap)) :=
  isMarkovChain_iff_eq_channelExtension_condFstGivenSndChannel p

/--
Textbook channel-factorization characterization of a finite Markov triple: a
law is Markov exactly when some channel from the middle alphabet extends its
first-two marginal to the original triple law.
@isnad1 id=iff.0h4v.s5.465d7d5b1e91 from=translated src=- shape=09eb523e vocab=ebd11a1c
-/
theorem isMarkovChain_iff_exists_channelExtension
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Finite gamma]
    (p : PMF (alpha × beta × gamma)) :
    IsMarkovChain p ↔
      ∃ V : beta → PMF gamma,
        p = PMF.channelExtension (fstSndMarginal p) V := by
  classical
  let := Fintype.ofFinite gamma
  constructor
  · intro hp
    exact ⟨condFstGivenSndChannel ((sndThirdMarginal p).map Prod.swap),
      (isMarkovChain_iff_eq_channelExtension_condFstGivenSndChannel p).mp hp⟩
  · rintro ⟨V, hp⟩
    rw [hp]
    exact isMarkovChain_channelExtension _ _

/-! ## Markov mutual-information identities -/

/--
Exact mutual-information loss along a finite Markov triple:

`I(A;B) = I(A;C) + I(A;B | C)`.

This is the PMF form of the Markov chain rule. The Markov hypothesis removes
the opposite conditional term `I(A;C | B)` from the ordinary chain rule.
@isnad1 id=eq.1h4v.s6.c039ab64539f from=translated src=- shape=6600f218 vocab=b5e9bb7f
-/
theorem mutualInfo_markov_chain_rule
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) (hp : IsMarkovChain p) :
    mutualInfo (fstSndMarginal p) =
      mutualInfo (fstThirdMarginal p) + condMutualInfo p := by
  have hzero :
      condMutualInfoOf p (fun x => x.1) (fun x => x.2.2)
        (fun x => x.2.1) = 0 :=
    (condMutualInfoOf_eq_zero_iff_isMarkovChainOf p
      (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2)).2 hp
  change condMutualInfo (p.map fun x => (x.1, x.2.2, x.2.1)) = 0 at hzero
  calc
    mutualInfo (fstSndMarginal p) = mutualInfo p := by
      rw [mutualInfo_chain_rule_snd, hzero, add_zero]
    _ = mutualInfo (fstThirdMarginal p) + condMutualInfo p :=
      mutualInfo_chain_rule_fst p

/--
Exact mutual-information loss along the finite Markov chain `X → Y → Z`:

`I(X;Y) = I(X;Z) + I(X;Y | Z)`.
@isnad1 id=eq.1h8v.s6.1cf918c7bad3 from=translated src=- shape=0c57c10b vocab=bd2f43e3
-/
theorem mutualInfoOf_markov_chain_rule
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) (hp : IsMarkovChainOf p X Y Z) :
    mutualInfoOf p X Y =
      mutualInfoOf p X Z + condMutualInfoOf p X Y Z := by
  have hzero : condMutualInfoOf p X Z Y = 0 :=
    (condMutualInfoOf_eq_zero_iff_isMarkovChainOf p X Y Z).2 hp
  calc
    mutualInfoOf p X Y =
        mutualInfoOf p X (fun omega => (Y omega, Z omega)) := by
      rw [mutualInfoOf_chain_rule_snd, hzero, add_zero]
    _ = mutualInfoOf p X Z + condMutualInfoOf p X Y Z :=
      mutualInfoOf_chain_rule_fst p X Y Z

/-! ## Mutual-information data processing -/

/--
Mutual-information data processing for a finite Markov triple:

`I(A;C) <= I(A;B)` when `A -> B -> C`.
@isnad1 id=le.1h4v.s5.cd02c6facc78 from=translated src=- shape=a2f5f055 vocab=f22f0840
-/
theorem mutualInfo_dataProcessing
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) (hp : IsMarkovChain p) :
    mutualInfo (fstThirdMarginal p) ≤ mutualInfo (fstSndMarginal p) := by
  rw [mutualInfo_markov_chain_rule p hp]
  exact le_add_of_nonneg_right (condMutualInfo_nonneg p)

/--
Random-variable mutual-information data processing:

`I(X;Z) <= I(X;Y)` when `X -> Y -> Z`.
@isnad1 id=le.1h8v.s5.e23a232c0935 from=translated src=- shape=e37d2ce4 vocab=2b79db29
-/
theorem mutualInfoOf_dataProcessing
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) (hp : IsMarkovChainOf p X Y Z) :
    mutualInfoOf p X Z ≤ mutualInfoOf p X Y := by
  rw [mutualInfoOf_markov_chain_rule p X Y Z hp]
  exact le_add_of_nonneg_right (condMutualInfoOf_nonneg p X Y Z)

/--
Conditional-entropy form of data processing:

`H(X|Y) <= H(X|Z)` when `X -> Y -> Z`.
@isnad1 id=le.1h8v.s5.602e2414d1d3 from=translated src=- shape=8f38564c vocab=ff4ad09d
-/
theorem condEntropyOf_dataProcessing
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) (hp : IsMarkovChainOf p X Y Z) :
    condEntropyOf p X Y ≤ condEntropyOf p X Z := by
  have h := mutualInfoOf_dataProcessing p X Y Z hp
  rw [mutualInfoOf_eq_entropyOf_sub_condEntropyOf,
    mutualInfoOf_eq_entropyOf_sub_condEntropyOf,
    sub_eq_add_neg, sub_eq_add_neg] at h
  have hneg : -condEntropyOf p X Z ≤ -condEntropyOf p X Y :=
    (add_le_add_iff_left (entropyOf p X)).mp h
  exact neg_le_neg_iff.mp hneg

/--
PMF form of the conditional-entropy data-processing consequence:

`H(A|B) <= H(A|C)` when `A -> B -> C`.
@isnad1 id=le.1h4v.s5.0182e90c34c2 from=translated src=- shape=07328b8a vocab=e4aea37a
-/
theorem condEntropy_dataProcessing
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) (hp : IsMarkovChain p) :
    condEntropy (fstSndMarginal p) ≤ condEntropy (fstThirdMarginal p) := by
  change condEntropyOf p (fun x => x.1) (fun x => x.2.1) ≤
    condEntropyOf p (fun x => x.1) (fun x => x.2.2)
  exact condEntropyOf_dataProcessing p _ _ _ hp

/--
Equality in mutual-information data processing holds exactly when the reverse
chain `X -> Z -> Y` is also Markov.
@isnad1 id=iff.1h8v.s6.bcd84f89aa62 from=translated src=- shape=099fe013 vocab=1a82822f
-/
theorem mutualInfoOf_dataProcessing_eq_iff
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) (hp : IsMarkovChainOf p X Y Z) :
    mutualInfoOf p X Z = mutualInfoOf p X Y ↔
      IsMarkovChainOf p X Z Y := by
  rw [mutualInfoOf_markov_chain_rule p X Y Z hp]
  constructor
  · intro h
    have hzero : condMutualInfoOf p X Y Z = 0 := by
      apply add_left_cancel (a := mutualInfoOf p X Z)
      simpa using h.symm
    exact (condMutualInfoOf_eq_zero_iff_isMarkovChainOf p X Z Y).1 hzero
  · intro hreverse
    have hzero : condMutualInfoOf p X Y Z = 0 :=
      (condMutualInfoOf_eq_zero_iff_isMarkovChainOf p X Z Y).2 hreverse
    rw [hzero, add_zero]

/--
For a Markov triple law, equality in mutual-information data processing holds
exactly when its first, third, and second coordinate variables form the reverse
Markov chain.
@isnad1 id=iff.1h4v.s6.fd0b6f117116 from=translated src=- shape=e36f9904 vocab=a0aaef74
-/
theorem mutualInfo_dataProcessing_eq_iff
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) (hp : IsMarkovChain p) :
    mutualInfo (fstThirdMarginal p) = mutualInfo (fstSndMarginal p) ↔
      IsMarkovChainOf p (fun x => x.1) (fun x => x.2.2)
        (fun x => x.2.1) := by
  change mutualInfoOf p (fun x => x.1) (fun x => x.2.2) =
      mutualInfoOf p (fun x => x.1) (fun x => x.2.1) ↔ _
  exact mutualInfoOf_dataProcessing_eq_iff p _ _ _ hp

/--
Under the forward chain `X -> Y -> Z`, equality in conditional-entropy data
processing holds exactly when the reverse chain `X -> Z -> Y` is also Markov.
Equivalently, `X` and `Y` are conditionally independent given `Z`,
`X ⟂ Y | Z`; in this sense, `Z` retains all information about `X` carried by
`Y`.
@isnad1 id=iff.1h8v.s6.e63597cf700f from=translated src=- shape=86e18b01 vocab=9ec7e4bb
-/
theorem condEntropyOf_dataProcessing_eq_iff
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta)
    (Z : omega → gamma) (hp : IsMarkovChainOf p X Y Z) :
    condEntropyOf p X Y = condEntropyOf p X Z ↔
      IsMarkovChainOf p X Z Y := by
  rw [← mutualInfoOf_dataProcessing_eq_iff p X Y Z hp,
    mutualInfoOf_eq_entropyOf_sub_condEntropyOf,
    mutualInfoOf_eq_entropyOf_sub_condEntropyOf,
    sub_right_inj]
  exact eq_comm

/--
For a Markov triple law, equality in conditional-entropy data processing holds
exactly when its first, third, and second coordinate variables form the reverse
Markov chain.
@isnad1 id=iff.1h4v.s6.5847c27d50c8 from=translated src=- shape=357aeff5 vocab=363524bd
-/
theorem condEntropy_dataProcessing_eq_iff
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) (hp : IsMarkovChain p) :
    condEntropy (fstSndMarginal p) = condEntropy (fstThirdMarginal p) ↔
      IsMarkovChainOf p (fun x => x.1) (fun x => x.2.2)
        (fun x => x.2.1) := by
  change condEntropyOf p (fun x => x.1) (fun x => x.2.1) =
      condEntropyOf p (fun x => x.1) (fun x => x.2.2) ↔ _
  exact condEntropyOf_dataProcessing_eq_iff p _ _ _ hp

/-! ## Channel-facing mutual-information processing -/

/--
Applying a channel to the right coordinate of a finite joint law cannot
increase mutual information.
@isnad1 id=le.0h5v.s5.37cbf4fb8d1e from=translated src=- shape=a1feb82c vocab=3fb016cf
-/
theorem mutualInfo_channel_right_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta)) (V : beta → PMF gamma) :
    mutualInfo (fstThirdMarginal (PMF.channelExtension p V)) ≤
      mutualInfo p := by
  simpa using
    mutualInfo_dataProcessing (PMF.channelExtension p V)
      (isMarkovChain_channelExtension p V)

private theorem channel_left_processed_law
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta)) (W : alpha → PMF gamma) :
    (fstThirdMarginal
        (PMF.channelExtension (p.map Prod.swap) W)).map Prod.swap =
      p.bind fun ab => (W ab.1).map fun c => (c, ab.2) := by
  unfold fstThirdMarginal PMF.channelExtension
  rw [PMF.map_comp, PMF.map_bind, PMF.bind_map]
  apply congrArg (PMF.bind p)
  funext ab
  rcases ab with ⟨a, b⟩
  simp only [Function.comp_apply]
  rw [PMF.map_comp]
  rfl

/--
Applying a channel to the left coordinate of a finite joint law cannot
increase mutual information. The displayed bind is the law of the processed
left output paired with the unchanged right coordinate.
@isnad1 id=le.0h5v.s6.701853fe9578 from=translated src=- shape=104c77c3 vocab=68e895f7
-/
theorem mutualInfo_channel_left_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta)) (W : alpha → PMF gamma) :
    mutualInfo (p.bind fun ab => (W ab.1).map fun c => (c, ab.2)) ≤
      mutualInfo p := by
  rw [← channel_left_processed_law]
  calc
    mutualInfo
        ((fstThirdMarginal
          (PMF.channelExtension (p.map Prod.swap) W)).map Prod.swap) =
        mutualInfo
          (fstThirdMarginal (PMF.channelExtension (p.map Prod.swap) W)) :=
      mutualInfo_map_swap _
    _ ≤ mutualInfo (p.map Prod.swap) :=
      mutualInfo_channel_right_le (p.map Prod.swap) W
    _ = mutualInfo p := mutualInfo_map_swap p

private theorem independent_channels_processed_law
    {alpha : Type u} {beta : Type v} {gamma : Type w} {delta : Type x}
    (p : PMF (alpha × beta)) (W : alpha → PMF gamma)
    (V : beta → PMF delta) :
    fstThirdMarginal
        (PMF.channelExtension
          (p.bind fun ab => (W ab.1).map fun c => (c, ab.2)) V) =
      p.bind fun ab => indepProd (W ab.1) (V ab.2) := by
  unfold fstThirdMarginal PMF.channelExtension indepProd
  rw [PMF.map_bind, PMF.bind_bind]
  apply congrArg (PMF.bind p)
  funext ab
  rw [PMF.bind_map]
  apply congrArg (PMF.bind (W ab.1))
  funext c
  simp only [Function.comp_apply]
  rw [PMF.map_comp]
  rfl

/--
Applying independent channels to both coordinates of a finite joint law
cannot increase mutual information. Conditional on an input pair `(a,b)`, the
two channel outputs have law `indepProd (W a) (V b)`.
@isnad1 id=le.0h7v.s6.81be6ed2e779 from=translated src=- shape=5d9369e0 vocab=54846990
-/
theorem mutualInfo_independent_channels_le
    {alpha : Type u} {beta : Type v} {gamma : Type w} {delta : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma] [Fintype delta]
    (p : PMF (alpha × beta)) (W : alpha → PMF gamma)
    (V : beta → PMF delta) :
    mutualInfo (p.bind fun ab => indepProd (W ab.1) (V ab.2)) ≤
      mutualInfo p := by
  let q : PMF (gamma × beta) :=
    p.bind fun ab => (W ab.1).map fun c => (c, ab.2)
  calc
    mutualInfo (p.bind fun ab => indepProd (W ab.1) (V ab.2)) =
        mutualInfo (fstThirdMarginal (PMF.channelExtension q V)) := by
      rw [independent_channels_processed_law]
    _ ≤ mutualInfo q := mutualInfo_channel_right_le q V
    _ ≤ mutualInfo p := mutualInfo_channel_left_le p W

/--
Mutual information contracts along a two-stage finite channel cascade.
@isnad1 id=le.0h6v.s5.f3c3fb329bad from=translated src=- shape=3cc56e61 vocab=fbee4685
-/
theorem mutualInfo_channelComp_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF alpha) (W : alpha → PMF beta) (V : beta → PMF gamma) :
    mutualInfo (PMF.channelJoint p (PMF.channelComp W V)) ≤
      mutualInfo (PMF.channelJoint p W) := by
  simpa using
    mutualInfo_channel_right_le (PMF.channelJoint p W) V

/-- Textbook-facing alias for mutual-information contraction along a channel cascade.
@isnad1 id=le.0h6v.s5.f3c3fb329bad from=translated src=- shape=3cc56e61 vocab=fbee4685
-/
theorem mutualInfo_channel_cascade_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF alpha) (W : alpha → PMF beta) (V : beta → PMF gamma) :
    mutualInfo (PMF.channelJoint p (PMF.channelComp W V)) ≤
      mutualInfo (PMF.channelJoint p W) :=
  mutualInfo_channelComp_le p W V

/--
Deterministically mapping every output law of a finite channel cannot increase
its input-output mutual information.
@isnad1 id=le.0h6v.s5.9c5c99b9aacb from=translated src=- shape=ceb30c8e vocab=bef0058c
-/
theorem mutualInfo_channel_map_output_le
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF alpha) (W : alpha → PMF beta) (f : beta → gamma) :
    mutualInfo (PMF.channelJoint p fun a => (W a).map f) ≤
      mutualInfo (PMF.channelJoint p W) := by
  simpa using
    mutualInfo_channelComp_le p W (PMF.deterministicChannel f)

end

end Shannon
end LeanInfoTheory
