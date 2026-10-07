/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.BinaryEntropy
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.EntropyBounds
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Theorems

/-!
# Decoding error and Fano's inequality

This opt-in module develops the finite-alphabet objects used in Fano's
inequality. A decoding-error indicator is `true` exactly when the decoder
fails to reproduce the source symbol. The basic definitions are type-generic;
finite-alphabet assumptions enter only in later entropy bounds.

The public theorem surface includes:

* expanded and `Real.qaryEntropy` forms of the exact conditional-entropy bound;
* corresponding random-variable forms for finite-valued source and observation
  variables over an arbitrary source sample space;
* the conventional weaker finite-alphabet inequality;
* decoding-error lower bounds; and
* mutual-information and normalized-error corollaries for a uniform source.

All logarithms are natural. The exact and weak entropy forms include singleton
source alphabets; a cardinality lower bound appears only in results that divide
by the logarithm of the source-alphabet size. Coding theorems and equality or
sharpness characterizations are outside this module.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

noncomputable section

universe u v w

/--
The Boolean error indicator for a deterministic decoder.

It is `true` exactly when decoding the observation `y` does not recover the
source symbol `x`. Decidable equality is chosen internally.
-/
noncomputable def decodingErrorIndicator
    {alpha : Type u} {beta : Type v}
    (decoder : beta -> alpha) (x : alpha) (y : beta) : Bool := by
  classical
  exact decide (decoder y ≠ x)

/-- The decoding-error indicator is `true` exactly on decoder failure. -/
@[simp]
theorem decodingErrorIndicator_eq_true_iff
    {alpha : Type u} {beta : Type v}
    (decoder : beta -> alpha) (x : alpha) (y : beta) :
    decodingErrorIndicator decoder x y = true ↔ decoder y ≠ x := by
  classical
  simp [decodingErrorIndicator]

/-- The decoding-error indicator is `false` exactly on decoder success. -/
@[simp]
theorem decodingErrorIndicator_eq_false_iff
    {alpha : Type u} {beta : Type v}
    (decoder : beta -> alpha) (x : alpha) (y : beta) :
    decodingErrorIndicator decoder x y = false ↔ decoder y = x := by
  classical
  simp [decodingErrorIndicator]

/--
The probability that a deterministic decoder fails under a joint law.

The PMF is a joint law of a source symbol and an observation, in that order.
-/
noncomputable def decodingErrorProbability
    {alpha : Type u} {beta : Type v}
    (p : PMF (alpha × beta)) (decoder : beta -> alpha) : Real :=
  (p.map (fun z => decodingErrorIndicator decoder z.1 z.2) true).toReal

/--
The probability that a deterministic decoder fails for random variables.

Here `X` is the source variable, `Y` is the observation, and `decoder` tries
to recover `X` from `Y`.
-/
noncomputable def decodingErrorProbabilityOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) : Real :=
  decodingErrorProbability (p.map fun omega => (X omega, Y omega)) decoder

open scoped Classical in
/--
The decoding-error probability is the total mass of the joint atoms on which
the decoder fails.

This is the main finite-sum elimination theorem for decoding error.
-/
theorem decodingErrorProbability_eq_sum
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) (decoder : beta -> alpha) :
    decodingErrorProbability p decoder =
      ∑ z : alpha × beta, if decoder z.2 ≠ z.1 then (p z).toReal else 0 := by
  classical
  rw [decodingErrorProbability, PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z _hz
    by_cases h : decoder z.2 = z.1
    · simp [decodingErrorIndicator, h]
    · simp [decodingErrorIndicator, h]
  · intro z _hz
    split
    · exact p.apply_ne_top z
    · exact ENNReal.zero_ne_top

/-- A decoding-error probability is nonnegative. -/
theorem decodingErrorProbability_nonneg
    {alpha : Type u} {beta : Type v}
    (p : PMF (alpha × beta)) (decoder : beta -> alpha) :
    0 <= decodingErrorProbability p decoder := by
  unfold decodingErrorProbability
  exact PMF.toReal_nonneg _ true

/-- A decoding-error probability is at most one. -/
theorem decodingErrorProbability_le_one
    {alpha : Type u} {beta : Type v}
    (p : PMF (alpha × beta)) (decoder : beta -> alpha) :
    decodingErrorProbability p decoder <= 1 := by
  unfold decodingErrorProbability
  exact PMF.toReal_le_one _ true

/-- The decoding-error probability of random variables is nonnegative. -/
theorem decodingErrorProbabilityOf_nonneg
    {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) :
    0 <= decodingErrorProbabilityOf p X Y decoder := by
  unfold decodingErrorProbabilityOf
  exact decodingErrorProbability_nonneg _ decoder

/-- The decoding-error probability of random variables is at most one. -/
theorem decodingErrorProbabilityOf_le_one
    {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) :
    decodingErrorProbabilityOf p X Y decoder <= 1 := by
  unfold decodingErrorProbabilityOf
  exact decodingErrorProbability_le_one _ decoder

/--
The entropy, in nats, of the Boolean decoding-error indicator is the binary
entropy of the decoding-error probability.

The indicator is `true` exactly on decoder failure.
-/
theorem entropy_decodingErrorIndicator
    {alpha : Type u} {beta : Type v}
    (p : PMF (alpha × beta)) (decoder : beta -> alpha) :
    entropy (p.map fun z => decodingErrorIndicator decoder z.1 z.2) =
      Real.binEntropy (decodingErrorProbability p decoder) := by
  simpa only [decodingErrorProbability] using
    entropy_bool (p.map fun z => decodingErrorIndicator decoder z.1 z.2)

/--
The entropy, in nats, of a random variable's Boolean decoding-error indicator
is the binary entropy of its decoding-error probability.

Here `X` is the source variable, `Y` is the observation, and `decoder` attempts
to recover `X` from `Y`.
-/
theorem entropyOf_decodingErrorIndicator
    {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) :
    entropyOf p (fun omega => decodingErrorIndicator decoder (X omega) (Y omega)) =
      Real.binEntropy (decodingErrorProbabilityOf p X Y decoder) := by
  have hcomp :
      (fun z : alpha × beta =>
          decodingErrorIndicator decoder z.1 z.2) ∘
          (fun omega => (X omega, Y omega)) =
        (fun omega =>
          decodingErrorIndicator decoder (X omega) (Y omega)) := by
    funext omega
    rfl
  simpa only [entropyOf, decodingErrorProbabilityOf, PMF.map_comp, hcomp] using
    entropy_decodingErrorIndicator
      (p.map fun omega => (X omega, Y omega)) decoder

/--
The conditional chain identity for the deterministic decoding-error
indicator, used internally in the proof of Fano's inequality.
-/
private theorem condEntropyOf_eq_error_add_residual
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) :
    condEntropyOf p X Y =
      condEntropyOf p
          (fun omega => decodingErrorIndicator decoder (X omega) (Y omega)) Y +
        condEntropyOf p X
          (fun omega =>
            (decodingErrorIndicator decoder (X omega) (Y omega), Y omega)) := by
  let E : omega -> Bool :=
    fun omega => decodingErrorIndicator decoder (X omega) (Y omega)
  have hzero :
      condEntropyOf p E (fun omega => (X omega, Y omega)) = 0 := by
    simpa only [E] using
      (condEntropyOf_comp_eq_zero p
        (fun omega => (X omega, Y omega))
        (fun z : alpha × beta =>
          decodingErrorIndicator decoder z.1 z.2))
  have hright := condEntropyOf_pair_chain_rule p E X Y
  have hswap := condEntropyOf_pair_chain_rule_swap p E X Y
  rw [hzero, add_zero] at hright
  simpa only [E] using hright.symm.trans hswap

/--
The joint law of the source together with its decoding-error indicator and
observation, used internally by the conditional-fiber proof.
-/
private noncomputable def decodingErrorAugmentedLaw
    {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) : PMF (alpha × (Bool × beta)) :=
  p.map fun omega =>
    (X omega,
      (decodingErrorIndicator decoder (X omega) (Y omega), Y omega))

/--
The no-error fiber of the augmented law has zero entropy, including when the
conditioning atom itself has zero mass.
-/
private theorem condEntropyFstGivenSnd_decodingError_false_eq_zero
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) (y : beta) :
    condEntropyFstGivenSnd
        (decodingErrorAugmentedLaw p X Y decoder) (false, y) = 0 := by
  let q := decodingErrorAugmentedLaw p X Y decoder
  by_cases hfiber : sndMarginal q (false, y) = 0
  · exact condEntropyFstGivenSnd_of_sndMarginal_eq_zero q hfiber
  · apply
      (condEntropyFstGivenSnd_eq_zero_iff_of_sndMarginal_ne_zero
        q hfiber).2
    refine ⟨decoder y, ?_⟩
    apply
      (PMF.eq_pure_iff_support_eq_singleton
        (condFstGivenSnd q (false, y) hfiber) (decoder y)).2
    have hsubset :
        (condFstGivenSnd q (false, y) hfiber).support ⊆
          ({decoder y} : Set alpha) := by
      intro a ha
      have hcond_ne : condFstGivenSnd q (false, y) hfiber a ≠ 0 :=
        (PMF.mem_support_iff (condFstGivenSnd q (false, y) hfiber) a).1 ha
      have hq_ne : q (a, (false, y)) ≠ 0 :=
        (condFstGivenSnd_apply_ne_zero_iff
          q (false, y) hfiber a).1 hcond_ne
      have hq_mem : (a, (false, y)) ∈ q.support :=
        (PMF.mem_support_iff q (a, (false, y))).2 hq_ne
      dsimp only [q, decodingErrorAugmentedLaw] at hq_mem
      rw [PMF.mem_support_map_iff] at hq_mem
      obtain ⟨omega, _homega, hmap⟩ := hq_mem
      have hX : X omega = a :=
        congrArg (fun z : alpha × (Bool × beta) => z.1) hmap
      have herror :
          decodingErrorIndicator decoder (X omega) (Y omega) = false :=
        congrArg (fun z : alpha × (Bool × beta) => z.2.1) hmap
      have hY : Y omega = y :=
        congrArg (fun z : alpha × (Bool × beta) => z.2.2) hmap
      have hdecode : decoder (Y omega) = X omega :=
        (decodingErrorIndicator_eq_false_iff
          decoder (X omega) (Y omega)).1 herror
      exact Set.mem_singleton_iff.2 (by
        calc
          a = X omega := hX.symm
          _ = decoder (Y omega) := hdecode.symm
          _ = decoder y := congrArg decoder hY)
    apply Set.Subset.antisymm hsubset
    intro a ha
    have ha_eq : a = decoder y := Set.mem_singleton_iff.1 ha
    subst a
    obtain ⟨a, ha⟩ :=
      (condFstGivenSnd q (false, y) hfiber).support_nonempty
    have ha_eq : a = decoder y :=
      Set.mem_singleton_iff.1 (hsubset ha)
    simpa only [ha_eq] using ha

/--
On a positive-mass true-error fiber, the conditional source support excludes
the decoder output.
-/
private theorem decodingError_true_fiber_support_subset
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) (y : beta)
    (hfiber :
      sndMarginal (decodingErrorAugmentedLaw p X Y decoder) (true, y) ≠ 0) :
    (condFstGivenSnd
        (decodingErrorAugmentedLaw p X Y decoder)
        (true, y) hfiber).support ⊆
      ({decoder y} : Set alpha)ᶜ := by
  intro a ha
  have hcond_ne :
      condFstGivenSnd
          (decodingErrorAugmentedLaw p X Y decoder)
          (true, y) hfiber a ≠ 0 :=
    (PMF.mem_support_iff
      (condFstGivenSnd
        (decodingErrorAugmentedLaw p X Y decoder)
        (true, y) hfiber) a).1 ha
  have hq_ne :
      decodingErrorAugmentedLaw p X Y decoder (a, (true, y)) ≠ 0 :=
    (condFstGivenSnd_apply_ne_zero_iff
      (decodingErrorAugmentedLaw p X Y decoder)
      (true, y) hfiber a).1 hcond_ne
  have hq_mem :
      (a, (true, y)) ∈
        (decodingErrorAugmentedLaw p X Y decoder).support :=
    (PMF.mem_support_iff
      (decodingErrorAugmentedLaw p X Y decoder)
      (a, (true, y))).2 hq_ne
  dsimp only [decodingErrorAugmentedLaw] at hq_mem
  rw [PMF.mem_support_map_iff] at hq_mem
  obtain ⟨omega, _homega, hmap⟩ := hq_mem
  have hX : X omega = a :=
    congrArg (fun z : alpha × (Bool × beta) => z.1) hmap
  have herror :
      decodingErrorIndicator decoder (X omega) (Y omega) = true :=
    congrArg (fun z : alpha × (Bool × beta) => z.2.1) hmap
  have hY : Y omega = y :=
    congrArg (fun z : alpha × (Bool × beta) => z.2.2) hmap
  have hdecode : decoder (Y omega) ≠ X omega :=
    (decodingErrorIndicator_eq_true_iff
      decoder (X omega) (Y omega)).1 herror
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro ha_decoder
  apply hdecode
  calc
    decoder (Y omega) = decoder y := congrArg decoder hY
    _ = a := ha_decoder.symm
    _ = X omega := hX.symm

/--
Each total true-error conditional fiber is bounded by the logarithm of the
source alphabet with the decoder output removed.

The Nat subtraction is intentional. On a singleton source alphabet the true
fiber has zero mass and both sides reduce to zero.
-/
private theorem decodingError_true_fiber_entropy_le
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) (y : beta) :
    condEntropyFstGivenSnd
        (decodingErrorAugmentedLaw p X Y decoder) (true, y) ≤
      Real.log ((Fintype.card alpha - 1 : Nat) : Real) := by
  let q := decodingErrorAugmentedLaw p X Y decoder
  change
    condEntropyFstGivenSnd q (true, y) ≤
      Real.log ((Fintype.card alpha - 1 : Nat) : Real)
  have hcard_pos : 0 < Fintype.card alpha :=
    Fintype.card_pos_iff.mpr ⟨decoder y⟩
  have hlog_nonneg :
      0 ≤ Real.log ((Fintype.card alpha - 1 : Nat) : Real) := by
    by_cases hcard_one : Fintype.card alpha = 1
    · simp [hcard_one]
    · have hcard_two : 2 ≤ Fintype.card alpha := by omega
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ Fintype.card alpha - 1 by omega)
  by_cases hfiber : sndMarginal q (true, y) = 0
  · rw [condEntropyFstGivenSnd_of_sndMarginal_eq_zero q hfiber]
    exact hlog_nonneg
  · rw [condEntropyFstGivenSnd_of_sndMarginal_ne_zero q hfiber]
    have hsupport :
        (condFstGivenSnd q (true, y) hfiber).support ⊆
          ({decoder y} : Set alpha)ᶜ := by
      simpa only [q] using
        (decodingError_true_fiber_support_subset
          p X Y decoder y hfiber)
    have hcompl_ncard :
        (({decoder y} : Set alpha)ᶜ).ncard =
          Fintype.card alpha - 1 := by
      rw [Set.ncard_compl, Set.ncard_singleton,
        Nat.card_eq_fintype_card]
    have hncard :
        (condFstGivenSnd q (true, y) hfiber).support.ncard ≤
          Fintype.card alpha - 1 := by
      calc
        (condFstGivenSnd q (true, y) hfiber).support.ncard ≤
            (({decoder y} : Set alpha)ᶜ).ncard :=
          Set.ncard_le_ncard hsupport
        _ = Fintype.card alpha - 1 := hcompl_ncard
    have hsupport_pos_nat :
        0 < (condFstGivenSnd q (true, y) hfiber).support.ncard :=
      (Set.ncard_pos).2
        (condFstGivenSnd q (true, y) hfiber).support_nonempty
    have hsupport_pos_real :
        0 <
          ((condFstGivenSnd q (true, y) hfiber).support.ncard : Real) := by
      exact_mod_cast hsupport_pos_nat
    have hncard_real :
        ((condFstGivenSnd q (true, y) hfiber).support.ncard : Real) ≤
          ((Fintype.card alpha - 1 : Nat) : Real) := by
      exact_mod_cast hncard
    calc
      entropy (condFstGivenSnd q (true, y) hfiber) ≤
          Real.log
            ((condFstGivenSnd q (true, y) hfiber).support.ncard : Real) :=
        entropy_le_log_support_ncard _
      _ ≤ Real.log ((Fintype.card alpha - 1 : Nat) : Real) :=
        Real.log_le_log hsupport_pos_real hncard_real

/--
The residual conditional entropy after adjoining the decoding-error indicator
is bounded by the true-error probability times the logarithm of the remaining
source-alphabet size.
-/
private theorem condEntropyOf_decodingError_residual_le
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) :
    condEntropyOf p X
        (fun omega =>
          (decodingErrorIndicator decoder (X omega) (Y omega), Y omega)) ≤
      decodingErrorProbabilityOf p X Y decoder *
        Real.log ((Fintype.card alpha - 1 : Nat) : Real) := by
  let q := decodingErrorAugmentedLaw p X Y decoder
  let L : Real := Real.log ((Fintype.card alpha - 1 : Nat) : Real)
  change
    condEntropy q ≤
      decodingErrorProbabilityOf p X Y decoder * L
  have hfalse_fiber (y : beta) :
      condEntropyFstGivenSnd q (false, y) = 0 := by
    simpa only [q] using
      (condEntropyFstGivenSnd_decodingError_false_eq_zero
        p X Y decoder y)
  have htrue_fiber (y : beta) :
      condEntropyFstGivenSnd q (true, y) ≤ L := by
    simpa only [q, L] using
      (decodingError_true_fiber_entropy_le p X Y decoder y)
  have herrorLaw :
      fstMarginal (sndMarginal q) =
        p.map (fun omega =>
          decodingErrorIndicator decoder (X omega) (Y omega)) := by
    dsimp only [q, decodingErrorAugmentedLaw]
    rw [sndMarginal_map_pair, fstMarginal_map_pair]
  have hweight_ennreal :
      (∑ y : beta, sndMarginal q (true, y)) =
        (p.map fun omega =>
          decodingErrorIndicator decoder (X omega) (Y omega)) true := by
    calc
      (∑ y : beta, sndMarginal q (true, y)) =
          fstMarginal (sndMarginal q) true :=
        (fstMarginal_apply (sndMarginal q) true).symm
      _ =
          (p.map fun omega =>
            decodingErrorIndicator decoder (X omega) (Y omega)) true := by
        rw [herrorLaw]
  have hfinite :
      ∀ y ∈ (Finset.univ : Finset beta),
        sndMarginal q (true, y) ≠ ⊤ := by
    intro y _hy
    exact (sndMarginal q).apply_ne_top (true, y)
  have hweight_real :
      (∑ y : beta, (sndMarginal q (true, y)).toReal) =
        decodingErrorProbabilityOf p X Y decoder := by
    calc
      (∑ y : beta, (sndMarginal q (true, y)).toReal) =
          (∑ y : beta, sndMarginal q (true, y)).toReal := by
        simpa using
          (ENNReal.toReal_sum
            (s := Finset.univ)
            (f := fun y : beta => sndMarginal q (true, y))
            hfinite).symm
      _ =
          ((p.map fun omega =>
            decodingErrorIndicator decoder (X omega) (Y omega)) true).toReal :=
        congrArg ENNReal.toReal hweight_ennreal
      _ = decodingErrorProbabilityOf p X Y decoder := by
        unfold decodingErrorProbabilityOf decodingErrorProbability
        have hmap :
            (p.map fun omega =>
              decodingErrorIndicator decoder (X omega) (Y omega)) =
              (p.map fun omega => (X omega, Y omega)).map
                (fun z : alpha × beta =>
                  decodingErrorIndicator decoder z.1 z.2) := by
          simpa [Function.comp_def] using
            (PMF.map_comp
              (p := p)
              (f := fun omega => (X omega, Y omega))
              (g := fun z : alpha × beta =>
                decodingErrorIndicator decoder z.1 z.2)).symm
        rw [hmap]
  rw [condEntropy_eq_sum_sndMarginal_mul_condEntropyFstGivenSnd,
    Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [hfalse_fiber, mul_zero, Finset.sum_const_zero, add_zero]
  calc
    (∑ y : beta,
        (sndMarginal q (true, y)).toReal *
          condEntropyFstGivenSnd q (true, y)) ≤
        ∑ y : beta, (sndMarginal q (true, y)).toReal * L := by
      apply Finset.sum_le_sum
      intro y _hy
      exact
        mul_le_mul_of_nonneg_left
          (htrue_fiber y)
          (PMF.toReal_nonneg (sndMarginal q) (true, y))
    _ = (∑ y : beta, (sndMarginal q (true, y)).toReal) * L := by
      rw [Finset.sum_mul]
    _ = decodingErrorProbabilityOf p X Y decoder * L := by
      rw [hweight_real]

private theorem qaryEntropy_eq_binEntropy_add_mul_log_nat_sub_one
    (q : Nat) (x : Real) :
    Real.qaryEntropy q x =
      Real.binEntropy x + x * Real.log ((q - 1 : Nat) : Real) := by
  by_cases hq : q = 0
  · subst q
    simp [Real.qaryEntropy]
  · have hq_one : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
    have hcast :
        (((q : Int) - 1 : Int) : Real) = ((q - 1 : Nat) : Real) := by
      push_cast
      rw [Nat.cast_sub hq_one]
      norm_num
    rw [Real.qaryEntropy, hcast]
    ring

/--
Fano's inequality for a finite joint law and a deterministic decoder, in nats.

Here the first coordinate is the source, the second coordinate is the
observation, and `decoder` attempts to recover the source from the observation.
The decoding-error indicator is `true` exactly when decoding fails. No lower
bound on the source-alphabet cardinality is required; in particular, the
singleton case is included.
-/
theorem condEntropy_fano
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) (decoder : beta -> alpha) :
    condEntropy p ≤
      Real.binEntropy (decodingErrorProbability p decoder) +
        decodingErrorProbability p decoder *
          Real.log ((Fintype.card alpha - 1 : Nat) : Real) := by
  have hprob :
      decodingErrorProbabilityOf p Prod.fst Prod.snd decoder =
        decodingErrorProbability p decoder := by
    unfold decodingErrorProbabilityOf
    rw [show
      (fun z : alpha × beta => (Prod.fst z, Prod.snd z)) = id by
        funext z
        cases z
        rfl]
    simp only [PMF.map_id]
  calc
    condEntropy p = condEntropyOf p Prod.fst Prod.snd :=
      (condEntropyOf_fst_snd p).symm
    _ =
        condEntropyOf p
            (fun z : alpha × beta =>
              decodingErrorIndicator decoder z.1 z.2) Prod.snd +
          condEntropyOf p Prod.fst
            (fun z : alpha × beta =>
              (decodingErrorIndicator decoder z.1 z.2, z.2)) :=
      condEntropyOf_eq_error_add_residual
        p Prod.fst Prod.snd decoder
    _ ≤
        entropyOf p
            (fun z : alpha × beta =>
              decodingErrorIndicator decoder z.1 z.2) +
          decodingErrorProbabilityOf p Prod.fst Prod.snd decoder *
            Real.log ((Fintype.card alpha - 1 : Nat) : Real) :=
      add_le_add
        (condEntropyOf_le_entropyOf p
          (fun z : alpha × beta =>
            decodingErrorIndicator decoder z.1 z.2)
          Prod.snd)
        (condEntropyOf_decodingError_residual_le
          p Prod.fst Prod.snd decoder)
    _ =
        Real.binEntropy (decodingErrorProbability p decoder) +
          decodingErrorProbability p decoder *
            Real.log ((Fintype.card alpha - 1 : Nat) : Real) := by
      rw [entropyOf_decodingErrorIndicator, hprob]

/--
Fano's inequality for a finite joint law, expressed with mathlib's
`Real.qaryEntropy`, in nats.

The error convention and decoder direction are the same as in
`condEntropy_fano`. This form is valid without a lower bound on the source
alphabet cardinality.
-/
theorem condEntropy_fano_qary
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) (decoder : beta -> alpha) :
    condEntropy p ≤
      Real.qaryEntropy
        (Fintype.card alpha) (decodingErrorProbability p decoder) := by
  calc
    condEntropy p ≤
        Real.binEntropy (decodingErrorProbability p decoder) +
          decodingErrorProbability p decoder *
            Real.log ((Fintype.card alpha - 1 : Nat) : Real) :=
      condEntropy_fano p decoder
    _ =
        Real.qaryEntropy
          (Fintype.card alpha) (decodingErrorProbability p decoder) :=
      (qaryEntropy_eq_binEntropy_add_mul_log_nat_sub_one
        (Fintype.card alpha)
        (decodingErrorProbability p decoder)).symm

/--
The random-variable form of `condEntropy_fano`, in nats.

Here `X` is the finite source variable, `Y` is the finite observation, and
`decoder` attempts to recover `X` from `Y`. The error indicator is `true`
exactly when decoding fails. The source sample space itself need not be finite.
-/
theorem condEntropyOf_fano
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) :
    condEntropyOf p X Y ≤
      Real.binEntropy (decodingErrorProbabilityOf p X Y decoder) +
        decodingErrorProbabilityOf p X Y decoder *
          Real.log ((Fintype.card alpha - 1 : Nat) : Real) := by
  simpa only [condEntropyOf, decodingErrorProbabilityOf] using
    condEntropy_fano
      (p.map fun omega => (X omega, Y omega)) decoder

/--
The random-variable form of `condEntropy_fano_qary`, in nats.

The decoder direction and error convention are those of `condEntropyOf_fano`.
Only the value alphabets of `X` and `Y` must be finite.
-/
theorem condEntropyOf_fano_qary
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) :
    condEntropyOf p X Y ≤
      Real.qaryEntropy
        (Fintype.card alpha)
        (decodingErrorProbabilityOf p X Y decoder) := by
  simpa only [condEntropyOf, decodingErrorProbabilityOf] using
    condEntropy_fano_qary
      (p.map fun omega => (X omega, Y omega)) decoder

/--
The conventional weaker form of Fano's inequality for a finite joint law:

`H(X | Y) <= log 2 + Pe * log |alpha|`.

All logarithms are natural, so `log 2` is the one-bit textbook constant
expressed in nats. No lower bound on the source-alphabet cardinality is
required.
-/
theorem condEntropy_fano_weak
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) (decoder : beta -> alpha) :
    condEntropy p ≤
      Real.log 2 +
        decodingErrorProbability p decoder *
          Real.log (Fintype.card alpha : Real) := by
  have hcard_pos : 0 < Fintype.card alpha := by
    obtain ⟨z, _hz⟩ := p.support_nonempty
    exact Fintype.card_pos_iff.mpr ⟨z.1⟩
  have hlog :
      Real.log ((Fintype.card alpha - 1 : Nat) : Real) ≤
        Real.log (Fintype.card alpha : Real) := by
    by_cases hcard_one : Fintype.card alpha = 1
    · simp [hcard_one]
    · have hcard_two : 2 ≤ Fintype.card alpha := by omega
      have hsub_pos : 0 < Fintype.card alpha - 1 := by omega
      have hsub_le :
          Fintype.card alpha - 1 ≤ Fintype.card alpha :=
        Nat.sub_le _ _
      exact
        Real.log_le_log
          (by exact_mod_cast hsub_pos)
          (by exact_mod_cast hsub_le)
  calc
    condEntropy p ≤
        Real.binEntropy (decodingErrorProbability p decoder) +
          decodingErrorProbability p decoder *
            Real.log ((Fintype.card alpha - 1 : Nat) : Real) :=
      condEntropy_fano p decoder
    _ ≤
        Real.log 2 +
          decodingErrorProbability p decoder *
            Real.log (Fintype.card alpha : Real) :=
      add_le_add
        Real.binEntropy_le_log_two
        (mul_le_mul_of_nonneg_left hlog
          (decodingErrorProbability_nonneg p decoder))

/--
The random-variable form of `condEntropy_fano_weak`, in nats.

Only the finite value alphabets of `X` and `Y` are required; the source sample
space may be arbitrary.
-/
theorem condEntropyOf_fano_weak
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha) :
    condEntropyOf p X Y ≤
      Real.log 2 +
        decodingErrorProbabilityOf p X Y decoder *
          Real.log (Fintype.card alpha : Real) := by
  simpa only [condEntropyOf, decodingErrorProbabilityOf] using
    condEntropy_fano_weak
      (p.map fun omega => (X omega, Y omega)) decoder

/--
Fano's lower bound on the decoding-error probability for a finite joint law:

`(H(X | Y) - log 2) / log |alpha| <= Pe`.

The hypothesis `2 <= |alpha|` is needed here, unlike in the entropy forms of
Fano's inequality, because it makes the logarithmic denominator strictly
positive.
-/
theorem decodingErrorProbability_fano_lower_bound
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) (decoder : beta -> alpha)
    (hcard : 2 ≤ Fintype.card alpha) :
    (condEntropy p - Real.log 2) /
        Real.log (Fintype.card alpha : Real) ≤
      decodingErrorProbability p decoder := by
  have hcard_real :
      (1 : Real) < (Fintype.card alpha : Real) := by
    exact_mod_cast (show 1 < Fintype.card alpha by omega)
  have hlog_pos :
      0 < Real.log (Fintype.card alpha : Real) :=
    Real.log_pos hcard_real
  apply (div_le_iff₀ hlog_pos).2
  linarith [condEntropy_fano_weak p decoder]

/--
The random-variable form of
`decodingErrorProbability_fano_lower_bound`.

Only the finite value alphabets of `X` and `Y` are required. The source sample
space may be arbitrary.
-/
theorem decodingErrorProbabilityOf_fano_lower_bound
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha)
    (hcard : 2 ≤ Fintype.card alpha) :
    (condEntropyOf p X Y - Real.log 2) /
        Real.log (Fintype.card alpha : Real) ≤
      decodingErrorProbabilityOf p X Y decoder := by
  simpa only [condEntropyOf, decodingErrorProbabilityOf] using
    decodingErrorProbability_fano_lower_bound
      (p.map fun omega => (X omega, Y omega)) decoder hcard

private theorem mutualInfo_eq_log_card_sub_condEntropy_of_uniform_source
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] [Nonempty alpha]
    (p : PMF (alpha × beta))
    (huniform :
      fstMarginal p = PMF.uniformOfFintype alpha) :
    mutualInfo p =
      Real.log (Fintype.card alpha : Real) - condEntropy p := by
  calc
    mutualInfo p =
        entropy (fstMarginal p) - condEntropy p :=
      mutualInfo_eq_entropy_fstMarginal_sub_condEntropy p
    _ =
        Real.log (Fintype.card alpha : Real) - condEntropy p := by
      rw [huniform, entropy_uniformOfFintype]

/--
Fano's mutual-information lower bound for a uniform finite source, in nats:

`log |alpha| - log 2 - Pe * log |alpha| <= I(X;Y)`.

The first marginal of the supplied joint law is the source law. No cardinality
lower bound is needed because this theorem does not divide by `log |alpha|`.
-/
theorem mutualInfo_fano_lower_bound_of_uniform_source
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] [Nonempty alpha]
    (p : PMF (alpha × beta)) (decoder : beta -> alpha)
    (huniform :
      fstMarginal p = PMF.uniformOfFintype alpha) :
    Real.log (Fintype.card alpha : Real) - Real.log 2 -
        decodingErrorProbability p decoder *
          Real.log (Fintype.card alpha : Real) ≤
      mutualInfo p := by
  have hmi :=
    mutualInfo_eq_log_card_sub_condEntropy_of_uniform_source p huniform
  linarith [condEntropy_fano_weak p decoder]

/--
The random-variable form of
`mutualInfo_fano_lower_bound_of_uniform_source`.

Uniformity is stated through the existing pushforward-law equality
`p.map X = PMF.uniformOfFintype alpha`.
-/
theorem mutualInfoOf_fano_lower_bound_of_uniform_source
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta] [Nonempty alpha]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha)
    (huniform :
      p.map X = PMF.uniformOfFintype alpha) :
    Real.log (Fintype.card alpha : Real) - Real.log 2 -
        decodingErrorProbabilityOf p X Y decoder *
          Real.log (Fintype.card alpha : Real) ≤
      mutualInfoOf p X Y := by
  have hfst :
      fstMarginal (p.map fun omega => (X omega, Y omega)) =
        PMF.uniformOfFintype alpha := by
    rw [fstMarginal_map_pair]
    exact huniform
  simpa only [mutualInfoOf, decodingErrorProbabilityOf] using
    mutualInfo_fano_lower_bound_of_uniform_source
      (p.map fun omega => (X omega, Y omega)) decoder hfst

/--
The standard uniform-source Fano lower bound on decoding error, in nats:

`1 - (I(X;Y) + log 2) / log |alpha| <= Pe`.

The hypothesis `2 <= |alpha|` makes the logarithmic denominator strictly
positive. Uniformity is expressed by equality of the first marginal with the
existing finite uniform PMF.
-/
theorem decodingErrorProbability_fano_lower_bound_of_uniform_source
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] [Nonempty alpha]
    (p : PMF (alpha × beta)) (decoder : beta -> alpha)
    (huniform :
      fstMarginal p = PMF.uniformOfFintype alpha)
    (hcard : 2 ≤ Fintype.card alpha) :
    1 -
        (mutualInfo p + Real.log 2) /
          Real.log (Fintype.card alpha : Real) ≤
      decodingErrorProbability p decoder := by
  have hmi :=
    mutualInfo_eq_log_card_sub_condEntropy_of_uniform_source p huniform
  have hcard_real :
      (1 : Real) < (Fintype.card alpha : Real) := by
    exact_mod_cast (show 1 < Fintype.card alpha by omega)
  have hlog_pos :
      0 < Real.log (Fintype.card alpha : Real) :=
    Real.log_pos hcard_real
  calc
    1 -
        (mutualInfo p + Real.log 2) /
          Real.log (Fintype.card alpha : Real) =
        (condEntropy p - Real.log 2) /
          Real.log (Fintype.card alpha : Real) := by
      rw [hmi]
      field_simp [hlog_pos.ne']; ring
    _ ≤ decodingErrorProbability p decoder :=
      decodingErrorProbability_fano_lower_bound p decoder hcard

/--
The random-variable form of
`decodingErrorProbability_fano_lower_bound_of_uniform_source`.

The sample space may be arbitrary; only the source and observation value
alphabets are finite.
-/
theorem decodingErrorProbabilityOf_fano_lower_bound_of_uniform_source
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta] [Nonempty alpha]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta)
    (decoder : beta -> alpha)
    (huniform :
      p.map X = PMF.uniformOfFintype alpha)
    (hcard : 2 ≤ Fintype.card alpha) :
    1 -
        (mutualInfoOf p X Y + Real.log 2) /
          Real.log (Fintype.card alpha : Real) ≤
      decodingErrorProbabilityOf p X Y decoder := by
  have hfst :
      fstMarginal (p.map fun omega => (X omega, Y omega)) =
        PMF.uniformOfFintype alpha := by
    rw [fstMarginal_map_pair]
    exact huniform
  simpa only [mutualInfoOf, decodingErrorProbabilityOf] using
    decodingErrorProbability_fano_lower_bound_of_uniform_source
      (p.map fun omega => (X omega, Y omega)) decoder hfst hcard

end

end Shannon
end LeanInfoTheory
