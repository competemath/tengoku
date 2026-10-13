/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.FiniteEnsemble.Defs
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal

/-!
# Finite uniform-seed distribution ensembles

This module exposes exact distributions generated from arbitrary nonempty finite
uniform seed spaces. It generalizes dyadic ensembles while preserving sampler
multiplicity, and provides probability laws, pushforwards, products, point
masses, normalization, and an exact dyadic-to-finite bridge.
-/

public section

universe u v w

namespace Complexity

/-- Uniform finite-event probabilities are nonnegative.
@isnad1 id=le.0h2v.s4.7b0e44b3e903 from=translated src=- shape=38fc717e vocab=dc1eab13
-/
theorem uniformProbability_nonneg {Ω : Type u} [Fintype Ω]
    (event : Finset Ω) :
    0 ≤ uniformProbability event :=
  uniformProbability_nonneg_internal event

/-- Uniform finite-event probabilities are at most one in a nonempty sample
space.
@isnad1 id=le.0h2v.s4.8bfa38b67f45 from=translated src=- shape=f686e912 vocab=14877a98
-/
theorem uniformProbability_le_one {Ω : Type u}
    [Fintype Ω] [Nonempty Ω] (event : Finset Ω) :
    uniformProbability event ≤ 1 :=
  uniformProbability_le_one_internal event

/-- The empty event has uniform probability zero.
@isnad1 id=eq.0h1v.s4.17694a60e324 from=translated src=- shape=bba61b78 vocab=21b4fdae
-/
@[simp] theorem uniformProbability_empty {Ω : Type u} [Fintype Ω] :
    uniformProbability (∅ : Finset Ω) = 0 :=
  uniformProbability_empty_internal

/-- The entire nonempty sample space has uniform probability one.
@isnad1 id=eq.0h1v.s4.2e142737d99c from=translated src=- shape=1e8b59d0 vocab=dc166ca9
-/
@[simp] theorem uniformProbability_univ {Ω : Type u}
    [Fintype Ω] [Nonempty Ω] :
    uniformProbability (Finset.univ : Finset Ω) = 1 :=
  uniformProbability_univ_internal

/-- Uniform probability of a complement is one minus the original
probability.
@isnad1 id=eq.0h2v.s5.3e462f9ca35b from=translated src=- shape=672dec26 vocab=44a7b6dc
-/
theorem uniformProbability_compl {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] (event : Finset Ω) :
    uniformProbability eventᶜ = 1 - uniformProbability event :=
  uniformProbability_compl_internal event

/-- Union bound for arbitrary finite uniform sample spaces.
@isnad1 id=le.0h3v.s5.08f72f12fdcc from=translated src=- shape=eb60f9bb vocab=b6c9266c
-/
theorem uniformProbability_union_le {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (event₁ event₂ : Finset Ω) :
    uniformProbability (event₁ ∪ event₂) ≤
      uniformProbability event₁ + uniformProbability event₂ :=
  uniformProbability_union_le_internal event₁ event₂

/-- Conditioning by a finite partition of a uniform sample space.
@isnad1 id=eq.1h5v.s6.52f1c1ef3df1 from=translated src=- shape=c775d109 vocab=c53f4567
-/
theorem uniformProbability_eq_sum_fiberwise
    {Ω : Type u} {ι : Type v} [Fintype Ω]
    [DecidableEq ι] (event : Finset Ω) (indices : Finset ι) (f : Ω → ι)
    (hmaps : (event : Set Ω).MapsTo f indices) :
    uniformProbability event =
      ∑ i ∈ indices,
        uniformProbability (event.filter fun seed => f seed = i) :=
  uniformProbability_eq_sum_fiberwise_internal event indices f hmaps

/-- Independent finite uniform seeds multiply event probabilities.
@isnad1 id=eq.0h4v.s6.e0dbf5048bb9 from=translated src=- shape=0df4a00d vocab=c1838c89
-/
theorem uniformProbability_product
    {Ω : Type u} {Ξ : Type v} [Fintype Ω]
    [Fintype Ξ] (P : Ω → Prop) (Q : Ξ → Prop)
    [DecidablePred P] [DecidablePred Q] :
    uniformProbability
        (Finset.univ.filter fun seed : Ω × Ξ => P seed.1 ∧ Q seed.2) =
      uniformProbability (Finset.univ.filter P) *
      uniformProbability (Finset.univ.filter Q) :=
  uniformProbability_product_internal P Q

/-- Uniform probability on a product is the average of its conditional fiber
probabilities over the first coordinate.
@isnad1 id=eq.0h3v.s6.ff6b36ec0c1c from=translated src=- shape=7a74fb98 vocab=520d8c4f
-/
theorem uniformProbability_product_eq_average_fibers
    {advice : Type u} {challenge : Type v}
    [Fintype advice] [Nonempty advice]
    [Fintype challenge] [Nonempty challenge]
    (event : advice → challenge → Prop)
    [∀ fixed, DecidablePred (event fixed)] :
    uniformProbability (Finset.univ.filter fun sample : advice × challenge =>
        event sample.1 sample.2) =
      (∑ fixed : advice,
        uniformProbability (Finset.univ.filter (event fixed))) /
        Fintype.card advice :=
  uniformProbability_product_eq_average_fibers_internal event

/-- Some first-coordinate fiber has probability at least the joint product
probability.
@isnad1 id=ex.0h3v.s6.5a57133b0857 from=translated src=- shape=7b3f2064 vocab=7acb8728
-/
theorem exists_fiber_uniformProbability_ge
    {advice : Type u} {challenge : Type v}
    [Fintype advice] [Nonempty advice]
    [Fintype challenge] [Nonempty challenge]
    (event : advice → challenge → Prop)
    [∀ fixed, DecidablePred (event fixed)] :
    ∃ fixed : advice,
      uniformProbability (Finset.univ.filter fun sample : advice × challenge =>
          event sample.1 sample.2) ≤
        uniformProbability (Finset.univ.filter (event fixed)) :=
  exists_fiber_uniformProbability_ge_internal event

/-- If a finite statistic is at most one, its mean is bounded by a threshold
plus the probability of exceeding that threshold times the remaining range.
@isnad1 id=le.1h3v.s6.db95fe52d448 from=translated src=- shape=54e194b2 vocab=ba4b40bd
-/
theorem uniformMean_le_threshold_add_probability
    {sample : Type u} [Fintype sample]
    [Nonempty sample] (value : sample → ℚ) (threshold : ℚ)
    (hupper : ∀ input, value input ≤ 1) :
    uniformMean value ≤ threshold +
      uniformProbability (Finset.univ.filter fun input =>
        threshold ≤ value input) * (1 - threshold) :=
  uniformMean_le_threshold_add_probability_internal value threshold hupper

/-- Exact reverse averaging bound for a statistic bounded above by one.
@isnad1 id=le.3h4v.s6.15e6c73641a4 from=translated src=- shape=815ca6f3 vocab=f56f27b4
-/
theorem uniformMean_sub_div_le_probability_ge
    {sample : Type u} [Fintype sample]
    [Nonempty sample] (value : sample → ℚ) (lower threshold : ℚ)
    (hupper : ∀ input, value input ≤ 1)
    (hlower : lower ≤ uniformMean value) (hthreshold : threshold < 1) :
    (lower - threshold) / (1 - threshold) ≤
      uniformProbability (Finset.univ.filter fun input =>
        threshold ≤ value input) :=
  uniformMean_sub_div_le_probability_ge_internal
    value lower threshold hupper hlower hthreshold

/-- Hirahara's convenient half-advantage corollary: mean at least
`1/2 + ε` forces an `ε/2` fraction of samples to have value at least
`1/2 + ε/2`.
@isnad1 id=le.3h3v.s7.3478f9e2d911 from=translated src=- shape=50fd510e vocab=fff08c84
-/
theorem half_epsilon_le_probability_ge_of_le_uniformMean
    {sample : Type u} [Fintype sample]
    [Nonempty sample] (value : sample → ℚ) (epsilon : ℚ)
    (hepsilon : 0 ≤ epsilon) (hupper : ∀ input, value input ≤ 1)
    (hmean : 1 / 2 + epsilon ≤ uniformMean value) :
    epsilon / 2 ≤
      uniformProbability (Finset.univ.filter fun input =>
        1 / 2 + epsilon / 2 ≤ value input) :=
  half_epsilon_le_probability_ge_of_le_uniformMean_internal
    value epsilon hepsilon hupper hmean

/-- Exact success probability for independent repetition: if one uniform draw
lands in `event` with probability `p`, then at least one of `trials` draws lands
there with probability `1 - (1 - p) ^ trials`.
@isnad1 id=eq.0h3v.s5.c14a7c8c220f from=translated src=- shape=fa72149b vocab=98383c49
-/
theorem uniformAtLeastOneProbability_eq_one_sub_pow
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (trials : ℕ) :
    uniformAtLeastOneProbability event trials =
      1 - (1 - uniformProbability event) ^ trials :=
  uniformAtLeastOneProbability_eq_one_sub_pow_internal event trials

/-- A lower bound on one-draw success lifts to the corresponding independent
repetition bound.
@isnad1 id=le.1h4v.s6.e646ce4139c4 from=translated src=- shape=0c32713d vocab=575aec9a
-/
theorem one_sub_pow_le_uniformAtLeastOneProbability
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (trials : ℕ) (singleDrawLower : ℚ)
    (hlower : singleDrawLower ≤ uniformProbability event) :
    1 - (1 - singleDrawLower) ^ trials ≤
      uniformAtLeastOneProbability event trials :=
  one_sub_pow_le_uniformAtLeastOneProbability_internal
    event trials singleDrawLower hlower

/-- A denominator-free quantitative repetition bound: `trials` independent
draws hit an event of probability `p` with probability at least
`trials * p / (1 + trials * p)`.
@isnad1 id=le.0h3v.s6.1c083f65fe5f from=translated src=- shape=a4652416 vocab=9374914d
-/
theorem trials_mul_div_one_add_le_uniformAtLeastOneProbability
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (trials : ℕ) :
    (trials : ℚ) * uniformProbability event /
        (1 + (trials : ℚ) * uniformProbability event) ≤
      uniformAtLeastOneProbability event trials :=
  trials_mul_div_one_add_le_uniformAtLeastOneProbability_internal
    event trials

/-- If the number of trials times a certified one-draw success lower bound is
at least one, independent repetition succeeds with probability at least one
half.
@isnad1 id=le.2h4v.s6.0ae13db8abf1 from=translated src=- shape=5fa5b8a3 vocab=2d41d381
-/
theorem half_le_uniformAtLeastOneProbability_of_singleDrawLower
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (event : Finset Ω) (trials : ℕ) (singleDrawLower : ℚ)
    (hlower : singleDrawLower ≤ uniformProbability event)
    (htrials : 1 ≤ (trials : ℚ) * singleDrawLower) :
    1 / 2 ≤ uniformAtLeastOneProbability event trials :=
  half_le_uniformAtLeastOneProbability_of_singleDrawLower_internal
    event trials singleDrawLower hlower htrials

/-- Relabeling a finite uniform sample space by an equivalence preserves event
probability.
@isnad1 id=eq.0h4v.s6.496d3eb50814 from=translated src=- shape=ae9ae9ae vocab=a0c34961
-/
theorem uniformProbability_equiv
    {Ω : Type u} {Ξ : Type v} [Fintype Ω]
    [Fintype Ξ] (e : Ω ≃ Ξ) (P : Ξ → Prop)
    [DecidablePred P] :
    uniformProbability (Finset.univ.filter fun x : Ω => P (e x)) =
      uniformProbability (Finset.univ.filter P) :=
  uniformProbability_equiv_internal e P

/-- Every point in a finite uniform sample space has reciprocal-cardinality
probability.
@isnad1 id=eq.0h2v.s5.a499e7f91fe0 from=translated src=- shape=72acdad6 vocab=45891444
-/
theorem uniformProbability_eq {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (x : Ω) :
    uniformProbability (Finset.univ.filter fun y : Ω => y = x) =
      1 / Fintype.card Ω :=
  uniformProbability_eq_internal x

namespace FiniteEnsemble

variable {α : Type u} {β : Type w}

/-- Ensemble event probabilities are nonnegative.
@isnad1 id=le.0h4v.s4.7035d9462816 from=translated src=- shape=f2bf0f33 vocab=ce3f43bc
-/
theorem probability_nonneg (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    0 ≤ D.probability n P :=
  probability_nonneg_internal D n P

/-- Ensemble event probabilities are at most one.
@isnad1 id=le.0h4v.s4.4d048de19c02 from=translated src=- shape=ebb9692a vocab=ce3f43bc
-/
theorem probability_le_one (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n P ≤ 1 :=
  probability_le_one_internal D n P

/--
@isnad1 id=eq.0h3v.s4.4486082b069e from=translated src=- shape=ae09135e vocab=0c875944
-/
@[simp] theorem probability_false (D : FiniteEnsemble α) (n : ℕ) :
    D.probability n (fun _ => False) = 0 :=
  probability_false_internal D n

/--
@isnad1 id=eq.0h3v.s4.c50e59c758af from=translated src=- shape=ae09135e vocab=0c875944
-/
@[simp] theorem probability_true (D : FiniteEnsemble α) (n : ℕ) :
    D.probability n (fun _ => True) = 1 :=
  probability_true_internal D n

/--
@isnad1 id=eq.0h4v.s5.89604d5a24f1 from=translated src=- shape=f3f60ada vocab=801fbba7
-/
theorem probability_not (D : FiniteEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.probability n (fun x => ¬ P x) = 1 - D.probability n P :=
  probability_not_internal D n P

/--
@isnad1 id=le.0h5v.s6.5348b5765b48 from=translated src=- shape=f893ad17 vocab=e1175c25
-/
theorem probability_or_le (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    D.probability n (fun x => P x ∨ Q x) ≤
      D.probability n P + D.probability n Q :=
  probability_or_le_internal D n P Q

/--
@isnad1 id=le.0h6v.s5.c18897b17e8a from=translated src=- shape=047e6ddb vocab=ce3f43bc
-/
theorem probability_mono (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x → Q x) :
    D.probability n P ≤ D.probability n Q :=
  probability_mono_internal D n P Q hPQ

/--
@isnad1 id=eq.1h5v.s5.384ec6362b9d from=translated src=- shape=4afcf808 vocab=30c38946
-/
theorem probability_congr (D : FiniteEnsemble α) (n : ℕ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ x, P x ↔ Q x) :
    D.probability n P = D.probability n Q :=
  probability_congr_internal D n P Q hPQ

/--
@isnad1 id=eq.0h6v.s5.ef01f2f2fda3 from=translated src=- shape=1d8e707b vocab=39eeef9e
-/
@[simp] theorem probability_map (D : FiniteEnsemble α) (f : α → β)
    (n : ℕ) (P : β → Prop) [DecidablePred P] :
    (D.map f).probability n P = D.probability n (fun x => P (f x)) :=
  probability_map_internal D f n P

/--
@isnad1 id=eq.0h3v.s5.a7823b705417 from=translated src=- shape=991c0722 vocab=d9bdb7e7
-/
theorem sum_mass_eq_one [DecidableEq α] (D : FiniteEnsemble α) (n : ℕ) :
    ∑ x ∈ D.support n, D.mass n x = 1 :=
  sum_mass_eq_one_internal D n

/--
@isnad1 id=eq.0h7v.s6.d55a08c103b7 from=translated src=- shape=f13ff71b vocab=d167e962
-/
theorem probability_product (D : FiniteEnsemble α) (E : FiniteEnsemble β)
    (n : ℕ) (P : α → Prop) (Q : β → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (D.product E).probability n (fun xy => P xy.1 ∧ Q xy.2) =
      D.probability n P * E.probability n Q :=
  probability_product_internal D E n P Q

/--
@isnad1 id=eq.0h4v.s5.1ab830559c6b from=translated src=- shape=06d34295 vocab=35d237f4
-/
theorem probability_dirac (x : ℕ → α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    (dirac x).probability n P = if P (x n) then 1 else 0 :=
  probability_dirac_internal x n P

end FiniteEnsemble

namespace DyadicEnsemble

variable {α : Type u}

/-- The finite-uniform embedding preserves every event probability exactly.
@isnad1 id=eq.0h4v.s4.c365f831a7d7 from=translated src=- shape=8ad1fe96 vocab=2e9d1631
-/
@[simp] theorem probability_toFinite (D : DyadicEnsemble α) (n : ℕ)
    (P : α → Prop) [DecidablePred P] :
    D.toFinite.probability n P = D.probability n P :=
  probability_toFinite_internal D n P

end DyadicEnsemble

end Complexity
