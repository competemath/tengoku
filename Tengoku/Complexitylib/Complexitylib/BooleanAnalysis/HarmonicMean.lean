/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.BooleanAnalysis.Bernoulli
public import Tengoku.Complexitylib.Complexitylib.BooleanAnalysis.HarmonicMean.Defs
public import Tengoku.Complexitylib.Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Density
public import Tengoku.Complexitylib.Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Projection

/-!
# Korten's harmonic mean transform

This module formalizes Definition 5, Lemmas 11--12, and Corollary 1 of Oliver
Korten, *Top-Down Lower Bounds for All Depths*, ECCC TR26-221 (2026),
https://eccc.weizmann.ac.il/report/2026/221/.

`harmonicMean_variational` works on any nonempty finite type. The coordinate
transform uses Boolean membership functions for sets and real nonnegative
densities. `harmonicTransform_eq_harmonicMean_coordinateMarginal` identifies
the convenient full-cube representation with the harmonic mean over actual
projected patterns. Zero entries give harmonic mean zero, as in the paper.

`expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform` is Lemma 12, including
dimension zero. `harmonicTransform_good_probability` supplies the intermediate
1/4-sampling estimate in the proof of Lemma 10, using a density bound `B` in
place of `2 ^ k`. The sparse-sampling conclusion and pattern count of Lemma 10
are proved in `Complexitylib.BooleanAnalysis.LightPatterns`, which feeds the
mirror-set argument of `Complexitylib.BooleanAnalysis.MirrorSets`. The top-down
communication and circuit lower bounds of Theorem 3 are
`Complexity.KarchmerWigderson.parity_communication_lower_bound` and
`Complexity.Circuit.parity_wire_lower_bound` in
`Complexitylib.Circuits.KarchmerWigderson.TopDown`.
-/

public section

namespace Complexity.BooleanAnalysis

open scoped BigOperators

section Mean

variable {α : Type*} [Fintype α]

/-- A zero entry makes the harmonic mean zero, implementing `0⁻¹ = ∞`
inside the average rather than Lean's real inverse at zero.
@isnad1 id=eq.1h2v.s5.aff1937aca4e from=translated src=- shape=cd2441b5 vocab=ecc4ed94
-/
theorem harmonicMean_eq_zero_of_exists {f : α → ℝ} (hf : ∃ x, f x = 0) :
    harmonicMean f = 0 := by
  rw [harmonicMean, ite_eq_left hf]

/-- Harmonic means of nonnegative entries are nonnegative.
@isnad1 id=le.1h2v.s5.4b43c2fb1a6e from=translated src=- shape=92c325ac vocab=32c96a78
-/
theorem harmonicMean_nonneg {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ harmonicMean f := harmonicMean_nonneg_internal hf

variable [Nonempty α]

/-- The harmonic mean of a constant on a nonempty finite set is that constant.
@isnad1 id=eq.0h2v.s4.d00bf32dca9a from=translated src=- shape=5addde91 vocab=3dede0ac
-/
theorem harmonicMean_const (c : ℝ) : harmonicMean (fun _ : α => c) = c :=
  harmonicMean_const_internal c

/-- Every weight with mean one bounds the harmonic mean by its quadratic energy.
The weight need not be nonnegative for this direction.
@isnad1 id=le.2h3v.s6.11d240768c76 from=translated src=- shape=37f15ab3 vocab=cb1b6c73
-/
theorem harmonicMean_le_energy {f w : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hw : (𝔼 x, w x) = 1) : harmonicMean f ≤ 𝔼 x, f x * w x ^ 2 :=
  harmonicMean_le_energy_internal hf hw

/-- A nonnegative weight of mean one attains the variational minimum,
including when an entry of `f` is zero.
@isnad1 id=ex.1h2v.s7.0c3e7f355fdb from=translated src=- shape=9dbbf4d9 vocab=cb1b6c73
-/
theorem harmonicMean_exists_weight {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∃ w : α → ℝ, (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧
      (𝔼 x, f x * w x ^ 2) = harmonicMean f :=
  harmonicMean_exists_weight_internal hf

/-- Korten's Lemma 11, generalized to every nonempty finite type.
@isnad1 id=eq.1h2v.s7.d65368ca3c96 from=translated src=- shape=c31934f1 vocab=9c4d5742
-/
theorem harmonicMean_variational {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f = sInf {a : ℝ | ∃ w : α → ℝ,
      (∀ x, 0 ≤ w x) ∧ (𝔼 x, w x) = 1 ∧ (𝔼 x, f x * w x ^ 2) = a} :=
  harmonicMean_variational_internal hf

/-- Harmonic means are monotone in their nonnegative entries.
@isnad1 id=le.2h3v.s5.1dda5d8661ef from=translated src=- shape=7921e296 vocab=90db7c68
-/
theorem harmonicMean_mono {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hfg : ∀ x, f x ≤ g x) : harmonicMean f ≤ harmonicMean g :=
  harmonicMean_mono_internal hf hfg

/-- Harmonic means are concave on nonnegative functions.
@isnad1 id=le.4h4v.s7.b2935e0103b0 from=translated src=- shape=5c66275e vocab=6cd5c4de
-/
theorem harmonicMean_concave {f g : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    t * harmonicMean f + (1 - t) * harmonicMean g ≤
      harmonicMean (fun x => t * f x + (1 - t) * g x) :=
  harmonicMean_concave_internal hf hg ht ht'

/-- The harmonic mean is at most the arithmetic mean.
@isnad1 id=le.1h2v.s5.3daf5dea7bd3 from=translated src=- shape=2add7083 vocab=cffc9632
-/
theorem harmonicMean_le_expect {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    harmonicMean f ≤ 𝔼 x, f x := harmonicMean_le_expect_internal hf

/-- A positive harmonic-mean lower bound controls the fraction of small entries.
This is the reciprocal-density Markov step used for light patterns.
@isnad1 id=le.4h4v.s6.b4a772c85d45 from=translated src=- shape=e1696c82 vocab=0435d1ca
-/
theorem harmonicMean_light_fraction_le {f : α → ℝ} (hf : ∀ x, 0 ≤ f x)
    {a b : ℝ} (ha : 0 < a) (ha' : a ≤ harmonicMean f) (hb : 0 ≤ b) :
    (𝔼 x, if f x ≤ b then (1 : ℝ) else 0) ≤ b / a :=
  harmonicMean_light_fraction_le_internal hf ha ha' hb

end Mean

section Projection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full-cube projection depends exactly on the selected input pattern.
@isnad1 id=eq.0h4v.s5.33e8673c544f from=translated src=- shape=0ffd0f66 vocab=71b1e2bb
-/
theorem projectionAverage_eq_coordinateMarginal (f : (ι → Bool) → ℝ)
    (selected x : ι → Bool) :
    projectionAverage f selected x = coordinateMarginal f selected (fun i => x i) :=
  projectionAverage_eq_coordinateMarginal_internal f selected x

/-- Marginalization preserves the uniform mean, hence also density normalization.
@isnad1 id=eq.0h3v.s7.a4a8d951d7cd from=translated src=- shape=ac009517 vocab=411a15cb
-/
theorem expect_coordinateMarginal (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    (𝔼 z, coordinateMarginal f selected z) = 𝔼 x, f x :=
  expect_coordinateMarginal_internal f selected

/-- The transform agrees with Definition 5 on the actual projected cube;
repeating each pattern on the full cube does not change its harmonic mean.
@isnad1 id=eq.0h3v.s7.c71f62edb8dc from=translated src=- shape=f0d6e184 vocab=1a6c6aba
-/
theorem harmonicTransform_eq_harmonicMean_coordinateMarginal
    (f : (ι → Bool) → ℝ) (selected : ι → Bool) :
    harmonicTransform f selected = harmonicMean (coordinateMarginal f selected) :=
  harmonicTransform_eq_harmonicMean_coordinateMarginal_internal f selected

/-- Lemma 11 on the selected-coordinate cube, with nonnegative weights of mean one.
@isnad1 id=eq.1h3v.s8.604fe94c2aab from=translated src=- shape=5231b427 vocab=a8cd31d0
-/
theorem harmonicTransform_variational {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) :
    harmonicTransform f selected = sInf {a : ℝ |
      ∃ w : ({i // selected i = true} → Bool) → ℝ,
        (∀ z, 0 ≤ w z) ∧ (𝔼 z, w z) = 1 ∧
          (𝔼 z, coordinateMarginal f selected z * w z ^ 2) = a} := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal]
  exact harmonicMean_variational fun _ => Finset.expect_nonneg fun _ _ => hf _

/-- A positive transform lower bound bounds the fraction of light projected
patterns. The expectation ranges over the actual selected-coordinate cube.
@isnad1 id=le.4h5v.s8.2b63232039f2 from=translated src=- shape=4265399d vocab=690d96c2
-/
theorem coordinateMarginal_light_fraction_le {f : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : ι → Bool) {a b : ℝ} (ha : 0 < a)
    (ha' : a ≤ harmonicTransform f selected) (hb : 0 ≤ b) :
    (𝔼 z, if coordinateMarginal f selected z ≤ b then (1 : ℝ) else 0) ≤ b / a := by
  rw [harmonicTransform_eq_harmonicMean_coordinateMarginal] at ha'
  exact harmonicMean_light_fraction_le
    (fun _ => Finset.expect_nonneg fun _ _ => hf _) ha ha' hb

/-- The harmonic transform is nonnegative on nonnegative functions.
@isnad1 id=le.1h3v.s5.a30b5c68d975 from=translated src=- shape=0b531906 vocab=0bd237b1
-/
theorem harmonicTransform_nonneg {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (selected : ι → Bool) : 0 ≤ harmonicTransform f selected :=
  harmonicTransform_nonneg_internal hf selected

/-- Corollary 1(1): the transform is pointwise concave in its input function.
@isnad1 id=le.4h5v.s7.84b14507cdf1 from=translated src=- shape=7a88534e vocab=aa22654f
-/
theorem harmonicTransform_concave {f g : (ι → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (selected : ι → Bool) :
    t * harmonicTransform f selected + (1 - t) * harmonicTransform g selected ≤
      harmonicTransform (fun x => t * f x + (1 - t) * g x) selected :=
  harmonicTransform_concave_internal hf hg ht ht' selected

/-- Selecting no coordinates gives the ordinary mean.
@isnad1 id=eq.0h2v.s6.81ad079e6382 from=translated src=- shape=b42dfc65 vocab=e5b2efb7
-/
theorem harmonicTransform_empty (f : (ι → Bool) → ℝ) :
    harmonicTransform f (fun _ => false) = 𝔼 x, f x :=
  harmonicTransform_empty_internal f

/-- Selecting all coordinates gives the harmonic mean of the original function.
@isnad1 id=eq.0h2v.s5.d4ac7113971a from=translated src=- shape=92df96e2 vocab=e29e2aad
-/
theorem harmonicTransform_full (f : (ι → Bool) → ℝ) :
    harmonicTransform f (fun _ => true) = harmonicMean f :=
  harmonicTransform_full_internal f

/-- Constants are fixed by the harmonic transform.
@isnad1 id=eq.0h3v.s4.57f48872a431 from=translated src=- shape=ebd2f44a vocab=3de0c738
-/
theorem harmonicTransform_const (c : ℝ) (selected : ι → Bool) :
    harmonicTransform (fun _ => c) selected = c := harmonicTransform_const_internal c selected

end Projection

/-- Corollary 1(2): revealing more coordinates decreases the harmonic transform.
The hypothesis is inclusion of the two sets represented by Boolean masks.
@isnad1 id=le.2h4v.s6.e537eea1c51a from=translated src=- shape=56cb0ee8 vocab=9408b770
-/
theorem harmonicTransform_antitone {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) {r s : Fin n → Bool} (hrs : ∀ i, r i = true → s i = true) :
    harmonicTransform f s ≤ harmonicTransform f r := harmonicTransform_antitone_internal hf hrs

/-- Corollary 1(3): the harmonic transform is at most the ordinary mean.
@isnad1 id=le.1h3v.s6.37acb57e9337 from=translated src=- shape=8c4d5f4f vocab=e0011664
-/
theorem harmonicTransform_le_expect {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (selected : Fin n → Bool) :
    harmonicTransform f selected ≤ 𝔼 x, f x := harmonicTransform_le_expect_internal hf selected

/-- Korten's Lemma 12: on the `1/4`-biased coordinate cube, the mean square root
of the harmonic transform dominates the uniform mean square root of `f`.
@isnad1 id=le.1h2v.s6.e29a8c22543d from=translated src=- shape=0f95181a vocab=2c9d13be
-/
theorem expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform {n : ℕ}
    {f : (Fin n → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x, Real.sqrt (f x)) ≤
      bernoulliAverage (1 / 4) (fun selected => Real.sqrt (harmonicTransform f selected)) :=
  expect_sqrt_le_bernoulliAverage_sqrt_harmonicTransform_internal hf

/-- Intermediate estimate in the proof of Lemma 10: a normalized density bounded
by `B` has harmonic transform at least `1 / (4 * B)` with probability at least
`1 / (2 * sqrt B)` under `1/4`-coordinate sampling. The `LightPatterns` module
transfers this estimate to sparse sampling.
@isnad1 id=le.4h3v.s8.9a14d1b6fb7b from=translated src=- shape=a2f7c404 vocab=6f1c3f81
-/
theorem harmonicTransform_good_probability {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hmean : (𝔼 x, f x) = 1) {B : ℝ} (hB : 1 ≤ B)
    (hbound : ∀ x, f x ≤ B) :
    1 / (2 * Real.sqrt B) ≤ bernoulliAverage (1 / 4)
      (fun selected => if 1 / (4 * B) ≤ harmonicTransform f selected then 1 else 0) :=
  harmonicTransform_good_probability_internal hf hmean hB hbound

end Complexity.BooleanAnalysis
