/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Tengoku.Seed.Analysis.Complex.ValueDistribution.Proximity.Basic

/-!
# The Characteristic Function of Value Distribution Theory

This file defines the "characteristic function" attached to a meromorphic function defined on the
complex plane.  Also known as "Nevanlinna Height", this is one of the three main functions used in
Value Distribution Theory.

The characteristic function plays a role analogous to the height function in number theory: both
measure the "complexity" of objects. For rational functions, the characteristic function grows like
the degree times the logarithm, much like the logarithmic height in number theory reflects the
degree of an algebraic number.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

### TODO

- Characterize rational functions in terms of the growth rate of their characteristic function, as
  discussed in Theorem 2.6 on p. 170 of [Lang, *Introduction to Complex Hyperbolic
  Spaces*][MR886677].
-/

@[expose] public section

open Filter Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℂ → E} {a : WithTop E}

variable (f a) in
/--
The Characteristic Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic and `a : WithTop E` is any value, the characteristic function of `f`
is defined as the sum of two terms: the proximity function, which quantifies how close `f` gets to
`a` on the circle `∣z∣ = r`, and the logarithmic counting function, which counts the number times
that `f` attains the value `a` inside the disk `∣z∣ ≤ r`, weighted by multiplicity.
-/
noncomputable def characteristic : ℝ → ℝ := proximity f a + logCounting f a

/-!
## Elementary Properties
-/

/--
If two functions differ only on a discrete set, then their characteristic functions agree, except
perhaps at radius 0.
@isnad1 id=eq.2h5v.s6.59fc5e1b1b9f from=seed src=0 shape=7ecaa385 vocab=e9402c9f
-/
theorem characteristic_congr_codiscrete {r : ℝ} (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) :
    characteristic f a r = characteristic g a r := by
  simp [characteristic, proximity_congr_codiscrete hfg hr, logCounting_congr_codiscrete hfg]

/--
The difference between the characteristic functions for the poles of `f` and `f - const` simplifies
to the difference between the proximity functions.
@isnad1 id=eq.1h3v.s7.818008c2d882 from=seed src=0 shape=fa33422e vocab=faa40dc8
-/
@[simp]
lemma characteristic_sub_characteristic_eq_proximity_sub_proximity (h : Meromorphic f) (a₀ : E) :
    characteristic f ⊤ - characteristic (f · - a₀) ⊤ = proximity f ⊤ - proximity (f · - a₀) ⊤ := by
  simp [← Pi.sub_def, characteristic, logCounting_sub_const h]

/--
The characteristic function is even.
@isnad1 id=even.0h3v.s4.f9f85c8c2ebd from=seed src=0 shape=43ec87ef vocab=d8dc8894
-/
theorem characteristic_even :
    (characteristic f a).Even := proximity_even.add logCounting_even

/--
For `1 ≤ r`, the characteristic function is non-negative.
@isnad1 id=le.1h4v.s5.9f082b7ca887 from=seed src=0 shape=e672994f vocab=2d4b4d2f
-/
theorem characteristic_nonneg {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ characteristic f a r :=
  add_nonneg (proximity_nonneg r) (logCounting_nonneg hr)

/--
The characteristic function is asymptotically non-negative.
@isnad1 id=eventual.0h3v.s5.fd279a176c1e from=seed src=0 shape=ea1a33c2 vocab=92a91a8c
-/
theorem characteristic_eventually_nonneg :
    0 ≤ᶠ[Filter.atTop] characteristic f a := by
  filter_upwards [Filter.eventually_ge_atTop 1] using fun _ hr ↦ by simp [characteristic_nonneg hr]

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or equal to the sum
of the characteristic functions of `f ·`, plus `log s.card`.
@isnad1 id=le.2h5v.s7.19c8ad994ec1 from=seed src=0 shape=121380fb vocab=43e30a04
-/
theorem characteristic_sum_top_le {α : Type*} (s : Finset α) (f : α → ℂ → E) {r : ℝ}
    (hf : ∀ a ∈ s, Meromorphic (f a)) (hr : 1 ≤ r) :
    characteristic (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (characteristic (f a) ⊤)) r + log s.card := by
  simp only [characteristic, Pi.add_apply, Finset.sum_apply]
  calc proximity (∑ a ∈ s, f a) ⊤ r + logCounting (∑ a ∈ s, f a) ⊤ r
  _ ≤ ((∑ a ∈ s, proximity (f a) ⊤) r) + log s.card + (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
      gcongr
      · apply proximity_sum_top_le s f hf r
      · apply logCounting_sum_top_le s f hf hr
    _ = ((∑ a ∈ s, proximity (f a) ⊤) r) + (∑ a ∈ s, (logCounting (f a) ⊤)) r + log s.card := by
      ring
    _ = ∑ x ∈ s, (proximity (f x) ⊤ r + logCounting (f x) ⊤ r) + log s.card := by
      simp [Finset.sum_add_distrib]

/--
Asymptotically, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or equal to the
sum of the characteristic functions of `f ·`.
@isnad1 id=eventual.1h4v.s7.e73f9304fe82 from=seed src=0 shape=982a1bf1 vocab=fc6c6ee0
-/
theorem characteristic_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a ∈ s, Meromorphic (f a)) :
    characteristic (∑ a ∈ s, f a) ⊤
      ≤ᶠ[Filter.atTop] ∑ a ∈ s, (characteristic (f a) ⊤) + fun _ ↦ log s.card := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_sum_top_le s f hf hr

/--
For `1 ≤ r`, the characteristic function of `f + g` at `⊤` is less than or equal to the sum of the
characteristic functions of `f` and `g`, respectively, plus `log 2` (where `2` is the number of
summands).
@isnad1 id=le.3h4v.s7.48f77564761d from=seed src=0 shape=bd94913d vocab=039c01ec
-/
theorem characteristic_add_top_le {f₁ f₂ : ℂ → E} {r : ℝ} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 ≤ r) :
    characteristic (f₁ + f₂) ⊤ r ≤ characteristic f₁ ⊤ r + characteristic f₂ ⊤ r + log 2 := by
  have h_meromorphic : ∀ a ∈ Finset.univ, Meromorphic (![f₁, f₂] a) := by
    simpa using ⟨h₁f₁, h₁f₂⟩
  simpa using characteristic_sum_top_le Finset.univ ![f₁, f₂] h_meromorphic hr

/--
Asymptotically, the characteristic function of `f + g` at `⊤` is less than or equal to the sum of
the characteristic functions of `f` and `g`, respectively.
@isnad1 id=eventual.2h3v.s7.c0a09c6bb86f from=seed src=0 shape=90ba0d00 vocab=3ebaa410
-/
theorem characteristic_add_top_eventuallyLE {f₁ f₂ : ℂ → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    characteristic (f₁ + f₂) ⊤
      ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ + fun _ ↦ log 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    using characteristic_add_top_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the characteristic function for the zeros of `f * g` is less than or equal to the sum
of the characteristic functions for the zeros of `f` and `g`, respectively.
@isnad1 id=le.5h3v.s7.126a765e18bb from=seed src=0 shape=ad3967db vocab=e3ea905c
-/
theorem characteristic_mul_zero_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 r ≤ (characteristic f₁ 0 + characteristic f₂ 0) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_zero_le h₁f₁ h₁f₂ r)
    (logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function for the zeros of `f * g` is less than or equal to the
sum of the characteristic functions for the zeros of `f` and `g`, respectively.
@isnad1 id=eventual.4h2v.s7.dc9619337442 from=seed src=0 shape=9d1147bc vocab=7a932e10
-/
theorem characteristic_mul_zero_eventuallyLE {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) 0 ≤ᶠ[Filter.atTop] characteristic f₁ 0 + characteristic f₂ 0 := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For `1 ≤ r`, the characteristic function for the poles of `f * g` is less than or equal to the sum
of the characteristic functions for the poles of `f` and `g`, respectively.
@isnad1 id=le.5h3v.s7.f1890ac6877c from=seed src=0 shape=f53b2a40 vocab=e3ea905c
-/
theorem characteristic_mul_top_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ r ≤ (characteristic f₁ ⊤ + characteristic f₂ ⊤) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  apply add_le_add (proximity_mul_top_le h₁f₁ h₁f₂ r)
    (logCounting_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function for the poles of `f * g` is less than or equal to the
sum of the characteristic functions for the poles of `f` and `g`, respectively.
@isnad1 id=eventual.4h2v.s7.34a4b05dd6fd from=seed src=0 shape=ca092fb2 vocab=7a932e10
-/
theorem characteristic_mul_top_eventuallyLE {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, meromorphicOrderAt f₁ z ≠ ⊤)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, meromorphicOrderAt f₂ z ≠ ⊤) :
    characteristic (f₁ * f₂) ⊤ ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ + characteristic f₂ ⊤ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_mul_top_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For natural numbers `n`, the characteristic function for the zeros of `f ^ n` equals `n` times the
characteristic counting function for the zeros of `f`.
@isnad1 id=eq.1h2v.s7.ac18494def03 from=seed src=0 shape=f700cb98 vocab=e8ce16dd
-/
@[simp]
theorem characteristic_pow_zero {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f) :
    characteristic (f ^ n) 0 = n • characteristic f 0 := by
  simp_all [characteristic]

/--
For natural numbers `n`, the characteristic function for the poles of `f ^ n` equals `n` times the
characteristic function for the poles of `f`.
@isnad1 id=eq.1h2v.s6.4af78fa34a51 from=seed src=0 shape=c7c27893 vocab=7c3e7f0f
-/
@[simp]
theorem characteristic_pow_top {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f) :
    characteristic (f ^ n) ⊤ = n • characteristic f ⊤ := by
  simp_all [characteristic]

end ValueDistribution
