/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Tengoku.Seed.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Order properties of `CFC.rpow`

This file shows that `a ↦ a ^ p` is monotone for `p ∈ [0, 1]`, where `a` is an element of a
C⋆-algebra. The proof makes use of the integral representation of `rpow` in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation`.

## Main declarations

+ `CFC.monotone_nnrpow`, `CFC.monotone_rpow`: `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`
+ `CFC.monotone_sqrt`: `CFC.sqrt` is operator monotone
+ `CFC.concaveOn_nnrpow`, `CFC.concaveOn_rpow`: `a ↦ a ^ p` is operator concave for `p ∈ [0,1]`
+ `CFC.concaveOn_sqrt`: `CFC.sqrt` is operator concave

## TODO

+ Show that `rpow` over `Icc (-1) 0` is operator antitone and operator convex
+ Show operator convexity of `rpow` over `Icc 1 2`

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

public section

open Set
open scoped NNReal

namespace CFC

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Real MeasureTheory

/-- This is an intermediate result; use the more general `CFC.monotone_nnrpow` instead. -/
private lemma monotoneOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 0 1) :
    MonotoneOn (fun a : A => a ^ p) (Ici 0) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine MonotoneOn.congr ?_ h₃'.symm
  refine integral_monotoneOn_of_integrand_ae ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact monotoneOn_cfcₙ_rpowIntegrand₀₁ hp ht

/-- `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`.
@isnad1 id=monotone.1h2v.s6.313c4f9e355c from=seed src=0 shape=04b5eeb9 vocab=5a04a5a7
-/
lemma monotone_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) :
    Monotone (fun a : A => a ^ p) := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have hIcc : Icc (0 : ℝ≥0) 1 = Ioo 0 1 ∪ {0} ∪ {1} := by ext; simp
    rw [hIcc] at hp
    obtain (hp | hp) | hp := hp
    · exact monotoneOn_nnrpow_Ioo hp ha hb hab
    · simp_all [mem_singleton_iff]
    · simp_all [mem_singleton_iff, nnrpow_one a, nnrpow_one b]
  · have : a ^ p = 0 := cfcₙ_apply_of_not_predicate a ha
    simp [this]

/-- `CFC.sqrt` is operator monotone.
@isnad1 id=monotone.0h1v.s6.7123aee4cce0 from=seed src=0 shape=c1322f8b vocab=ea5e22e9
-/
lemma monotone_sqrt : Monotone (sqrt : A → A) := by
  intro a b hab
  rw [CFC.sqrt_eq_nnrpow a, CFC.sqrt_eq_nnrpow b]
  refine (monotone_nnrpow (A := A) ?_) hab
  constructor <;> norm_num

/--
@isnad1 id=le.2h4v.s7.8a73802c4b0f from=seed src=0 shape=618cd5dd vocab=59296602
-/
@[gcongr]
lemma nnrpow_le_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
    a ^ p ≤ b ^ p := monotone_nnrpow hp hab

/--
@isnad1 id=le.1h3v.s7.ccef04262519 from=seed src=0 shape=fe0de4a1 vocab=3d470e21
-/
@[gcongr]
lemma sqrt_le_sqrt (a b : A) (hab : a ≤ b) : sqrt a ≤ sqrt b :=
  monotone_sqrt hab

/-- This is an intermediate result; use the more general `CFC.concaveOn_nnrpow` instead. -/
private lemma concaveOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 0 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConcaveOn.congr ?_ h₃'.symm
  refine integral_concaveOn_of_integrand_ae (convex_Ici _) ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact concaveOn_cfcₙ_rpowIntegrand₀₁ hp ht

/-- `a ↦ a ^ p` is operator concave for `p ∈ [0,1]`.
@isnad1 id=concaveo.1h2v.s8.8f609852525f from=seed src=0 shape=3438b6bd vocab=84c3caa4
-/
lemma concaveOn_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  have hIcc : Icc (0 : ℝ≥0) 1 = Ioo 0 1 ∪ {0} ∪ {1} := by ext; simp
  rw [hIcc] at hp
  obtain (hp | hp) | hp := hp
  · exact concaveOn_nnrpow_Ioo hp
  · simp only [mem_singleton_iff] at hp
    simp only [hp, nnrpow_zero]
    exact concaveOn_const _ (convex_Ici _)
  · simp only [mem_singleton_iff] at hp
    simp only [hp]
    exact ConcaveOn.congr (concaveOn_id (convex_Ici _)) nnrpow_one_eqOn.symm

/-- The square root is operator concave.
@isnad1 id=concaveo.0h1v.s8.b9f6d1bb1f27 from=seed src=0 shape=e8633e9e vocab=b1ba6066
-/
lemma concaveOn_sqrt : ConcaveOn ℝ (Ici (0 : A)) (sqrt : A → A) := by
  eta_expand
  simp_rw [sqrt_eq_nnrpow]
  exact concaveOn_nnrpow ⟨by norm_num, by norm_num⟩

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`.
@isnad1 id=monotone.1h2v.s6.08ce8ff63816 from=seed src=0 shape=04b5eeb9 vocab=d06660eb
-/
lemma monotone_rpow {p : ℝ} (hp : p ∈ Icc 0 1) : Monotone (fun a : A => a ^ p) := by
  let q : ℝ≥0 := ⟨p, hp.1⟩
  change Monotone (fun a : A => a ^ (q : ℝ))
  obtain hq | hq := eq_zero_or_pos q
  · rw [hq]
    intro a b hab
    by_cases ha : 0 ≤ a
    · have hb : 0 ≤ b := ha.trans hab
      simp [CFC.rpow_zero a, CFC.rpow_zero b]
    · have : a ^ (0 : ℝ) = 0 := cfc_apply_of_not_predicate a ha
      simp [this]
  · simp_rw [← CFC.nnrpow_eq_rpow hq]
    exact monotone_nnrpow hp

/--
@isnad1 id=le.2h4v.s7.9d8474bda641 from=seed src=0 shape=618cd5dd vocab=21e68c6a
-/
@[gcongr]
lemma rpow_le_rpow {p : ℝ} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
    a ^ p ≤ b ^ p := monotone_rpow hp hab

/-- `a ↦ a ^ p` is operator concave for `p ∈ [0,1]`.
@isnad1 id=concaveo.1h2v.s7.fd6399d37f31 from=seed src=0 shape=3de6a49b vocab=e1303014
-/
lemma concaveOn_rpow {p : ℝ} (hp : p ∈ Icc 0 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  let q : ℝ≥0 := ⟨p, hp.1⟩
  change ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ (q : ℝ))
  obtain hq | hq := eq_zero_or_pos q
  · simp only [hq, NNReal.coe_zero]
    exact ConcaveOn.congr (concaveOn_const _ (convex_Ici _)) rpow_zero_eqOn.symm
  · simp_rw [← CFC.nnrpow_eq_rpow hq]
    exact concaveOn_nnrpow hp

end UnitalCStarAlgebra

end CFC
