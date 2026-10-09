/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Anatole Dedecker
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Algebra.Spectrum
public import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Tengoku.Seed.Analysis.RCLike.Lemmas
public import Tengoku.Seed.MeasureTheory.SpecificCodomains.ContinuousMapZero
public import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals and the continuous functional calculus

This file gives results about integrals of the form `∫ x, cfc (f x) a`. Most notably, we show
that the integral commutes with the continuous functional calculus under appropriate conditions.

## Main declarations

+ `cfc_setIntegral` (resp. `cfc_integral`): given a function `f : X → 𝕜 → 𝕜`, we have that
  `cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ`
  under appropriate conditions (resp. with `s = univ`)
+ `cfcₙ_setIntegral`, `cfcₙ_integral`: the same for the non-unital continuous functional calculus
+ `integrableOn_cfc`, `integrableOn_cfcₙ`, `integrable_cfc`, `integrable_cfcₙ`:
  functions of the form `fun x => cfc (f x) a` are integrable.

## Implementation Notes

The lemmas mentioned above are stated under much stricter hypotheses than necessary
(typically, simultaneous continuity of `f` in the parameter and the spectrum element).
They all come with primed version which only assume what's needed, and may be used together
with the API developed in `Mathlib.MeasureTheory.SpecificCodomains.ContinuousMap`.

## TODO

+ Lift this to the case where the CFC is over `ℝ≥0`
+ Use this to prove operator monotonicity and concavity/convexity of `rpow` and `log`
-/

public section

open MeasureTheory
open scoped ContinuousMapZero

section unital

open ContinuousMap

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X}
  [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
  [ContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

/--
@isnad1 id=eq.1h8v.s11.47bb8c611e52 from=seed src=0 shape=63d74e45 vocab=36e248c9
-/
lemma cfcL_integral [NormedSpace ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜)) (hf₁ : Integrable f μ)
    (ha : p a := by cfc_tac) :
    ∫ x, cfcL (a := a) ha (f x) ∂μ = cfcL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

/--
@isnad1 id=integrab.1h8v.s11.8ccec8c5d0a9 from=seed src=0 shape=c8eb4394 vocab=98e4efd7
-/
lemma cfcL_integrable (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x ↦ cfcL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

/--
@isnad1 id=eq.1h8v.s11.850facb77df4 from=seed src=0 shape=05eadf07 vocab=c15acacf
-/
lemma cfcHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(spectrum 𝕜 a, 𝕜))
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcHom (a := a) ha (f x) ∂μ = cfcHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcL_integral a f hf₁ ha

/-- An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrable_cfc`.
@isnad1 id=integrab.1h8v.s10.0d3e13bb15bf from=seed src=0 shape=a58cc992 vocab=1c297cca
-/
lemma integrable_cfc' (f : X → 𝕜 → 𝕜) (a : A)
    (hf : Integrable
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  conv in cfc _ _ => rw [cfc_eq_cfcL_mkD _ a]
  exact cfcL_integrable _ _ hf ha

/-- An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrableOn_cfc`.
@isnad1 id=integrab.1h9v.s10.fda70504c8f9 from=seed src=0 shape=5e610baf vocab=7bdbf40c
-/
lemma integrableOn_cfc' {s : Set X} (f : X → 𝕜 → 𝕜) (a : A)
    (hf : IntegrableOn
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  exact integrable_cfc' _ _ hf ha

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrable_cfc'` for a statement
with weaker assumptions.
@isnad1 id=integrab.3h9v.s9.882425a60b1a from=seed src=0 shape=fe6ddd72 vocab=9b517b7f
-/
lemma integrable_cfc [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfc (f x) a) μ := by
  refine integrable_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact .of_forall fun x ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrableOn_cfc'` for a statement
with weaker assumptions.
@isnad1 id=integrab.4h10v.s9.e00abdf0cde8 from=seed src=0 shape=3a3802f5 vocab=ff8ec9a7
-/
lemma integrableOn_cfc [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfc (f x) a) s μ := by
  refine integrableOn_cfc' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩

open Set in
/-- The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfc_integral`.
@isnad1 id=eq.2h8v.s10.27c91d686025 from=seed src=0 shape=a84265ed vocab=1fb9aa57
-/
lemma cfc_integral' [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : Integrable
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have key₁ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((spectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₂]
    refine integral_congr_ae ?_
    filter_upwards [hf₁] with x cont_x
    rw [mkD_apply_of_continuousOn cont_x]
  have key₂ (z : spectrum 𝕜 a) :
      ∫ x, f x z ∂μ = mkD ((spectrum 𝕜 a).domRestrict (fun z ↦ ∫ x, f x z ∂μ)) 0 z := by
    rw [mkD_apply_of_continuousOn]
    rw [continuousOn_iff_continuous_domRestrict]
    refine continuous_congr key₁ |>.mpr ?_
    exact map_continuous (∫ x, mkD ((spectrum 𝕜 a).domRestrict (f x)) 0 ∂μ)
  simp_rw [cfc_eq_cfcL_mkD _ a, cfcL_integral a _ hf₂ ha]
  congr
  ext z
  rw [← key₁, key₂]

open Set in
/-- The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfc_setIntegral`.
@isnad1 id=eq.2h9v.s10.40d31c26623c from=seed src=0 shape=7d8a66bf vocab=2ff03227
-/
lemma cfc_setIntegral' {s : Set X} [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a))
    (hf₂ : IntegrableOn
      (fun x : X => mkD ((spectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    cfc (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfc (f x) a ∂μ :=
  cfc_integral' _ _ hf₁ hf₂ ha

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfc_integral'` for a statement
with weaker assumptions.
@isnad1 id=eq.3h9v.s9.9e80f0b7bcbe from=seed src=0 shape=3c30b0fa vocab=96d97dbb
-/
lemma cfc_integral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A) [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfc (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂μ, ContinuousOn (f x) (spectrum 𝕜 a) := .of_forall fun x ↦
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩
  refine cfc_integral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfc_setIntegral'` for a statement
with weaker assumptions.
@isnad1 id=eq.4h10v.s9.692117173f69 from=seed src=0 shape=32dd19ad vocab=15d1916b
-/
lemma cfc_setIntegral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(spectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ spectrum 𝕜 a))
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ spectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfc (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfc (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (spectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  refine cfc_setIntegral' _ _ this ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this bound bound_int bound_ge

end unital

section nonunital

open ContinuousMapZero

variable {X : Type*} {𝕜 : Type*} {A : Type*} {p : A → Prop} [RCLike 𝕜]
  [MeasurableSpace X] {μ : Measure X} [NonUnitalNormedRing A] [StarRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]
  [CompleteSpace A]

/--
@isnad1 id=eq.1h8v.s12.751fedd41ea7 from=seed src=0 shape=a354b878 vocab=c74e09be
-/
lemma cfcₙL_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙL (a := a) ha (f x) ∂μ = cfcₙL (a := a) ha (∫ x, f x ∂μ) := by
  rw [ContinuousLinearMap.integral_comp_comm _ hf₁]

/--
@isnad1 id=eq.1h8v.s13.e5be7cb9ef17 from=seed src=0 shape=6a3fe894 vocab=d163a4f1
-/
lemma cfcₙHom_integral [NormedSpace ℝ A] (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    ∫ x, cfcₙHom (a := a) ha (f x) ∂μ = cfcₙHom (a := a) ha (∫ x, f x ∂μ) :=
  cfcₙL_integral a f hf₁ ha

/--
@isnad1 id=integrab.1h8v.s11.11aa3b561160 from=seed src=0 shape=a950d433 vocab=ae001bae
-/
lemma cfcₙL_integrable (a : A) (f : X → C(quasispectrum 𝕜 a, 𝕜)₀)
    (hf₁ : Integrable f μ) (ha : p a := by cfc_tac) :
    Integrable (fun x ↦ cfcₙL (a := a) ha (f x)) μ :=
  ContinuousLinearMap.integrable_comp _ hf₁

/-- An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrable_cfcₙ`.
@isnad1 id=integrab.1h8v.s11.15cd20c5adad from=seed src=0 shape=de7b8e33 vocab=7af5b308
-/
lemma integrable_cfcₙ' (f : X → 𝕜 → 𝕜) (a : A)
    (hf : Integrable
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  conv in cfcₙ _ _ => rw [cfcₙ_eq_cfcₙL_mkD _ a]
  exact cfcₙL_integrable _ _ hf ha

/-- An integrability criterion for the continuous functional calculus.
For a version with stronger assumptions which in practice are often easier to verify, see
`integrableOn_cfcₙ`.
@isnad1 id=integrab.1h9v.s11.1bfc35e95e18 from=seed src=0 shape=766fb846 vocab=a2032e09
-/
lemma integrableOn_cfcₙ' {s : Set X} (f : X → 𝕜 → 𝕜) (a : A)
    (hf : IntegrableOn
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  exact integrable_cfcₙ' _ _ hf ha

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrable_cfcₙ'` for a statement
with weaker assumptions.
@isnad1 id=integrab.4h9v.s10.7893a05abde6 from=seed src=0 shape=e0df6b4c vocab=fdd244ce
-/
lemma integrable_cfcₙ [TopologicalSpace X] [OpensMeasurableSpace X] (f : X → 𝕜 → 𝕜)
    (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    Integrable (fun x => cfcₙ (f x) a) μ := by
  refine integrable_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact .of_forall fun x ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩

open Set Function in
/-- An integrability criterion for the continuous functional calculus.
This version assumes joint continuity of `f`, see `integrableOn_cfcₙ'` for a statement
with weaker assumptions.
@isnad1 id=integrab.5h10v.s10.08c45a8eb560 from=seed src=0 shape=cdd3120c vocab=1ecaa94c
-/
lemma integrableOn_cfcₙ [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    IntegrableOn (fun x => cfcₙ (f x) a) s μ := by
  refine integrableOn_cfcₙ' _ _ ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · refine hasFiniteIntegral_mkD_restrict_of_bound f _ ?_ f_zero bound bound_int bound_ge
    exact ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩

open Set in
/-- The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfcₙ_integral`.
@isnad1 id=eq.3h8v.s11.b5905176c649 from=seed src=0 shape=1752efda vocab=db4bd4a0
-/
lemma cfcₙ_integral' [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂μ, f x 0 = 0)
    (hf₃ : Integrable
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) μ)
    (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x, f x z ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have key₁ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = (∫ x, mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0 ∂μ) z := by
    rw [integral_apply hf₃]
    refine integral_congr_ae ?_
    filter_upwards [hf₁, hf₂] with x cont_x zero_x
    rw [mkD_apply_of_continuousOn cont_x zero_x]
  have key₂ (z : quasispectrum 𝕜 a) :
      ∫ x, f x z ∂μ = mkD ((quasispectrum 𝕜 a).domRestrict (fun z ↦ ∫ x, f x z ∂μ)) 0 z := by
    rw [mkD_apply_of_continuousOn]
    · rw [continuousOn_iff_continuous_domRestrict]
      refine continuous_congr key₁ |>.mpr ?_
      exact map_continuous (∫ x, mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0 ∂μ)
    · exact integral_eq_zero_of_ae hf₂
  simp_rw [cfcₙ_eq_cfcₙL_mkD _ a, cfcₙL_integral a _ hf₃ ha]
  congr
  ext z
  rw [← key₁, key₂]

open Set in
/-- The continuous functional calculus commutes with integration.
For a version with stronger assumptions which in practice are often easier to verify, see
`cfcₙ_setIntegral`.
@isnad1 id=eq.3h9v.s11.962c723b5d56 from=seed src=0 shape=f162f4f9 vocab=d66869a4
-/
lemma cfcₙ_setIntegral' {s : Set X} [NormedSpace ℝ A] (f : X → 𝕜 → 𝕜) (a : A)
    (hf₁ : ∀ᵐ x ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a))
    (hf₂ : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (hf₃ : IntegrableOn
      (fun x : X => mkD ((quasispectrum 𝕜 a).domRestrict (f x)) 0) s μ)
    (ha : p a := by cfc_tac) :
    cfcₙ (fun z => ∫ x in s, f x z ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ :=
  cfcₙ_integral' _ _ hf₁ hf₂ hf₃ ha

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfcₙ_integral'` for a statement
with weaker assumptions.
@isnad1 id=eq.4h9v.s10.f0e8694438c2 from=seed src=0 shape=da941c32 vocab=0d6b5095
-/
lemma cfcₙ_integral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X]
    (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (univ ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂μ, f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂μ, ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound μ) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x, f x r ∂μ) a = ∫ x, cfcₙ (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂μ, ContinuousOn (f x) (quasispectrum 𝕜 a) := .of_forall fun x ↦
    hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨Set.mem_univ _, hz⟩
  refine cfcₙ_integral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_mkD_restrict_of_uncurry _ _ hf f_zero
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this f_zero bound bound_int bound_ge

open Function Set in
/-- The continuous functional calculus commutes with integration.
This version assumes joint continuity of `f`, see `cfcₙ_setIntegral'` for a statement
with weaker assumptions.
@isnad1 id=eq.5h10v.s10.b51fd3601e88 from=seed src=0 shape=ddc0fe6b vocab=34e6ca82
-/
lemma cfcₙ_setIntegral [NormedSpace ℝ A] [TopologicalSpace X] [OpensMeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) (f : X → 𝕜 → 𝕜) (bound : X → ℝ) (a : A)
    [SecondCountableTopologyEither X C(quasispectrum 𝕜 a, 𝕜)]
    (hf : ContinuousOn (uncurry f) (s ×ˢ quasispectrum 𝕜 a))
    (f_zero : ∀ᵐ x ∂(μ.restrict s), f x 0 = 0)
    (bound_ge : ∀ᵐ x ∂(μ.restrict s), ∀ z ∈ quasispectrum 𝕜 a, ‖f x z‖ ≤ bound x)
    (bound_int : HasFiniteIntegral bound (μ.restrict s)) (ha : p a := by cfc_tac) :
    cfcₙ (fun r => ∫ x in s, f x r ∂μ) a = ∫ x in s, cfcₙ (f x) a ∂μ := by
  have : ∀ᵐ (x : X) ∂(μ.restrict s), ContinuousOn (f x) (quasispectrum 𝕜 a) :=
    ae_restrict_of_forall_mem hs fun x hx ↦
      hf.comp (Continuous.prodMk_right x).continuousOn fun _ hz ↦ ⟨hx, hz⟩
  refine cfcₙ_setIntegral' _ _ this f_zero ⟨?_, ?_⟩ ha
  · exact aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry hs _ _ hf f_zero
  · exact hasFiniteIntegral_mkD_restrict_of_bound f _ this f_zero bound bound_int bound_ge

end nonunital
