/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ConcentrationInequalities.BennettBernstein

/-!
# Freedman / Bernstein inequality for martingales (adapted sums of sub-gamma increments)

The variance-based (Freedman) martingale tail: a finite adapted sum of conditionally sub-gamma
increments satisfies `P(∑ Yᵢ ≥ ε) ≤ exp(−ε²/(2(∑Vᵢ + cε)))`. Mathlib has Azuma (sub-Gaussian
martingales) but not the sub-gamma / Freedman version. Built on the sub-gamma MGF and Bernstein tail
of `Contrib.BennettBernstein`, with kernel-level tower additivity of the variance factors.

* `Contrib.Freedman.subgamma_bernstein_tail` — the Freedman/Bernstein upper tail.
* `Contrib.Freedman.Kernel.HasSubgammaMGF` (+ `add_compProd`, `add_of_indep`) — kernel-valued
  sub-gamma MGF with tower additivity.
* `Contrib.Freedman.MeasureSubgammaMGF`, `Contrib.Freedman.HasCondSubgammaMGF` — the measure- and
  conditional-level analogues, and the summation lemma over an adapted sequence.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Contrib.Bennett
open scoped ENNReal NNReal Topology

namespace Contrib.Freedman

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {V c : ℝ≥0}

/-- Kernel-valued sub-gamma MGF bound.  Integrability is required for every real
parameter (rather than only the effective domain of the estimate), as in Mathlib's
kernel-valued sub-Gaussian definition; this is what makes the tower argument composable. -/
structure Kernel.HasSubgammaMGF (X : Ω → ℝ) (V c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t → (c : ℝ) * t < 1 →
    mgf X (κ ω') t ≤ exp ((V : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t)))

namespace Kernel.HasSubgammaMGF

lemma ae_integrable_exp_mul (h : Kernel.HasSubgammaMGF X V c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ exp (t * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

lemma ae_forall_integrable_exp_mul (h : Kernel.HasSubgammaMGF X V c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  have hi (n : ℤ) : ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω') :=
    h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at hi
  filter_upwards [hi] with ω' hi t
  exact integrable_exp_mul_of_le_of_le (hi _) (hi _) (Int.floor_le t) (Int.le_ceil t)

@[simp] lemma fun_zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    Kernel.HasSubgammaMGF (fun _ ↦ 0) 0 c κ ν where
  integrable_exp_mul := by simp
  mgf_le := by
    filter_upwards with ω
    intro t ht htc
    simp [mgf, measureReal_le_one]

@[simp] lemma zero_measure : Kernel.HasSubgammaMGF X V c κ (0 : Measure Ω') := ⟨by simp, by simp⟩

@[simp] lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    Kernel.HasSubgammaMGF 0 0 c κ ν := fun_zero

lemma congr {Y : Ω → ℝ} (h : Kernel.HasSubgammaMGF X V c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) :
    Kernel.HasSubgammaMGF Y V c κ ν where
  integrable_exp_mul t := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω hω using by rw [hω]
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' hm heq t ht htc
    rw [mgf_congr (Filter.EventuallyEq.symm heq)]
    exact hm t ht htc

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {Y : Ω'' → ℝ} {W : ℝ≥0}

lemma prodMkLeft_compProd {η : Kernel Ω Ω''} (h : Kernel.HasSubgammaMGF Y W c η (κ ∘ₘ ν)) :
    Kernel.HasSubgammaMGF Y W c (Kernel.prodMkLeft Ω' η) (ν ⊗ₘ κ) := by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd, Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

variable [SFinite ν]

end Kernel.HasSubgammaMGF

end Contrib.Freedman

namespace Contrib.Freedman

section Conditional
variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {V c : ℝ≥0}
  {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

variable (m) (hm) in
/-- Conditional sub-gamma MGF, expressed using the conditional-expectation kernel. -/
def HasCondSubgammaMGF (X : Ω → ℝ) (V c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Contrib.Freedman.Kernel.HasSubgammaMGF X V c (condExpKernel μ m) (μ.trim hm)

namespace HasCondSubgammaMGF

lemma integrable_exp_mul (h : HasCondSubgammaMGF m hm X V c μ) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸
    Contrib.Freedman.Kernel.HasSubgammaMGF.integrable_exp_mul h t

lemma ae_condExp_le (h : HasCondSubgammaMGF m hm X V c μ) {t : ℝ}
    (ht : 0 ≤ t) (htc : (c : ℝ) * t < 1) :
    ∀ᵐ ω ∂μ, (μ[fun x ↦ exp (t * X x) | m]) ω ≤
      exp ((V : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) := by
  have heq := condExp_ae_eq_trim_integral_condExpKernel hm
    (Contrib.Freedman.Kernel.HasSubgammaMGF.integrable_exp_mul h t)
  simp_rw [condExpKernel_comp_trim] at heq
  have hb := Contrib.Freedman.Kernel.HasSubgammaMGF.mgf_le h
  apply ae_of_ae_trim hm
  filter_upwards [heq, hb] with ω heq hb
  rw [heq]
  exact hb t ht htc

end HasCondSubgammaMGF

end Conditional

end Contrib.Freedman

namespace Contrib.Freedman

section MeasureLevel

variable {Ω Ω' : Type*} {m mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {X : Ω → ℝ} {V W c : ℝ≥0}

/-- Measure-valued sub-gamma MGF bound, including exponential integrability. -/
structure MeasureSubgammaMGF (X : Ω → ℝ) (V c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, 0 ≤ t → (c : ℝ) * t < 1 →
    mgf X μ t ≤ exp ((V : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t)))

lemma measureSubgammaMGF_iff_kernel :
    MeasureSubgammaMGF X V c μ ↔
      Kernel.HasSubgammaMGF X V c (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa, by
      filter_upwards with u
      intro t ht htc
      simpa only [Kernel.const_apply] using h2 t ht htc⟩,
    fun ⟨h1, h2⟩ ↦ ⟨by simpa using h1, by
      simpa only [ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply] using h2⟩⟩

namespace MeasureSubgammaMGF

@[simp] lemma fun_zero [IsZeroOrProbabilityMeasure μ] :
    MeasureSubgammaMGF (fun _ ↦ 0) 0 c μ := by
  simp [measureSubgammaMGF_iff_kernel]

@[simp] lemma zero [IsZeroOrProbabilityMeasure μ] : MeasureSubgammaMGF 0 0 c μ := fun_zero

lemma of_map {μ : Measure Ω'} {Y : Ω' → Ω} (hY : AEMeasurable Y μ)
    (h : MeasureSubgammaMGF X V c (μ.map Y)) : MeasureSubgammaMGF (X ∘ Y) V c μ where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t ht htc := by
    convert h.mgf_le t ht htc using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]

lemma trim (hm : m ≤ mΩ) (hXm : Measurable[m] X) (hX : MeasureSubgammaMGF X V c μ) :
    MeasureSubgammaMGF X V c (μ.trim hm) where
  integrable_exp_mul t := by
    refine (hX.integrable_exp_mul t).trim hm ?_
    exact Measurable.stronglyMeasurable <| by fun_prop
  mgf_le t ht htc := by
    rw [mgf, ← integral_trim]
    · exact hX.mgf_le t ht htc
    · exact Measurable.stronglyMeasurable <| by fun_prop

end MeasureSubgammaMGF

end MeasureLevel

section Martingale

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : Ω → ℝ} [StandardBorelSpace Ω]

variable {Y : ℕ → Ω → ℝ} {V : ℕ → ℝ≥0} {c : ℝ≥0} {ℱ : Filtration ℕ mΩ}

end Martingale

end Contrib.Freedman
