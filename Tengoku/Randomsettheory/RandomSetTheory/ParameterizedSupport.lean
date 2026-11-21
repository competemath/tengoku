/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosCaratheodory
import Tengoku.Randomsettheory.RandomSetTheory.SupportSelection
import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parameterized support integrals

The support of a parameter-dependent Carathéodory image is jointly
measurable in the observation, parameter, and support direction.  Integrating
out the observation therefore leaves a measurable function of the parameter
and direction.  In finite dimension, the closed Aumann support identity
identifies this integral with the support function of the population Aumann
moment correspondence.

This is the measurability bridge used before treating the support class as an
empirical process in Section 5 of the report.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory TopologicalSpace
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- A jointly measurable real integrand remains measurable in its external
parameter after integrating over an `SFinite` measure.
@isnad1 id=measurab.1h4v.s6.b7d895860530 from=translated src=- shape=92421cc1 vocab=a6d007de
-/
theorem measurable_integral_prod_right_of_measurable
    {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {f : A × Ω → ℝ} (hf : Measurable f) :
    Measurable (fun a => ∫ ω, f (a, ω) ∂μ) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

/-- Joint measurability in `(θ,u)` of the integrated support function of a
parameter-dependent Carathéodory image.
@isnad1 id=measurab.5h7v.s8.09f7658a477a from=translated src=- shape=193ac29c vocab=a6eca656
-/
theorem measurable_integral_supportFunction_caratheodoryImage_param
    {Ω Θ X H : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    (μ : Measure Ω) [SFinite μ]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : (Ω × Θ) × X → H} (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x)) :
    Measurable (fun q : Θ × H =>
      ∫ ω, supportFunction
        ((fun x => φ ((ω, q.1), x)) '' S ω) q.2 ∂μ) := by
  have hsupp := measurable_supportFunction_caratheodoryImage_param_joint
    hS hcompact hne hφmeas hφcont
  have hreassoc : Measurable
      (fun q : (Θ × H) × Ω => ((q.2, q.1.1), q.1.2)) :=
    (measurable_snd.prodMk measurable_fst.fst).prodMk measurable_fst.snd
  have hintegrand : Measurable (fun q : (Θ × H) × Ω =>
      supportFunction
        ((fun x => φ ((q.2, q.1.1), x)) '' S q.2) q.1.2) :=
    hsupp.comp hreassoc
  exact measurable_integral_prod_right_of_measurable μ hintegrand

/-- In finite dimension, the preceding measurable integral is exactly the
joint support function of the closed parameterized Aumann expectation.
Compactness of each closure is discharged by the common integrable envelope.
@isnad1 id=measurab.7h8v.s8.dc4af004b983 from=translated src=- shape=bac7d268 vocab=7d66de64
-/
theorem measurable_supportFunction_closure_aumannExpectation_caratheodoryImage_param
    {Ω Θ X H : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [Nonempty X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    [FiniteDimensional ℝ H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Ω → Set X} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {φ : (Ω × Θ) × X → H} (hφmeas : Measurable φ)
    (hφcont : ∀ p : Ω × Θ, Continuous fun x => φ (p, x))
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω θ, ∀ y ∈ (fun x => φ ((ω, θ), x)) '' S ω,
      ‖y‖ ≤ g ω) :
    Measurable (fun q : Θ × H =>
      supportFunction
        (closure (aumannExpectation μ
          (fun ω => (fun x => φ ((ω, q.1), x)) '' S ω))) q.2) := by
  let Φ : Θ → Ω → Set H := fun θ ω =>
    (fun x => φ ((ω, θ), x)) '' S ω
  have hΦparam : RandomSet.IsEffrosMeasurable
      (fun p : Ω × Θ => Φ p.2 p.1) := by
    simpa only [Φ] using
      effrosMeasurable_caratheodoryImage_param
        hS (fun ω => (hcompact ω).isClosed) hne hφmeas hφcont
  have hΦ : ∀ θ, RandomSet.IsEffrosMeasurable (Φ θ) := by
    intro θ U hU
    have hEq :
        {ω | (Φ θ ω ∩ U).Nonempty} =
          (fun ω => (ω, θ)) ⁻¹'
            {p : Ω × Θ | (Φ p.2 p.1 ∩ U).Nonempty} := by
      ext ω
      rfl
    rw [hEq]
    exact (measurable_id.prodMk measurable_const) (hΦparam U hU)
  have hΦcompact : ∀ θ ω, IsCompact (Φ θ ω) := fun θ ω =>
    (hcompact ω).image (hφcont (ω, θ))
  have hΦne : ∀ θ ω, (Φ θ ω).Nonempty := fun θ ω =>
    (hne ω).image (fun x => φ ((ω, θ), x))
  have hAcompact : ∀ θ,
      IsCompact (closure (aumannExpectation μ (Φ θ))) := by
    intro θ
    exact closure_aumannExpectation_compact_of_integrable_envelope hg
      (Filter.Eventually.of_forall fun ω y hy => hdom ω θ y hy)
  have hEq : (fun q : Θ × H =>
      supportFunction (closure (aumannExpectation μ (Φ q.1))) q.2) =
      (fun q : Θ × H =>
        ∫ ω, supportFunction (Φ q.1 ω) q.2 ∂μ) := by
    funext q
    exact supportFunction_closure_aumannExpectation_of_envelope
      (hΦ q.1) (hΦcompact q.1) (hΦne q.1) hg
      (fun ω y hy => hdom ω q.1 y hy) (hAcompact q.1) q.2
  change Measurable (fun q : Θ × H =>
    supportFunction (closure (aumannExpectation μ (Φ q.1))) q.2)
  rw [hEq]
  simpa only [Φ] using
    measurable_integral_supportFunction_caratheodoryImage_param
      μ hS hcompact hne hφmeas hφcont

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
