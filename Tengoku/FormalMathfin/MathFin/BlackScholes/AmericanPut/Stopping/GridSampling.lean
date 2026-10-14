/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.Rules

/-!
# Sampling continuous-time stopping rules on a uniform grid

Rounding is upwards, so the rounded index is a stopping time for the sampled
filtration. No right-continuity or usual augmentation of the filtration is
assumed.

## Result

Public entry points include `gridFiltration`, `gridIndex`, `gridIndex_le_iff`, `gridIndex_stopping`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set Filter
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The continuous filtration sampled at the uniform grid times `i*δ`. -/
def gridFiltration (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (δ : ℝ≥0) :
    Filtration ℕ ‹MeasurableSpace Ω› where
  seq := fun i => 𝓕 ((i : ℝ≥0)*δ)
  mono' := fun _ _ hij => 𝓕.mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) zero_le)
  le' := fun i => 𝓕.le _

/-- The first grid index at or after a rule's time, `⌈θ.time ω/δ⌉₊`. -/
noncomputable def gridIndex {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (θ : BoundedRule 𝓕 T) (δ : ℝ≥0) (ω : Ω) : ℕ :=
  ⌈θ.time ω / δ⌉₊

/--
@isnad1 id=iff.1h7v.s6.f9797ed5b808 from=translated src=- shape=86da04b7 vocab=7a16e93d
-/
theorem gridIndex_le_iff {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}
    (θ : BoundedRule 𝓕 T) (hδ : 0 < δ) (ω : Ω) (i : ℕ) :
    gridIndex θ δ ω ≤ i ↔ θ.time ω ≤ (i : ℝ≥0)*δ := by
  simp only [gridIndex,Nat.ceil_le,div_le_iff₀ hδ]

/--
@isnad1 id=isstoppi.1h5v.s5.219ac92a1d27 from=translated src=- shape=98960912 vocab=c15fc156
-/
theorem gridIndex_stopping {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}
    (θ : BoundedRule 𝓕 T) (hδ : 0 < δ) :
    IsStoppingTime (gridFiltration 𝓕 δ) (fun ω => (gridIndex θ δ ω : ℕ∞)) := by
  intro i
  change MeasurableSet[𝓕 ((i : ℝ≥0)*δ)] {ω | (gridIndex θ δ ω : ℕ∞) ≤ i}
  simpa only [ENat.natCast_le_natCast,WithTop.coe_le_coe,gridIndex_le_iff θ hδ] using θ.stopping ((i : ℝ≥0)*δ)

/--
@isnad1 id=le.0h6v.s5.c5f6253adf33 from=translated src=- shape=62f0a02d vocab=b122f427
-/
theorem gridIndex_bounded {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}
    (θ : BoundedRule 𝓕 T) (ω : Ω) : gridIndex θ δ ω ≤ ⌈T/δ⌉₊ :=
  Nat.ceil_mono (div_le_div_of_nonneg_right (θ.le_horizon ω) zero_le)

/--
@isnad1 id=supermar.1h5v.s6.46375259267b from=translated src=- shape=7f8549ea vocab=2c278e7e
-/
theorem supermartingale_grid {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {P : Measure Ω} {U : ℝ≥0 → Ω → ℝ} (hU : Supermartingale U 𝓕 P) (δ : ℝ≥0) :
    Supermartingale (fun i : ℕ => U ((i : ℝ≥0)*δ)) (gridFiltration 𝓕 δ) P := by
  refine ⟨fun i => hU.stronglyAdapted _, ?_, fun i => hU.integrable _⟩
  intro i j hij
  exact hU.2.1 _ _ (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) zero_le)

/--
@isnad1 id=le.2h7v.s7.4dd7586a25d9 from=translated src=- shape=45625c82 vocab=82f659c7
-/
theorem expected_gridValue_le {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {P : Measure Ω} [IsFiniteMeasure P] {U : ℝ≥0 → Ω → ℝ}
    (hU : Supermartingale U 𝓕 P) {T δ : ℝ≥0}
    (θ : BoundedRule 𝓕 T) (hδ : 0 < δ) :
    (∫ ω, U ((gridIndex θ δ ω : ℝ≥0)*δ) ω ∂P) ≤ ∫ ω, U 0 ω ∂P := by
  have hh := (supermartingale_grid hU δ).neg.expected_stoppedValue_mono
    (isStoppingTime_const (gridFiltration 𝓕 δ) 0) (gridIndex_stopping θ hδ)
    (fun ω => bot_le) (fun ω => show (gridIndex θ δ ω : ℕ∞) ≤ (⌈T/δ⌉₊ : ℕ) by
      exact_mod_cast gridIndex_bounded θ ω)
  simpa [stoppedValue,integral_neg] using hh

/-- The mesh `((n : ℝ≥0)+1)⁻¹` of the `n`-th grid refinement. -/
noncomputable def gridStep (n : ℕ) : ℝ≥0 := ((n : ℝ≥0)+1)⁻¹

/--
@isnad1 id=lt.0h1v.s4.31e199723f28 from=translated src=- shape=b9369acb vocab=a1da25e3
-/
theorem gridStep_pos (n : ℕ) : 0 < gridStep n := by
  unfold gridStep
  positivity

/--
@isnad1 id=tendsto.0h5v.s6.5767996eade4 from=translated src=- shape=1ddfe54f vocab=561e5c1a
-/
theorem gridValue_time_tendsto {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T : ℝ≥0}
    (θ : BoundedRule 𝓕 T) (ω : Ω) :
    Tendsto (fun n => (gridIndex θ (gridStep n) ω : ℝ≥0)*gridStep n)
      atTop (𝓝 (θ.time ω)) := by
  apply NNReal.tendsto_coe.mp
  have hh := (tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := (θ.time ω : ℝ)) (θ.time ω).coe_nonneg).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hceil (x : ℝ≥0) : ⌈x⌉₊ = ⌈(x : ℝ)⌉₊ := by
    apply Nat.le_antisymm
    · rw [Nat.ceil_le]
      exact_mod_cast Nat.le_ceil (x : ℝ)
    · rw [Nat.ceil_le]
      exact_mod_cast Nat.le_ceil x
  simpa [Function.comp_def,gridIndex,gridStep,div_eq_mul_inv,hceil] using hh

/--
@isnad1 id=measurab.0h5v.s5.b8083e551b0c from=translated src=- shape=a1a95495 vocab=af21960c
-/
theorem gridIndex_measurable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {T δ : ℝ≥0}
    (θ : BoundedRule 𝓕 T) : Measurable (gridIndex θ δ) :=
  Nat.measurable_ceil.comp (θ.measurable_time.div_const δ)

/-- Bounded continuous-path optional stopping. This is derived from discrete
optional stopping, not assumed as an axiom or as a pricing-contract field.
@isnad1 id=le.3h7v.s7.d4dae881ab63 from=translated src=- shape=1c1ad4f3 vocab=85572d47
-/
theorem expected_stoppedValue_le_initial {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {P : Measure Ω} [IsFiniteMeasure P] {U : ℝ≥0 → Ω → ℝ}
    (hU : Supermartingale U 𝓕 P) (hcont : ∀ ω, Continuous (fun t => U t ω))
    {C : ℝ} (hbound : ∀ t ω, ‖U t ω‖ ≤ C) {T : ℝ≥0} (θ : BoundedRule 𝓕 T) :
    (∫ ω, U (θ.time ω) ω ∂P) ≤ ∫ ω, U 0 ω ∂P := by
  have hmeas : Measurable U.uncurry :=
    measurable_uncurry_of_continuous_of_measurable hcont
      (fun t => (hU.stronglyAdapted t).measurable.mono (𝓕.le t) le_rfl)
  have hlim := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => C)
    (F := fun n ω => U ((gridIndex θ (gridStep n) ω : ℝ≥0)*gridStep n) ω)
    (f := fun ω => U (θ.time ω) ω)
    (fun n => (hmeas.comp ((show Measurable (fun ω =>
      (gridIndex θ (gridStep n) ω : ℝ≥0)*gridStep n) by
        exact ((measurable_from_nat : Measurable (fun i : ℕ => (i : ℝ≥0))).comp
          (gridIndex_measurable θ)).mul_const _).prodMk measurable_id)).aestronglyMeasurable)
    (integrable_const C) (fun n => Filter.Eventually.of_forall (fun ω => hbound _ ω))
    (Filter.Eventually.of_forall (fun ω =>
      ((hcont ω).tendsto (θ.time ω)).comp (gridValue_time_tendsto θ ω)))
  exact le_of_tendsto hlim (Filter.Eventually.of_forall
    (fun n => expected_gridValue_le hU θ (gridStep_pos n)))

/--
@isnad1 id=eq.3h7v.s7.0b1d30877fb7 from=translated src=- shape=909b7cfc vocab=b3a6dd77
-/
theorem expected_stoppedValue_eq_initial {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {P : Measure Ω} [IsFiniteMeasure P] {U : ℝ≥0 → Ω → ℝ}
    (hU : Martingale U 𝓕 P) (hcont : ∀ ω, Continuous (fun t => U t ω))
    {C : ℝ} (hbound : ∀ t ω, ‖U t ω‖ ≤ C) {T : ℝ≥0} (θ : BoundedRule 𝓕 T) :
    (∫ ω, U (θ.time ω) ω ∂P) = ∫ ω, U 0 ω ∂P := by
  apply le_antisymm (expected_stoppedValue_le_initial hU.supermartingale hcont hbound θ)
  have hh := expected_stoppedValue_le_initial hU.neg.supermartingale
    (fun ω => (hcont ω).neg) (fun t ω => by simpa using hbound t ω) θ
  simpa only [Pi.neg_apply,integral_neg,neg_le_neg_iff] using hh

end MathFin.BlackScholes.AmericanPut.Stopping
