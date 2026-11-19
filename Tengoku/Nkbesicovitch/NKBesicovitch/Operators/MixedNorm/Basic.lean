/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.Indicator
public import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Tengoku.Seed.MeasureTheory.Measure.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mixed norms of nonnegative functions

The inner norm integrates the first coordinate. The outer norm integrates
the second coordinate, which is the direction variable for line families.
Both norms use Mathlib's extended-valued `eLpNorm`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace NKBesicovitch

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {q r : ℝ≥0∞} {f g : X × Y → ℝ≥0∞}

/-- The `L^q` norm in the second variable of the `L^r` norm in the first variable.-/
noncomputable def mixedNorm (f : X × Y → ℝ≥0∞) (q r : ℝ≥0∞)
    (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  eLpNorm (fun y ↦ eLpNorm (fun x ↦ f (x, y)) r μ) q ν

/--
@isnad1 id=eq.1h8v.s6.523d7191dd28 from=translated src=- shape=8fb71897 vocab=7c855ba1
-/
theorem mixedNorm_indicator_snd {A : Set Y} (hA : MeasurableSet A) :
    mixedNorm ((Prod.snd ⁻¹' A).indicator f) q r μ ν =
      mixedNorm f q r μ (ν.restrict A) := by
  unfold mixedNorm
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hA]
  congr 1
  funext y
  by_cases hy : y ∈ A
  · simp only [indicator_of_mem hy, mem_preimage, hy, indicator_of_mem]
  · have hx (x : X) : (x, y) ∉ Prod.snd ⁻¹' A := hy
    simp only [indicator_of_notMem hy, indicator_of_notMem (hx _)]
    exact eLpNorm_zero

/--
@isnad1 id=le.1h8v.s6.765e7f67166c from=translated src=- shape=683bc11e vocab=3be6f208
-/
theorem mixedNorm_mono (h : f ≤ g) : mixedNorm f q r μ ν ≤ mixedNorm g q r μ ν := by
  apply eLpNorm_mono_enorm
  intro y
  simp only [enorm_eq_self]
  exact eLpNorm_mono_enorm (fun x ↦ by simpa only [enorm_eq_self] using h (x, y))

/--
@isnad1 id=le.1h8v.s6.451fe18fb695 from=translated src=- shape=5f9afbd9 vocab=6765d960
-/
theorem mixedNorm_mono_fiber_ae (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x, y) ≤ g (x, y)) :
    mixedNorm f q r μ ν ≤ mixedNorm g q r μ ν := by
  apply eLpNorm_mono_enorm_ae
  filter_upwards [h] with y hy
  simp only [enorm_eq_self]
  exact eLpNorm_mono_enorm_ae (by simpa only [enorm_eq_self] using hy)

/--
@isnad1 id=le.1h9v.s7.43480098acdc from=translated src=- shape=d64628d1 vocab=2e1543d3
-/
theorem mixedNorm_le_const_mul_of_fiber_ae {c : ℝ≥0}
    (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, f (x, y) ≤ c * g (x, y)) :
    mixedNorm f q r μ ν ≤ c * mixedNorm g q r μ ν := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
  filter_upwards [h] with y hy
  simp only [enorm_eq_self]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'
    (by simpa only [enorm_eq_self] using hy) r

/--
@isnad1 id=le.0h8v.s6.9645bab4b616 from=translated src=- shape=b5a5dc7e vocab=a4e79970
-/
theorem mixedNorm_const_mul_le (c : ℝ≥0) (f : X × Y → ℝ≥0∞) :
    mixedNorm (fun p ↦ c * f p) q r μ ν ≤ c * mixedNorm f q r μ ν :=
  mixedNorm_le_const_mul_of_fiber_ae (ae_of_all _ fun _ ↦ ae_of_all _ fun _ ↦ le_rfl)

/--
@isnad1 id=measurab.3h5v.s6.afabcfcb79a3 from=translated src=- shape=42dbf2bb vocab=7c5bdb97
-/
theorem measurable_eLpNorm_fiber [SFinite μ] (hf : Measurable f) (hr : r ≠ 0)
    (hrfin : r ≠ ∞) : Measurable (fun y ↦ eLpNorm (fun x ↦ f (x, y)) r μ) := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr hrfin, enorm_eq_self]
  exact (hf.pow_const r.toReal).lintegral_prod_left'.pow_const _

/--
@isnad1 id=le.5h8v.s7.5df722cfc993 from=translated src=- shape=ab50bd19 vocab=01538629
-/
theorem mixedNorm_add_le [SFinite μ] (hf : Measurable f) (hg : Measurable g)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hrfin : r ≠ ∞) :
    mixedNorm (f + g) q r μ ν ≤ mixedNorm f q r μ ν + mixedNorm g q r μ ν := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  calc
    _ ≤ eLpNorm (fun y ↦ eLpNorm (fun x ↦ f (x, y)) r μ +
        eLpNorm (fun x ↦ g (x, y)) r μ) q ν := by
      apply eLpNorm_mono_enorm
      intro y
      simp only [enorm_eq_self]
      exact eLpNorm_add_le (hf.comp measurable_prodMk_right).aestronglyMeasurable
        (hg.comp measurable_prodMk_right).aestronglyMeasurable hr
    _ ≤ _ := eLpNorm_add_le (measurable_eLpNorm_fiber hf hr0 hrfin).aestronglyMeasurable
      (measurable_eLpNorm_fiber hg hr0 hrfin).aestronglyMeasurable hq

/-- The outer power of an indicator mixed norm is an integral of fiber measures.
@isnad1 id=eq.3h7v.s7.c9ac200bd9d0 from=translated src=- shape=d2f287bc vocab=81232188
-/
theorem mixedNorm_indicator_rpow {F : Set (X × Y)} (hF : MeasurableSet F)
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    mixedNorm (F.indicator (fun _ ↦ (1 : ℝ≥0∞))) (ENNReal.ofReal q)
      (ENNReal.ofReal r) μ ν ^ q =
        ∫⁻ y, μ ((fun x ↦ (x, y)) ⁻¹' F) ^ (q / r) ∂ν := by
  have hinner (y : Y) :
      eLpNorm (fun x ↦ F.indicator (fun _ ↦ (1 : ℝ≥0∞)) (x, y)) (ENNReal.ofReal r) μ =
        μ ((fun x ↦ (x, y)) ⁻¹' F) ^ (1 / r) := by
    simp_rw [← indicator_comp_right (fun x ↦ (x, y))]
    change eLpNorm (((fun x ↦ (x, y)) ⁻¹' F).indicator (fun _ ↦ (1 : ℝ≥0∞))) _ _ = _
    simp only [eLpNorm_indicator_const (hF.preimage measurable_prodMk_right)
      (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top,
      enorm_eq_self, ENNReal.toReal_ofReal hr.le, one_mul]
  simp only [mixedNorm, hinner,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hq).ne'
      ENNReal.ofReal_ne_top, enorm_eq_self, ENNReal.toReal_ofReal hq.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  congr 1
  funext y
  congr 1
  ring

end NKBesicovitch
