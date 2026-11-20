import Tengoku.PshdLean.PshLines.PSHD.Localization
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Real normalized truncated averages

The localized averages in Lemma 1.2 of `pshd-vibe` are Borel functions
with the real-valued integral and normalization used in the article.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace PshLines.PSHD

/-- Joint measurability of the real truncated ball integral on a finite
measurable region, under the section hypotheses of Lemma 1.2.
@isnad1 id=measurab.6h7v.s8.1f4f8148d6d0 from=translated src=- shape=9fb0b071 vocab=e2b4af1c
-/
theorem measurable_integral_ball_min_restrict
    {X Y : Type*} [TopologicalSpace X] [SequentialSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {s : Set Y} (hs : MeasurableSet s)
    [IsFiniteMeasure (μ.restrict s)] {f : X → Y → ℝ}
    (hmeas : ∀ x, Measurable (fun y : s => f x y))
    (husc : ∀ y ∈ s, UpperSemicontinuous (fun x => f x y))
    (hpos : ∀ x, ∀ y ∈ s, 0 ≤ f x y)
    {N : ℝ} (hN : 0 ≤ N) {r : ℝ}
    (hμ : ∀ y, μ (sphere y r) = 0) :
    Measurable (fun p : X × Y =>
      ∫ y in ball p.2 r, min (f p.1 y) N ∂(μ.restrict s)) := by
  have hm := measurable_lintegral_ball_min_restrict hs
    (fun x => ENNReal.continuous_ofReal.measurable.comp (hmeas x))
    (fun y hy => ENNReal.continuous_ofReal.comp_upperSemicontinuous
      (husc y hy) ENNReal.ofReal_mono) (ENNReal.ofReal_ne_top : ENNReal.ofReal N ≠ ⊤) hμ
  have heq (p : X × Y) :
      (∫ y in ball p.2 r, min (f p.1 y) N ∂(μ.restrict s)) =
      (∫⁻ y in ball p.2 r, min (ENNReal.ofReal (f p.1 y)) (ENNReal.ofReal N)
        ∂(μ.restrict s)).toReal := by
    have hfm : AEMeasurable (f p.1) (μ.restrict s) :=
      (aemeasurable_restrict_iff_comap_subtype hs).2 (hmeas p.1).aemeasurable
    rw [integral_eq_lintegral_of_nonneg_ae]
    · simp only [ENNReal.ofReal_min]
    · filter_upwards [ae_restrict_of_ae (ae_restrict_mem hs)] with y hy
      exact le_min (hpos p.1 y hy) hN
    · exact (hfm.min aemeasurable_const).aestronglyMeasurable.restrict
  convert hm.ennreal_toReal using 1
  funext p
  exact heq p

/-- Division by a fixed normalization preserves Borel measurability.
Taking `c = Real.pi * r ^ 2` gives the planar normalization of Lemma 1.2.
@isnad1 id=measurab.6h8v.s8.b98a0231d601 from=translated src=- shape=018c1f82 vocab=d42d0741
-/
theorem measurable_normalized_integral_ball_min_restrict
    {X Y : Type*} [TopologicalSpace X] [SequentialSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {s : Set Y} (hs : MeasurableSet s)
    [IsFiniteMeasure (μ.restrict s)] {f : X → Y → ℝ}
    (hmeas : ∀ x, Measurable (fun y : s => f x y))
    (husc : ∀ y ∈ s, UpperSemicontinuous (fun x => f x y))
    (hpos : ∀ x, ∀ y ∈ s, 0 ≤ f x y)
    {N : ℝ} (hN : 0 ≤ N) {r : ℝ}
    (hμ : ∀ y, μ (sphere y r) = 0) (c : ℝ) :
    Measurable (fun p : X × Y =>
      (∫ y in ball p.2 r, min (f p.1 y) N ∂(μ.restrict s)) / c) :=
  (measurable_integral_ball_min_restrict hs hmeas husc hpos hN hμ).div_const c

end PshLines.PSHD
