import Tengoku.PshdLean.PshLines.PSHD.Measurability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Localized truncated averages

The section hypotheses in Lemma 1.2 of `pshd-vibe` are only available on
the larger disc. Zero extension allows joint measurability to be applied
without imposing hypotheses outside that disc.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace PshLines.PSHD

/-- Localize the joint measurability theorem to a measurable region of finite
measure. Only sections on this region need to be measurable or upper
semicontinuous.-/
theorem measurable_lintegral_ball_min_restrict
    {X Y : Type*} [TopologicalSpace X] [SequentialSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {μ : Measure Y} {s : Set Y} (hs : MeasurableSet s)
    [IsFiniteMeasure (μ.restrict s)] {f : X → Y → ℝ≥0∞}
    (hmeas : ∀ x, Measurable (fun y : s => f x y))
    (husc : ∀ y ∈ s, UpperSemicontinuous (fun x => f x y))
    {N : ℝ≥0∞} (hN : N ≠ ⊤) {r : ℝ}
    (hμ : ∀ y, μ (sphere y r) = 0) :
    Measurable (fun p : X × Y =>
      ∫⁻ y in ball p.2 r, min (f p.1 y) N ∂(μ.restrict s)) := by
  classical
  let g : X → Y → ℝ≥0∞ := fun x => s.indicator (f x)
  have hgm : ∀ x, Measurable (g x) := by
    intro x
    apply measurable_of_restrict_of_restrict_compl hs
    · convert hmeas x using 1
      funext y
      simp [g, Set.domRestrict, y.property]
    · have heq : sᶜ.domRestrict (g x) = fun _ : (sᶜ : Set Y) => (0 : ℝ≥0∞) := by
        funext y
        exact indicator_of_notMem y.property _
      rw [heq]
      exact measurable_const
  have hgu : ∀ y, UpperSemicontinuous (fun x => g x y) := by
    intro y
    by_cases hy : y ∈ s
    · simpa only [g, indicator_of_mem hy] using husc y hy
    · simpa only [g, indicator_of_notMem hy] using
        (upperSemicontinuous_const : UpperSemicontinuous (fun _ : X => (0 : ℝ≥0∞)))
  have hnull : ∀ y, (μ.restrict s) (sphere y r) = 0 := by
    intro y
    exact le_antisymm ((Measure.restrict_apply_le s (sphere y r)).trans_eq (hμ y)) bot_le
  have hm := measurable_lintegral_ball_min (μ := μ.restrict s) hgm hgu hN hnull
  convert hm using 1
  funext p
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_restrict_mem hs)] with y hy
  simp [g, hy]

end PshLines.PSHD
