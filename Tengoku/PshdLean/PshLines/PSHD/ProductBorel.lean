import Tengoku.PshdLean.PshLines.PSHD.NormalizedAverage
import Tengoku.PshdLean.PshLines.PSHD.IteratedRecovery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Borel measurability on products with a planar region

This is the local product argument in Lemma 1.2 of `pshd-vibe`, using
the project's disc criterion on the individual complex fibers.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace PshLines.PSHD

set_option maxHeartbeats 800000 in
/-- A nonnegative function with upper semicontinuous horizontal sections
and disc-PSH vertical sections is jointly Borel on a product with an open
planar region of finite area.
@isnad1 id=measurab.4h3v.s7.f80d4722d95f from=translated src=- shape=2943b5c4 vocab=18e7aace
-/
theorem measurable_on_product_of_discPsh
    {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {s : Set ℂ} (hs : IsOpen s) [IsFiniteMeasure (volume.restrict s)]
    {f : X → ℂ → ℝ}
    (husc : ∀ y ∈ s, UpperSemicontinuous (fun x => f x y))
    (hpos : ∀ x, ∀ y ∈ s, 0 ≤ f x y)
    (hpsh : ∀ x, DiscPshOn (fun y => (f x y : EReal)) s) :
    Measurable (fun p : X × s => f p.1 p.2) := by
  have hmeas : ∀ x, Measurable (fun y : s => f x y) := by
    intro x
    have hm := (upperSemicontinuousOn_iff_restrict.mpr
      (hpsh x).upperSemicontinuousOn).measurable.ereal_toReal
    simpa using hm
  let r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hr : Tendsto r atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun k => by
        change 0 < 1 / ((k : ℝ) + 1)
        positivity)⟩
  let F : ℕ → ℕ → X × s → ℝ := fun N k p =>
    (∫ y in ball (p.2 : ℂ) (r k), min (f p.1 y) (N : ℝ)
      ∂(volume.restrict s)) / (volume (ball (0 : ℂ) (r k))).toReal
  apply measurable_of_eventually_tendsto (f := F)
  · intro N k
    have hm : Measurable (fun p : X × ℂ =>
        (∫ y in ball p.2 (r k), min (f p.1 y) (N : ℝ) ∂(volume.restrict s)) /
          (volume (ball (0 : ℂ) (r k))).toReal) :=
      measurable_normalized_integral_ball_min_restrict
      (μ := (volume : Measure ℂ)) (s := s) (f := f) (N := (N : ℝ)) (r := r k)
      hs.measurableSet
      hmeas husc hpos (Nat.cast_nonneg N)
      (fun y => (volume : Measure ℂ).addHaar_sphere y (r k))
      (volume (ball (0 : ℂ) (r k))).toReal
    have hmap : Measurable (fun p : X × s => (p.1, (p.2 : ℂ))) :=
      measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
    exact hm.comp hmap
  · intro p
    obtain ⟨N₀, hN₀⟩ := exists_nat_tendsto_truncated_real_ball_average_restrict
      (hpsh p.1) volume p.2 (hs.mem_nhds p.2.property) (hs.mem_nhds p.2.property)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have ht := (hN₀ N hN).comp hr
    convert ht using 1
    funext k
    have hm : volume (ball (0 : ℂ) (r k)) = volume (ball (p.2 : ℂ) (r k)) := by
      simpa using lintegral_ball_add (volume : Measure ℂ)
        (fun _ => (1 : ℝ≥0∞)) (p.2 : ℂ) (r k)
    simp only [F, hm, Function.comp_def]

end PshLines.PSHD
