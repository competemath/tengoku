import Tengoku.PshdLean.PshLines.PSHD.Measurability
import Tengoku.PshdLean.PshLines.PSHD.TruncatedRecovery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Measurability from eventual recovery by truncated averages

The truncation threshold may depend on the point. No measurability of
that threshold is needed in the double-limit argument of Lemma 1.2.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PshLines.PSHD

/-- If every sufficiently high row of a measurable double sequence converges
to the same value at each point, that value is measurable.-/
theorem measurable_of_eventually_tendsto
    {X : Type*} [MeasurableSpace X] {f : ℕ → ℕ → X → ℝ} {u : X → ℝ}
    (hf : ∀ N k, Measurable (f N k))
    (hu : ∀ x, ∀ᶠ N in atTop, Tendsto (fun k => f N k x) atTop (𝓝 (u x))) :
    Measurable u := by
  have hm : Measurable (fun x =>
      limsup (fun N => limsup (fun k => f N k x) atTop) atTop) :=
    Measurable.limsup (fun N => Measurable.limsup (hf N))
  convert hm using 1
  funext x
  symm
  apply Filter.Tendsto.limsup_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [hu x] with N hN
  exact hN.limsup_eq.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- Restricting the integration measure to a neighborhood of the center
does not change eventual recovery by the upper-truncated ball means.-/
theorem exists_nat_tendsto_truncated_real_ball_average_restrict
    {u : E → ℝ} {U s : Set E}
    (hu : DiscPshOn (fun x => (u x : EReal)) U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) (hUa : U ∈ 𝓝 a) (hsa : s ∈ 𝓝 a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Tendsto (fun r : ℝ => (∫ x in ball a r, min (u x) (N : ℝ) ∂(μ.restrict s)) /
        (μ (ball a r)).toReal) (𝓝[>] 0) (𝓝 (u a)) := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_tendsto_truncated_real_ball_average hu μ a hUa
  obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.mp hsa
  refine ⟨N₀, fun N hN => (hN₀ N hN).congr' ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hR)] with r hr
  have hbs : ball a r ⊆ s := (ball_subset_ball hr.le).trans hRs
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hbs]

end PshLines.PSHD
