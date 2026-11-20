import Tengoku.PshdLean.PshLines.PSHD.DiscRecovery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Recovery from sufficiently high truncations

Lemma 1.2 of `pshd-vibe` recovers the value from truncated fiber averages.
Compact upper bounds ensure the truncation disappears near the center.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- Every sufficiently high natural truncation has shrinking ball means
converging to the original finite disc-PSH function's value.
@isnad1 id=ex.2h5v.s8.c41828181cba from=translated src=- shape=d77b9dcc vocab=905fde13
-/
theorem exists_nat_tendsto_truncated_real_ball_average {u : E → ℝ} {U : Set E}
    (hu : DiscPshOn (fun x => (u x : EReal)) U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : E) (hUa : U ∈ 𝓝 a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Tendsto (fun r : ℝ => (∫ x in ball a r, min (u x) (N : ℝ) ∂μ) /
        (μ (ball a r)).toReal) (𝓝[>] 0) (𝓝 (u a)) := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp hUa
  have hhalf : 0 < R / 2 := half_pos hR
  have hB : closedBall a (R / 2) ⊆ U := by
    intro x hx
    apply hRU
    exact mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by linarith))
  obtain ⟨C, hC⟩ := hu.exists_compact_upper_bound (isCompact_closedBall a (R / 2))
    ⟨a, mem_closedBall_self hhalf.le⟩ hB
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge C
  refine ⟨N₀, ?_⟩
  intro N hN
  have hclip (x : E) (hx : x ∈ closedBall a (R / 2)) :
      min (u x) (N : ℝ) = u x := by
    apply min_eq_left
    have hxC : u x ≤ C := EReal.coe_le_coe_iff.mp (hC x hx)
    exact hxC.trans (hN₀.trans (Nat.cast_le.mpr hN))
  apply (tendsto_real_ball_average hu μ a hUa).congr'
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hhalf)] with r hr
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (hclip x (mem_closedBall.mpr ((mem_ball.mp hx).trans hr).le)).symm

end PshLines.PSHD
