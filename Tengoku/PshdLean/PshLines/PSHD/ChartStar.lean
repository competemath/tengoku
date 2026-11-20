import Tengoku.PshdLean.PshLines.PSHD.ChartSelection
import Tengoku.PshdLean.PshLines.PSHD.ChartParameters
import Tengoku.PshdLean.PshLines.PSHD.EuclideanEnergy
import Tengoku.Seed.MeasureTheory.Measure.Haar.Basic
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Uniform finite-energy high-value stars

A bounded affine chart supplies the probability law in `pshd-vibe`, Lemma 1.3.
The law is fixed before the function and the center, so the bound is uniform.
-/

open Set Metric MeasureTheory
open scoped ENNReal

namespace PshLines.PSHD

/-- A fixed unit vector supplies uniform high-value star measures at every
positive energy order below the real dimension of its radius--chart space.-/
theorem exists_uniform_highValue_star_of_unit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]
    {e : E} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s)
    (hd : s < Module.finrank ℝ (ℝ × (ℂ ∙ e)ᗮ))
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (u : E → ℝ), Measurable u →
      ∀ (D : Set E) (x : E), closedBall x R ⊆ D →
      (∀ v : E, v ≠ 0 → DiscPshOn (fun z => (u (x + z • v) : EReal))
        ((fun z : ℂ => x + z • v) ⁻¹' D)) →
      ∃ μ : Measure E, IsProbabilityMeasure μ ∧
        μ {y | ‖y - x‖ ∈ Icc (R / 2) R ∧ u x ≤ u y} = 1 ∧
        rieszEnergy s μ ≤ C := by
  let S := ℝ × (ℂ ∙ e)ᗮ
  let c : S := (3 * R / 4, 0)
  let δ : ℝ := min (R / 4) 1
  let B : Set S := ball c δ
  let η : Measure S := Measure.addHaar
  let m : Measure S := (η B)⁻¹ • η.restrict B
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨hm, _, henergy⟩ := normalized_restrict_ball_properties (μ := η) hs hd c hδ
  let : IsProbabilityMeasure m := hm
  let a : ℝ≥0∞ := ENNReal.ofReal (min 1 (R / 4))
  have ha0 : a ≠ 0 := by dsimp [a]; positivity
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hap : a ^ s ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, ha0, hat]
  refine ⟨(a ^ s)⁻¹ * rieszEnergy s m,
    ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hap)) henergy, ?_⟩
  intro u hum D x hball hu
  obtain ⟨Ψ, hΨ, hval⟩ := exists_highValue_chart_map hum x hR hball hu he
  have hmem : ∀ᵐ p ∂m, p ∈ B :=
    Measure.ae_smul_measure (self_mem_ae_restrict measurableSet_ball) _
  have hsep : ∀ᵐ p : S × S ∂m.prod m,
      a * edist p.1 p.2 ≤ edist (Ψ p.1) (Ψ p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hmem,
      Measure.quasiMeasurePreserving_snd.ae hmem] with p hp hq
    dsimp [a]
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (chart_map_dist_lower_bound he hR.le x (fun p => (hval p).2) hp hq)
  refine ⟨m.map Ψ, Measure.isProbabilityMeasure_map hΨ.aemeasurable, ?_,
    rieszEnergy_map_le_of_ae_edist_le hs.le m hΨ ha0 hat hsep⟩
  let K : Set E := {y | ‖y - x‖ ∈ Icc (R / 2) R ∧ u x ≤ u y}
  have hK : MeasurableSet K :=
    (measurableSet_Icc.preimage (measurable_id.sub measurable_const).norm).inter
      (measurableSet_le measurable_const hum)
  have hpre : Ψ ⁻¹' K = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨hhigh, z, hz, hzp⟩ := hval p
    have hn : ‖NormedSpace.normalize (e + (p.2 : E))‖ = 1 :=
      NormedSpace.norm_normalize (affineLift_ne_zero he
        (Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property))
    refine ⟨?_, hhigh⟩
    simp only [hzp, add_sub_cancel_left, norm_smul, hn, mul_one, hz, mem_Icc]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  change m.map Ψ K = 1
  rw [Measure.map_apply hΨ hK, hpre, measure_univ]

end PshLines.PSHD
