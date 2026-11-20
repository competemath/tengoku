import Tengoku.PshdLean.PshLines.PSHD.CirclePointSelection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # High-value star pushforward measures

The probability-measure construction in `pshd-vibe`, Lemma 1.3.
The radial and directional distribution is retained as an explicit parameter
for the subsequent energy estimate.
-/

open Set MeasureTheory Metric

namespace PshLines.PSHD

/-- Any probability distribution of admissible radii and unit directions can
be lifted measurably to high-value points, and its pushforward gives full mass
to the high-value annulus. The lift preserves each specified complex line.-/
theorem exists_highValue_annulus_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : E → ℝ} (hum : Measurable u) {D : Set E} (x : E)
    {R : ℝ} (hR : 0 < R) (hball : closedBall x R ⊆ D)
    (hu : ∀ v : E, v ≠ 0 → DiscPshOn (fun z => (u (x + z • v) : EReal))
      ((fun z : ℂ => x + z • v) ⁻¹' D))
    (m : Measure (Icc (R / 2) R × sphere (0 : E) 1)) [IsProbabilityMeasure m] :
    ∃ Ψ : (Icc (R / 2) R × sphere (0 : E) 1) → E, Measurable Ψ ∧
      (∀ s, u x ≤ u (Ψ s) ∧ ∃ z : ℂ,
        ‖z‖ = (s.1 : ℝ) ∧ Ψ s = x + z • (s.2 : E)) ∧
      m.map Ψ {y | ‖y - x‖ ∈ Icc (R / 2) R ∧ u x ≤ u y} = 1 := by
  let S := Icc (R / 2) R × sphere (0 : E) 1
  have hv : Measurable (fun s : S => (s.2 : E)) :=
    measurable_subtype_coe.comp measurable_snd
  have hrm : Measurable (fun s : S => (s.1 : ℝ)) :=
    measurable_subtype_coe.comp measurable_fst
  have hr : ∀ s : S, 0 < (s.1 : ℝ) :=
    fun s => (half_pos hR).trans_le s.1.property.1
  have hn : ∀ s : S, ‖(s.2 : E)‖ = 1 := fun s => by simp
  have hdisc : ∀ s : S, affineClosedDisc x (s.2 : E) (s.1 : ℝ) ⊆ D := by
    rintro s y ⟨z, hz, rfl⟩
    apply hball
    have hz' : ‖z‖ ≤ (s.1 : ℝ) := by simpa using hz
    simpa [mem_closedBall, dist_eq_norm, norm_smul, hn s] using
      hz'.trans s.1.property.2
  obtain ⟨Ψ, hΨ, hval⟩ := exists_measurable_highValue_circlePoint hum x hv hrm hr
    (fun s => hu _ (norm_ne_zero_iff.mp (by rw [hn s]; exact one_ne_zero))) hdisc
  refine ⟨Ψ, hΨ, hval, ?_⟩
  let K : Set E := {y | ‖y - x‖ ∈ Icc (R / 2) R ∧ u x ≤ u y}
  have hK : MeasurableSet K :=
    (measurableSet_Icc.preimage (measurable_id.sub measurable_const).norm).inter
      (measurableSet_le measurable_const hum)
  have hmem : ∀ s, Ψ s ∈ K := by
    intro s
    obtain ⟨hhigh, z, hz, heq⟩ := hval s
    refine ⟨?_, hhigh⟩
    simp [heq, norm_smul, hz, hn s]
  change m.map Ψ K = 1
  have hpre : Ψ ⁻¹' K = univ := by
    ext s
    exact iff_of_true (hmem s) (mem_univ s)
  rw [Measure.map_apply hΨ hK, hpre, measure_univ]

end PshLines.PSHD
