import Tengoku.PshdLean.PshLines.PSHD.HighValueSelection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Measurable high-value points on affine circles

The selected points in the high-value star of `pshd-vibe`, Lemma 1.3.
-/

open Set MeasureTheory Metric

namespace PshLines.PSHD

/-- A Borel function satisfying the planar disc criterion on a measurable
family of affine lines has a measurable high-value point on each admissible
circle. The chosen point remains on its specified affine line.-/
theorem exists_measurable_highValue_circlePoint
    {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : E → ℝ} (hum : Measurable u) (x : E) {D : Set E}
    {v : S → E} {r : S → ℝ} (hv : Measurable v) (hrm : Measurable r)
    (hr : ∀ s, 0 < r s)
    (hu : ∀ s, DiscPshOn (fun z => (u (x + z • v s) : EReal))
      ((fun z : ℂ => x + z • v s) ⁻¹' D))
    (hD : ∀ s, affineClosedDisc x (v s) (r s) ⊆ D) :
    ∃ Ψ : S → E, Measurable Ψ ∧ ∀ s,
      u x ≤ u (Ψ s) ∧
      ∃ z : ℂ, ‖z‖ = r s ∧ Ψ s = x + z • v s := by
  have hcircle : Measurable (fun p : S × ℝ => circleMap 0 (r p.1) p.2) := by
    have hcont : Continuous (fun q : ℝ × ℝ => circleMap 0 q.1 q.2) := by
      unfold circleMap
      fun_prop
    exact hcont.measurable.comp ((hrm.comp measurable_fst).prodMk measurable_snd)
  have hf : Measurable (fun p : S × ℝ =>
      u (x + circleMap 0 (r p.1) p.2 • v p.1)) :=
    hum.comp (measurable_const.add (hcircle.smul (hv.comp measurable_fst)))
  obtain ⟨θ, hθ, hval⟩ := exists_measurable_highValue_phase hu hr
    (fun s z hz => hD s ⟨z, hz, rfl⟩)
    (by simp) hf
  refine ⟨fun s => x + circleMap 0 (r s) (θ s) • v s,
    measurable_const.add ((hcircle.comp (measurable_id.prodMk hθ)).smul hv), ?_⟩
  intro s
  refine ⟨by simpa using (hval s).2, circleMap 0 (r s) (θ s), ?_, rfl⟩
  rw [norm_circleMap_zero, abs_of_pos (hr s)]

end PshLines.PSHD
