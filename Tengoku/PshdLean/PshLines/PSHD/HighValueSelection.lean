import Tengoku.PshdLean.PshLines.PSHD.PositiveMeasureSelection
import Tengoku.PshdLean.PshLines.PSHD.AngularSections
import Tengoku.PshdLean.PshLines.PSHD.HighValueMass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Borel selection of high-value phases

An explicit positive-measure selection proof of the choice step in
`pshd-vibe`, Lemma 1.3. Only the planar restrictions have semicontinuity.
-/

open Set MeasureTheory Metric

namespace PshLines.PSHD

/-- A measurable family of subharmonic circle restrictions admits a Borel
choice of an angle with value at least the central value.
@isnad1 id=ex.5h4v.s7.5cf354b787b7 from=translated src=- shape=2faea539 vocab=fa49e375
-/
theorem exists_measurable_highValue_phase
    {S : Type*} [MeasurableSpace S]
    {u : S → ℂ → ℝ} {U : S → Set ℂ} {r : S → ℝ}
    (hu : ∀ s, DiscPshOn (fun z => (u s z : EReal)) (U s))
    (hr : ∀ s, 0 < r s) (hD : ∀ s, closedBall (0 : ℂ) (r s) ⊆ U s)
    (hc : Measurable (fun s => u s 0))
    (hf : Measurable (fun p : S × ℝ => u p.1 (circleMap 0 (r p.1) p.2))) :
    ∃ θ : S → ℝ, Measurable θ ∧ ∀ s,
      θ s ∈ Icc 0 (2 * Real.pi) ∧ u s 0 ≤ u s (circleMap 0 (r s) (θ s)) := by
  let K : Set (S × ℝ) := {p | p.2 ∈ Icc 0 (2 * Real.pi) ∧
    u p.1 0 ≤ u p.1 (circleMap 0 (r p.1) p.2)}
  have hK : MeasurableSet K :=
    (measurableSet_Icc.preimage measurable_snd).inter
      (measurableSet_le (hc.comp measurable_fst) hf)
  have hclosed : ∀ s, IsClosed (Prod.mk s ⁻¹' K) := by
    intro s
    exact (isCompact_highValue_angles (hu s) (hr s).le (hD s) (u s 0)).isClosed
  have hbound : ∀ s, Prod.mk s ⁻¹' K ⊆ Icc 0 (2 * Real.pi) :=
    fun _ _ h => h.1
  have hpos : ∀ s, 0 < volume (Prod.mk s ⁻¹' K) := by
    intro s
    have hdisc : affineClosedDisc (0 : ℂ) 1 (r s) ⊆ U s := by
      simpa [affineClosedDisc] using hD s
    have hm := volume_highValue_angles_pos (hu s) 0 1 (hr s) hdisc
    simp only [smul_eq_mul, mul_one, zero_add] at hm
    exact hm.trans_le (measure_mono (fun _ h => ⟨⟨h.1.1.le, h.1.2⟩, h.2⟩))
  exact exists_measurable_mem_of_closed_positive_sections hK hclosed hbound hpos

end PshLines.PSHD
