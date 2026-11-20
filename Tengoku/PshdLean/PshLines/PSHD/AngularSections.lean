import Tengoku.PshdLean.PshLines.Plurisubharmonic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Compact Borel angular sections

Angular coordinates for the high-value sections in `pshd-vibe`, Lemma 1.3.
-/

open Set MeasureTheory

namespace PshLines.PSHD

/-- The high-value angles, including both endpoints of a full turn, form a
compact real set. The disc criterion is needed only along the given line.-/
theorem isCompact_highValue_angles
    {u : ℂ → ℝ} {U : Set ℂ}
    (hu : DiscPshOn (fun z => (u z : EReal)) U)
    {r : ℝ} (hr : 0 ≤ r) (hD : Metric.closedBall (0 : ℂ) r ⊆ U) (A : ℝ) :
    IsCompact {t ∈ Icc 0 (2 * Real.pi) | A ≤ u (circleMap 0 r t)} := by
  have hsc : UpperSemicontinuous (fun t : ℝ => (u (circleMap 0 r t) : EReal)) := by
    apply upperSemicontinuousOn_univ_iff.mp
    exact hu.upperSemicontinuousOn.comp (continuous_circleMap 0 r).continuousOn
      (fun t _ => hD (Metric.sphere_subset_closedBall (circleMap_mem_sphere 0 hr t)))
  have hc : IsClosed {t : ℝ | A ≤ u (circleMap 0 r t)} := by
    simpa only [preimage, mem_Ici, EReal.coe_le_coe_iff] using
      hsc.isClosed_preimage (A : EReal)
  exact isCompact_Icc.inter_right hc

/-- A Borel ambient function gives a Borel family of angular high-value sets
under measurable affine-circle parameters.-/
theorem measurableSet_highValue_angles
    {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : E → ℝ} (hu : Measurable u)
    {x v : S → E} {r A : S → ℝ}
    (hx : Measurable x) (hv : Measurable v)
    (hr : Measurable r) (hA : Measurable A) :
    MeasurableSet {p : S × ℝ | p.2 ∈ Icc 0 (2 * Real.pi) ∧
      A p.1 ≤ u (x p.1 + circleMap 0 (r p.1) p.2 • v p.1)} := by
  have hc : Measurable (fun p : S × ℝ => circleMap 0 (r p.1) p.2) := by
    have hcont : Continuous (fun q : ℝ × ℝ => circleMap 0 q.1 q.2) := by
      unfold circleMap
      fun_prop
    exact hcont.measurable.comp ((hr.comp measurable_fst).prodMk measurable_snd)
  exact (measurableSet_Icc.preimage measurable_snd).inter
    (measurableSet_le (hA.comp measurable_fst)
      (hu.comp ((hx.comp measurable_fst).add (hc.smul (hv.comp measurable_fst)))))

end PshLines.PSHD
