import Tengoku.PshdLean.PshLines.PSHD.ProductBorel
import Tengoku.PshdLean.PshLines.PSHD.BorelLocality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Borel measurability from semicontinuous and disc-PSH sections

The open-domain form of Lemma 1.2 of `pshd-vibe`.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace PshLines.PSHD

/-- Nonnegative real functions on an open product domain are Borel when
their horizontal sections are upper semicontinuous and their vertical
complex sections satisfy the disc criterion.-/
theorem measurable_on_open_of_discPsh_sections
    {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    {G : Set (X × ℂ)} (hG : IsOpen G) {f : X → ℂ → ℝ}
    (husc : ∀ y, UpperSemicontinuousOn (fun x => f x y) {x | (x, y) ∈ G})
    (hpos : ∀ x y, (x, y) ∈ G → 0 ≤ f x y)
    (hpsh : ∀ x, DiscPshOn (fun y => (f x y : EReal)) {y | (x, y) ∈ G}) :
    Measurable (fun p : G => f p.1.1 p.1.2) := by
  apply measurable_of_open_neighborhoods
  intro p
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hG.mem_nhds p.property)
  have hprod : ball p.1.1 r ×ˢ ball p.1.2 r ⊆ G := by
    simpa only [ball_prod_same] using hball
  let V : Set G := Subtype.val ⁻¹' (ball p.1.1 r ×ˢ ball p.1.2 r)
  refine ⟨V, (isOpen_ball.prod isOpen_ball).preimage continuous_subtype_val,
    ⟨mem_ball_self hr, mem_ball_self hr⟩, ?_⟩
  let : IsFiniteMeasure (volume.restrict (ball p.1.2 r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure ℂ)) (x := p.1.2) (r := r))⟩
  have hm := measurable_on_product_of_discPsh (X := ball p.1.1 r) isOpen_ball
    (f := fun x y => f x y)
    (fun y hy => upperSemicontinuousOn_iff_restrict.mpr
      ((husc y).mono (fun x hx => hprod ⟨hx, hy⟩)))
    (fun x y hy => hpos x y (hprod ⟨x.property, hy⟩))
    (fun x => (hpsh x).mono (fun y hy => hprod ⟨x.property, hy⟩))
  let q : V → ball p.1.1 r × ball p.1.2 r := fun z =>
    (⟨z.1.1.1, z.property.1⟩, ⟨z.1.1.2, z.property.2⟩)
  have hq : Measurable q := by
    exact ((measurable_fst.comp (measurable_subtype_coe.comp
      measurable_subtype_coe)).subtype_mk).prodMk
      ((measurable_snd.comp (measurable_subtype_coe.comp
        measurable_subtype_coe)).subtype_mk)
  exact hm.comp hq

end PshLines.PSHD
