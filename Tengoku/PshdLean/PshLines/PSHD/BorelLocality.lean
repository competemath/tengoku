import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Basic
import Tengoku.Seed.MeasureTheory.MeasurableSpace.Constructions
import Tengoku.Seed.Topology.Bases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Local Borel patching

The local-to-global step in the proof of Lemma 1.2 of `pshd-vibe`.
-/

open Set TopologicalSpace

namespace PshLines.PSHD

/-- On a second-countable space, measurability on an open neighborhood of
each point implies measurability on the whole space.
@isnad1 id=measurab.1h3v.s6.1426078edb5b from=translated src=- shape=6e79827f vocab=31950186
-/
theorem measurable_of_open_neighborhoods
    {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y}
    (h : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Measurable (V.domRestrict f)) :
    Measurable f := by
  classical
  choose V hVo hxV hVm using h
  obtain ⟨T, hT, hEq⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hcover (x : X) : ∃ i ∈ T, x ∈ V i := by
    have hx : x ∈ ⋃ i ∈ T, V i := by
      rw [hEq]
      exact mem_iUnion.mpr ⟨x, hxV x⟩
    simpa only [mem_iUnion, exists_prop] using hx
  intro s hs
  have heq : f ⁻¹' s = ⋃ i ∈ T, Subtype.val '' ((V i).domRestrict f ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := hcover x
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, ⟨⟨x, hxi⟩, hx, rfl⟩⟩⟩
    · intro hx
      obtain ⟨i, hi, y, hy, rfl⟩ := by
        simpa only [mem_iUnion, mem_image, exists_prop] using hx
      exact hy
  rw [heq]
  exact MeasurableSet.biUnion hT (fun i _ =>
    (hVo i).measurableSet.subtype_image (hVm i hs))

end PshLines.PSHD
