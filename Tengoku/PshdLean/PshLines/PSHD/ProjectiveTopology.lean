import Tengoku.PshdLean.PshLines.PSHD.HopfRelation
import Tengoku.Seed.Topology.Bases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The quotient topology on complex projective directions

The projective parameter space of `pshd-vibe`, Lemma 1.3, carries the
quotient topology of the Hopf map. The instances are scoped to PSHD.
-/

open Set Metric Topology

noncomputable section

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Complex projective space has the quotient topology of the unit sphere.-/
@[instance_reducible]
def projectiveTopology : TopologicalSpace (Projectivization ℂ E) :=
  TopologicalSpace.coinduced (hopf (E := E)) inferInstance

attribute [scoped instance] projectiveTopology

theorem isQuotientMap_hopf : IsQuotientMap (hopf (E := E)) :=
  ⟨⟨rfl⟩, hopf_surjective⟩

theorem continuous_hopf : Continuous (hopf (E := E)) :=
  isQuotientMap_hopf.continuous

/-- Saturation under the Hopf map is a union of inverse images under phases.-/
theorem hopf_saturation (U : Set (sphere (0 : E) 1)) :
    hopf ⁻¹' (hopf '' U) =
      ⋃ a : sphere (0 : ℂ) 1, (fun e => phaseOrbit e a) ⁻¹' U := by
  ext e
  simp only [mem_preimage, mem_image, mem_iUnion]
  constructor
  · rintro ⟨f, hf, hfe⟩
    obtain ⟨a, ha, heq⟩ := (hopf_eq_iff f e).mp hfe
    refine ⟨⟨a, by simpa using ha⟩, ?_⟩
    have h : phaseOrbit e ⟨a, by simpa using ha⟩ = f := Subtype.ext heq
    simpa only [h] using hf
  · rintro ⟨a, ha⟩
    exact ⟨phaseOrbit e a, ha, (hopf_eq_iff _ _).mpr ⟨a, by simp, rfl⟩⟩

/-- The Hopf quotient map is open.-/
theorem isOpenMap_hopf : IsOpenMap (hopf (E := E)) := by
  intro U hU
  apply isQuotientMap_hopf.isCoinducing.isOpen_preimage.mp
  rw [hopf_saturation]
  apply isOpen_iUnion
  intro a
  have hc : Continuous (fun e : sphere (0 : E) 1 => phaseOrbit e a) :=
    (continuous_const.smul continuous_subtype_val).subtype_mk _
  exact hU.preimage hc

theorem isOpenQuotientMap_hopf : IsOpenQuotientMap (hopf (E := E)) :=
  ⟨hopf_surjective, continuous_hopf, isOpenMap_hopf⟩

/-- Closedness of the Hopf relation makes projective space Hausdorff.-/
theorem projectiveT2Space : T2Space (Projectivization ℂ E) :=
  (t2Space_iff_of_isOpenQuotientMap isOpenQuotientMap_hopf).mpr isClosed_hopf_relation

attribute [scoped instance] projectiveT2Space

/-- Second countability descends through the open Hopf quotient.-/
theorem projectiveSecondCountableTopology [SecondCountableTopology E] :
    SecondCountableTopology (Projectivization ℂ E) :=
  isQuotientMap_hopf.secondCountableTopology isOpenMap_hopf

attribute [scoped instance] projectiveSecondCountableTopology

/-- In a proper ambient space the projective direction space is compact.-/
theorem projectiveCompactSpace [ProperSpace E] :
    CompactSpace (Projectivization ℂ E) :=
  ⟨by
    rw [← Set.range_eq_univ.mpr (hopf_surjective (E := E))]
    exact isCompact_range continuous_hopf⟩

attribute [scoped instance] projectiveCompactSpace

/-- The measurable structure on projective directions is the Borel structure.-/
@[instance_reducible]
def projectiveMeasurableSpace : MeasurableSpace (Projectivization ℂ E) :=
  borel _

attribute [scoped instance] projectiveMeasurableSpace

theorem projectiveBorelSpace : BorelSpace (Projectivization ℂ E) :=
  ⟨rfl⟩

attribute [scoped instance] projectiveBorelSpace

end PshLines.PSHD
