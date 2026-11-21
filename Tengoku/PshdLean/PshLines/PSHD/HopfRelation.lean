import Tengoku.PshdLean.PshLines.PSHD.Hopf
import Tengoku.Seed.Topology.Maps.Proper.Basic
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The closed Hopf relation on unit vectors

The lifted direction relation in `pshd-vibe`, Lemma 1.3, is closed.
This yields its Borel high-value restriction without presupposing a
measurable choice of representatives of projective directions.
-/

open Set Metric

namespace PshLines.PSHD

/-- Equality of projective directions is a closed relation on the unit sphere.
@isnad1 id=isclosed.0h1v.s9.85a9811a493c from=translated src=- shape=56d2aadd vocab=30c7e2d7
-/
theorem isClosed_hopf_relation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsClosed {p : sphere (0 : E) 1 × sphere (0 : E) 1 | hopf p.1 = hopf p.2} := by
  let C := {p : sphere (0 : ℂ) 1 × (sphere (0 : E) 1 × sphere (0 : E) 1) |
    (p.1 : ℂ) • (p.2.2 : E) = (p.2.1 : E)}
  have hC : IsClosed C := isClosed_eq
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd.snd))
    (continuous_subtype_val.comp continuous_snd.fst)
  have heq : {p : sphere (0 : E) 1 × sphere (0 : E) 1 | hopf p.1 = hopf p.2} =
      Prod.snd '' C := by
    ext p
    constructor
    · intro hp
      obtain ⟨a, ha, hval⟩ := (hopf_eq_iff p.1 p.2).mp hp
      exact ⟨(⟨a, by simpa using ha⟩, p), hval, rfl⟩
    · rintro ⟨⟨a, q⟩, hval, rfl⟩
      exact (hopf_eq_iff q.1 q.2).mpr ⟨a, by simp, hval⟩
  rw [heq]
  exact isClosedMap_snd_of_compactSpace C hC

/-- The high-value star relation lifted to unit direction vectors is Borel.
@isnad1 id=measurab.1h5v.s10.33e3aa1838e1 from=translated src=- shape=b695590b vocab=d3b9e528
-/
theorem measurableSet_highValue_hopf_relation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {u : E → ℝ} (hu : Measurable u) (x : E) (R A : ℝ) :
    MeasurableSet {p : (ℝ × sphere (0 : E) 1) × sphere (0 : E) 1 |
      p.1.1 ∈ Icc (R / 2) R ∧ hopf p.2 = hopf p.1.2 ∧
        A ≤ u (x + (p.1.1 : ℂ) • (p.2 : E))} := by
  have hr : Continuous (fun p : (ℝ × sphere (0 : E) 1) × sphere (0 : E) 1 =>
      p.1.1) := continuous_fst.fst
  have hdir : IsClosed {p : (ℝ × sphere (0 : E) 1) × sphere (0 : E) 1 |
      hopf p.2 = hopf p.1.2} :=
    isClosed_hopf_relation.preimage (continuous_snd.prodMk continuous_fst.snd)
  have hpoint : Continuous (fun p : (ℝ × sphere (0 : E) 1) × sphere (0 : E) 1 =>
      x + (p.1.1 : ℂ) • (p.2 : E)) :=
    continuous_const.add ((Complex.continuous_ofReal.comp hr).smul
      (continuous_subtype_val.comp continuous_snd))
  exact (measurableSet_Icc.preimage hr.measurable).inter
    (hdir.measurableSet.inter
      (measurableSet_le measurable_const (hu.comp hpoint.measurable)))

end PshLines.PSHD
