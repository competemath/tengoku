import Tengoku.PshdLean.PshLines.PSHD.HighValueCircle
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The Borel relation for high-value star selection

This is the Borel-graph step of `pshd-vibe`, Lemma 1.3. The direction map
is left general so that the statement applies to the Hopf map.
-/

open Set Metric

namespace PshLines.PSHD

/-- For any continuous direction map on the unit sphere, the relation specifying
an annular radius, its direction, and a high-value unit vector is Borel.
@isnad1 id=measurab.2h7v.s9.ab4048563f87 from=translated src=- shape=4160d054 vocab=e45309dd
-/
theorem measurableSet_highValue_relation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Type*} [TopologicalSpace P] [T2Space P]
    [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
    {q : sphere (0 : E) 1 → P} (hq : Continuous q)
    {u : E → ℝ} (hu : Measurable u) (x : E) (R A : ℝ) :
    MeasurableSet {p : (ℝ × P) × sphere (0 : E) 1 |
      p.1.1 ∈ Icc (R / 2) R ∧ q p.2 = p.1.2 ∧
        A ≤ u (x + (p.1.1 : ℂ) • (p.2 : E))} := by
  have hr : Continuous (fun p : (ℝ × P) × sphere (0 : E) 1 => p.1.1) :=
    continuous_fst.fst
  have he : Continuous (fun p : (ℝ × P) × sphere (0 : E) 1 => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hpoint : Continuous (fun p : (ℝ × P) × sphere (0 : E) 1 =>
      x + (p.1.1 : ℂ) • (p.2 : E)) :=
    continuous_const.add ((Complex.continuous_ofReal.comp hr).smul he)
  exact (measurableSet_Icc.preimage hr.measurable).inter
    ((isClosed_eq (hq.comp continuous_snd) continuous_fst.snd).measurableSet.inter
      (measurableSet_le measurable_const (hu.comp hpoint.measurable)))

end PshLines.PSHD
