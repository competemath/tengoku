import Tengoku.PshdLean.PshLines.PSHD.ProjectiveTopology
import Tengoku.Seed.Topology.Metrizable.Urysohn
import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Polish projective directions

The measurable-selection parameter space in `pshd-vibe`, Lemma 1.3.
-/

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [ProperSpace E] [SecondCountableTopology E]

/-- Proper second-countable complex normed spaces have Polish projectivizations.-/
theorem projectivePolishSpace : PolishSpace (Projectivization ℂ E) := by
  let : MetricSpace (Projectivization ℂ E) :=
    TopologicalSpace.metrizableSpaceMetric _
  infer_instance

attribute [scoped instance] projectivePolishSpace

/-- Their projective Borel structures are standard Borel.-/
theorem projectiveStandardBorelSpace : StandardBorelSpace (Projectivization ℂ E) := by
  infer_instance

attribute [scoped instance] projectiveStandardBorelSpace

end PshLines.PSHD
