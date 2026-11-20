import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
import Tengoku.Seed.Topology.Algebra.Star.Unitary
import Tengoku.Seed.MeasureTheory.Measure.Haar.Basic
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Haar probability on the unitary group

The compact unitary group of a finite-dimensional complex inner product space,
with its normalized Haar measure. This realizes the invariant probability on
complex hyperplanes used in `pshd-vibe`, Lemma 1.4.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PshLines.PSHD

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The unitary group of `E`, as unitary elements of the C⋆-algebra of operators.-/
abbrev UnitaryGroup := unitary (E →L[ℂ] E)

theorem isCompact_unitary : IsCompact (unitary (E →L[ℂ] E) : Set (E →L[ℂ] E)) := by
  have : ProperSpace (E →L[ℂ] E) := FiniteDimensional.proper ℂ _
  refine Metric.isCompact_of_isClosed_isBounded isClosed_unitary ?_
  refine (Metric.isBounded_closedBall (x := (0 : E →L[ℂ] E)) (r := 1)).subset ?_
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  rcases subsingleton_or_nontrivial (E →L[ℂ] E) with h | h
  · simp [Subsingleton.elim U 0]
  · exact (CStarRing.norm_of_mem_unitary hU).le

instance : CompactSpace (UnitaryGroup E) :=
  isCompact_iff_compactSpace.mp (isCompact_unitary E)

instance : MeasurableSpace (UnitaryGroup E) := borel _

instance : BorelSpace (UnitaryGroup E) := ⟨rfl⟩

/-- Normalized Haar measure on the unitary group.-/
def unitaryHaar : Measure (UnitaryGroup E) :=
  Measure.haarMeasure ⊤

instance : (unitaryHaar E).IsHaarMeasure := by
  unfold unitaryHaar
  infer_instance

instance : IsProbabilityMeasure (unitaryHaar E) := by
  refine ⟨?_⟩
  have h := Measure.haarMeasure_self (G := UnitaryGroup E) (K₀ := ⊤)
  simpa [unitaryHaar] using h

end PshLines.PSHD
