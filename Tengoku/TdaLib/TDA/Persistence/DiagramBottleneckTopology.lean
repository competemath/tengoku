import Tengoku.TdaLib.TDA.Persistence.DiagramBottleneckLaws
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Metric
import Tengoku.Seed.Topology.Bases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Borel geometry of finite persistence diagrams

Finite diagrams carry the extended metric induced by their bottleneck distance.
Distances can be infinite when the essential-bar multiplicities differ. Every
diagram has an ordered finite-coordinate presentation, and those presentations
also show that the resulting metric topology is separable.
-/

noncomputable section

namespace TDA.Persistence

open scoped ENNReal
open TopologicalSpace

/-- The bottleneck distance is a genuine extended metric on finite diagrams.
Its value may be `∞` when the essential-bar counts differ.-/
instance instEMetricSpace : EMetricSpace (Diagram ℝ) where
  edist := bottleneck
  edist_self := bottleneck_self
  edist_comm := bottleneck_comm
  edist_triangle := bottleneck_triangle
  eq_of_edist_eq_zero := fun h => (bottleneck_eq_zero_iff _ _).mp h

/--
@isnad1 id=lipschit.0h2v.s6.a91f25cd4072 from=translated src=- shape=ad83cb05 vocab=67b67f5c
-/
theorem lipschitzWith_orderedQ (m n : ℕ) :
    LipschitzWith 1 (orderedQ (α := ℝ) m n) := by
  intro z w
  change bottleneck (orderedQ (α := ℝ) m n z)
      (orderedQ (α := ℝ) m n w) ≤ 1 * edist z w
  rw [edist_dist, dist_eq_norm]
  simpa using bottleneck_orderedQ_le_norm m n z w

/--
@isnad1 id=continuo.0h2v.s6.988af4a3ecc0 from=translated src=- shape=fbe55d11 vocab=116fad2d
-/
theorem continuous_orderedQ (m n : ℕ) :
    Continuous (orderedQ (α := ℝ) m n) :=
  (lipschitzWith_orderedQ m n).continuous

/--
@isnad1 id=separabl.0h0v.s4.b9e0e0eeeeb7 from=translated src=- shape=87ceb31f vocab=48cc66e5
-/
instance instSeparableSpace : TopologicalSpace.SeparableSpace (Diagram ℝ) := by
  have hcover : (Set.univ : Set (Diagram ℝ)) =
      ⋃ p : ℕ × ℕ, Set.range (orderedQ (α := ℝ) p.1 p.2) := by
    ext D
    constructor
    · intro _
      obtain ⟨m, n, z, rfl⟩ := orderedQ_surjective D
      exact Set.mem_iUnion.mpr ⟨(m, n), ⟨z, rfl⟩⟩
    · intro _
      trivial
  rw [← isSeparable_univ_iff, hcover, isSeparable_iUnion]
  intro p
  exact isSeparable_range (continuous_orderedQ p.1 p.2)

/--
@isnad1 id=secondco.0h0v.s4.4dea82be6435 from=translated src=- shape=87ceb31f vocab=a20a4d7c
-/
instance instSecondCountableTopology : SecondCountableTopology (Diagram ℝ) :=
  UniformSpace.secondCountable_of_separable (Diagram ℝ)

instance instMeasurableSpace : MeasurableSpace (Diagram ℝ) := borel (Diagram ℝ)

/--
@isnad1 id=borelspa.0h0v.s4.7660613e2597 from=translated src=- shape=87ceb31f vocab=0ef9ea39
-/
instance instBorelSpace : BorelSpace (Diagram ℝ) := ⟨rfl⟩

/--
@isnad1 id=measurab.0h0v.s5.9a416fdd7f33 from=translated src=- shape=42673c7b vocab=5f4c6986
-/
theorem measurable_bottleneck :
    Measurable (fun p : Diagram ℝ × Diagram ℝ => bottleneck p.1 p.2) :=
  measurable_edist

end TDA.Persistence
