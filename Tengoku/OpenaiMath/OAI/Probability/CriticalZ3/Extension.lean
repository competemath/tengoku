import Tengoku.OpenaiMath.OAI.Probability.CriticalZ3.SeedQuality

namespace OAI

universe uOmega

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace MeasureTheory
open scoped _root_.MeasureTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
end MeasureTheory

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem entrant_exterior {C : Box} {ω : m.Config} {o : G.Node} {y : Vertex}
    (hy : y ∈ G.entrants m C ω o) : C.Exterior y :=
  (Finset.mem_filter.mp hy).2.choose_spec.1

theorem entrant_node {C : Box} {ω : m.Config} {o : G.Node} {y : Vertex}
    (hy : y ∈ G.entrants m C ω o) : y ∈ G.vertices := (Finset.mem_filter.mp hy).1

end CriticalZ3.LatticeGraph

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem measurableSet_large_entrants (C : Box) (o : G.Node) (L : ℕ) :
    MeasurableSet {ω | L ≤ (G.entrants m C ω o).card} := by
  apply ProductCylinder.measurableSet_determined (G.outsideBits m C)
  intro ω ω' h
  simp only [Set.mem_ofPred_eq,G.entrants_determined m C o ω ω' h]

end CriticalZ3.LatticeGraph

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

theorem entryBit_internal_expand {C : Box} {y : Vertex} (hy : C.Exterior y) (m : Model) :
    C.entryBit m y ∈ (C.expand 1).bits m := by
  cases m
  · exact LatticeGraph.incidence_internal (exterior_expand hy)
      (C.contains_expand 1 (entry_spec hy).1) (neighborBond_incidence (entry_spec hy).2)
  · exact (mem_vertices _ _).mpr (C.contains_expand 1 (entry_spec hy).1)
end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

end OAI
