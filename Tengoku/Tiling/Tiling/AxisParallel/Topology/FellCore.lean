import Tengoku.Tiling.Tiling.Topology.FellCore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/jaumededios/Tiling@00f80c7de5ac, `Tiling/AxisParallel/Topology/FellCore.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/


open Filter Set

namespace Tiling.AxisParallel.Topology

/-- Literal pairwise separation by at least `delta`.-/
abbrev IsUniformlySeparated {E : Type*} [PseudoMetricSpace E]
    (delta : ℝ) (S : Set E) : Prop :=
  Tiling.Topology.IsUniformlySeparated delta S

/-- Adjoin the point at infinity to a closed set, using the preserved proved generic body.-/
abbrev fellCompactification
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    (S : Set E) (hS : IsClosed S) :
    TopologicalSpace.NonemptyCompacts (OnePoint E) :=
  Tiling.Topology.fellCompactification S hS

/-- Vietoris convergence after adjoining infinity, with closedness included in the predicate.-/
abbrev LocallyFellConverges
    {E : Type*} [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    (S : ℕ → Set E) (L : Set E) : Prop :=
  Tiling.Topology.LocallyFellConverges S L

end Tiling.AxisParallel.Topology
