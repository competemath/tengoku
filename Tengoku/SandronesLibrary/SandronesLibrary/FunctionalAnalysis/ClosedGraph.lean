/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.OpenMapping
import Tengoku.Seed.Analysis.Normed.Operator.Banach

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closed graph theorem

The graph of a linear map is Mathlib's `LinearMap.graph`; closedness is the standard `IsClosed`
predicate in the product topology.  The Banach closed graph theorem then turns this algebraic map
into a continuous one without introducing a separate closed-operator interface.
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter
open SandronesLibrary.Topology.NormedSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedLinearSpace ℝ E] [NormedLinearSpace ℝ F]
variable [BanachSpace E] [BanachSpace F]

/-- **Closed graph theorem**: a linear map between Banach spaces with closed graph is continuous.

> **Entry**: functional-analysis.closed-graph
@isnad1 id=continuo.1h3v.s8.95dbb1a1708e from=translated src=- shape=33be914e vocab=8888facb
-/
theorem linearMap_continuous_of_isClosed_graph (T : E →ₗ[ℝ] F)
    (hGraph : IsClosed (T.graph : Set (E × F))) : Continuous T := by
  exact T.continuous_of_isClosed_graph hGraph

/-- A closed-graph linear map can be represented by a continuous linear map with the same values.
@isnad1 id=ex.1h3v.s9.fa4a59064b33 from=translated src=- shape=d74e2d33 vocab=c1d78e3e
-/
theorem exists_continuousLinearMap_of_isClosed_graph (T : E →ₗ[ℝ] F)
    (hGraph : IsClosed (T.graph : Set (E × F))) :
    ∃ T' : E →L[ℝ] F, ∀ x : E, T' x = T x := by
  exact ⟨ContinuousLinearMap.ofIsClosedGraph hGraph, fun _ ↦ rfl⟩

/-- Sequential closed-graph criterion: if simultaneous limits `xₙ → x` and `T xₙ → y` force
`y = T x`, then `T` is continuous.
@isnad1 id=continuo.1h3v.s8.e61ceb3c470b from=translated src=- shape=ae906eeb vocab=0aab4fb2
-/
theorem linearMap_continuous_of_sequential_closed_graph (T : E →ₗ[ℝ] F)
    (hGraph : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (nhds x) → Tendsto (T ∘ u) atTop (nhds y) → y = T x) :
    Continuous T := by
  exact T.continuous_of_seq_closed_graph hGraph

end SandronesLibrary.FunctionalAnalysis
