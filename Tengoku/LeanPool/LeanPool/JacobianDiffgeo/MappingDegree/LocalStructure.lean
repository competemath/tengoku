/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. FiberStack: adapted charts stacked over a whole fiber.
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.LocalMultiplicity.AdaptedCharts
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.MappingDegree.Basics
public import Tengoku

/-!
# The stack of adapted charts over a fiber (heart, part 1)

* `RS.FiberStack F y₀` — the (finite) fiber over `y₀` enumerated as `pt : Fin n → X`,
  pairwise-disjoint adapted charts at each fiber point, and an open `V ∋ y₀` contained in every
  target-chart source, whose target-chart images lie in the normal-form balls and whose
  `F`-preimage is trapped in the chart sources. This is the multiplicity-aware local model of
  `F` over an arbitrary point of `Y` (branch value or not); Forster's 4.24-proof mechanism.
* `RS.exists_fiberStack` — existence over every `y₀ : Y` (compactness of `X` traps the fiber
  via the closed-map filter inequality `IsClosedMap.comap_nhds_le`; no sequences).
* Basic API: `mem_fiber_pt`, `maps_pt_eq`, `mem_source_pt`, `radius_pos`, `mult_ne_zero`,
  `fiber_eq_iUnion`.

`LocalConstancy.lean` combines this with the planar count (`RootCounting.lean`) to prove that
`fiberMultSum` is locally constant.
-/

@[expose] public section

open Filter Set Function
open scoped ContDiff Manifold Topology

namespace RS

section Structure

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- A stack of adapted charts over `y₀`: the (finite) fiber enumerated as `pt : Fin n → X`,
pairwise-disjoint adapted charts at each fiber point, and an open `V ∋ y₀` that is contained
in every target-chart source, whose target-chart images lie in the normal-form balls, and whose
`F`-preimage is trapped in the chart sources. -/
structure FiberStack (F : X → Y) (y₀ : Y) where
  /-- The number of points in the fiber. -/
  n : ℕ
  /-- An enumeration of the fiber. -/
  pt : Fin n → X
  pt_injective : Function.Injective pt
  range_pt : Set.range pt = F ⁻¹' {y₀}
  one_le_mult : ∀ i, 1 ≤ multiplicity F (pt i)
  /-- Adapted charts (local normal form `z ↦ z ^ k`) at each fiber point. -/
  A : ∀ i, AdaptedChartsAt F (pt i) (multiplicity F (pt i))
  disjoint_sources : Pairwise (Disjoint on fun i ↦ (A i).e.source)
  /-- The distinguished open neighborhood of `y₀`. -/
  V : Set Y
  isOpen_V : IsOpen V
  mem_V : y₀ ∈ V
  V_subset : ∀ i, V ⊆ (A i).e'.source
  map_V_mem_ball : ∀ i, ∀ y ∈ V,
    (A i).e' y ∈ Metric.ball 0 ((A i).radius ^ multiplicity F (pt i))
  preimage_V_subset : F ⁻¹' V ⊆ ⋃ i, (A i).e.source

namespace FiberStack

variable {F : X → Y} {y₀ : Y} (S : FiberStack F y₀)

end FiberStack

end Structure

/-! ### Existence (standing surface hypotheses) -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

end RS
