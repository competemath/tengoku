/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. Ramification and branch loci are finite; regular values.
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.LocalMultiplicity.Multiplicity
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.LocalMultiplicity.Composition
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.MappingDegree.Basics
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Identity
public import Tengoku

/-!
# Ramification locus, branch locus, regular values

* `RS.ramificationLocus F` (points with `multiplicity ≥ 2`), `RS.branchLocus F` (their images),
  `RS.IsRegularValue F y` (no ramification point in the fiber).
* Finiteness (Forster 4.23-adjacent): `RS.isClosed_ramificationLocus`,
  `RS.isDiscrete_ramificationLocus`, `RS.ramificationLocus_finite`, `RS.branchLocus_finite`.
* Regular values: `RS.isRegularValue_iff_notMem_branchLocus`,
  `RS.multiplicity_eq_one_of_isRegularValue`, cofiniteness
  `RS.setOf_isRegularValue_mem_cofinite`, density `RS.dense_setOf_isRegularValue`, and
  existence `RS.exists_isRegularValue`.
-/

@[expose] public section

open Filter Set Function
open scoped ContDiff Manifold Topology

namespace RS

/-! ### Definitions (minimal instances) -/

section Defs

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Points where `F` is ramified (local multiplicity `≥ 2`, CC4's `IsRamifiedAt`). -/
def ramificationLocus (F : X → Y) : Set X := {x | IsRamifiedAt F x}

/-- Branch values (critical values): images of ramification points. -/
def branchLocus (F : X → Y) : Set Y := F '' ramificationLocus F

/-- `y` is a regular value iff every point of its fiber is unramified. (For holomorphic
nonconstant `F` this is equivalent to `y ∉ branchLocus F`, and then every fiber point has
multiplicity exactly `1`.) Values NOT attained are regular (empty fiber) — harmless, since for
nonconstant `F` every value is attained. -/
def IsRegularValue (F : X → Y) (y : Y) : Prop := ∀ x ∈ F ⁻¹' {y}, ¬ IsRamifiedAt F x

/--
@isnad1 id=iff.0h4v.s6.46ef8a5c5103 from=translated src=- shape=faf2e74f vocab=1a98d220
-/
theorem mem_ramificationLocus_iff {F : X → Y} {x : X} :
    x ∈ ramificationLocus F ↔ 2 ≤ multiplicity F x := Iff.rfl

/-- Pure set algebra: regular values are exactly the non-branch values.
@isnad1 id=iff.0h4v.s6.ad7337f9e034 from=translated src=- shape=42210c53 vocab=efc977f3
-/
theorem isRegularValue_iff_notMem_branchLocus (F : X → Y) (y : Y) :
    IsRegularValue F y ↔ y ∉ branchLocus F := by
  constructor
  · rintro h ⟨x, hx, rfl⟩
    exact h x rfl hx
  · intro h x hxy hram
    exact h ⟨x, hram, hxy⟩

end Defs

/-! ### Finiteness (standing surface hypotheses) -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

end RS
